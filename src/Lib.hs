{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE MultiWayIf       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

module Lib where

import           Control.Exception    (assert)
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Bits            hiding (isSigned)
import           Data.Default

-- * Type definitions

data NegativeZero
  = KeepNegativeZero -- ^ 6.2.6.2/3
  | MakeNormalZero -- ^ 6.2.6.2/3
  | NZHalt -- ^ 6.2.6.2/4
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | 6.2.6.2/2
data NegativeRepresentation
  = TwosComplement
  | OnesComplement NegativeZero
  | SignMagnitude NegativeZero
  deriving (Show, Eq, Ord)

data CIntegralSignedness = Unsigned | Signed | Unspecified
  deriving (Show, Eq, Ord, Enum, Bounded)

data CIntegralSize = CChar | CShort | CInt | CLong | CLongLong
  deriving (Show, Eq, Ord, Enum, Bounded)

data CIntegralType = CIntegralType CIntegralSize CIntegralSignedness
  deriving (Show, Eq, Ord)

data CIntegral = CIntegral CIntegralType Integer
  deriving (Show)

int :: CIntegralType
int = CIntegralType CInt Signed

unsigned :: CIntegralType
unsigned = CIntegralType CInt Unsigned

data OnSignedIntegerOverflow = SIOHalt | WrapAround | Saturate
  deriving (Show, Eq, Ord, Enum, Bounded)

data OnDivisionByZero = DBZHalt | ReturnDividend
  deriving (Show, Eq, Ord, Enum, Bounded)

data OnBitwiseShiftByNegative = BSBNHalt | ShiftInOtherDirection
  deriving (Show, Eq, Ord, Enum, Bounded)

data OnBitwiseShiftTooMuch = BSTMHalt | ShiftAsIfInfinitePrecision | ModuloShiftAmount
  deriving (Show, Eq, Ord, Enum, Bounded)

data OnBitwiseRightShiftNegative = LogicalShift | ArithmeticShift
  deriving (Show, Eq, Ord, Enum, Bounded)

data MachineDesc
  = MachineDesc
  { _charBits :: Int
  , _charSigned :: Bool
  , _shortBits :: Int
  , _intBits :: Int
  , _longBits :: Int
  , _longlongBits :: Int
  , _shortAddlPaddingBytes :: Int
  , _intAddlPaddingBytes :: Int
  , _longAddlPaddingBytes :: Int
  , _longlongAddlPaddingBytes :: Int
  , _sizetSize :: CIntegralSize
  , _negativeRep :: NegativeRepresentation
  , _onSignedOverflow :: OnSignedIntegerOverflow
  , _onDivByZero :: OnDivisionByZero
  , _onShiftByNegative :: OnBitwiseShiftByNegative
  , _onShiftTooMuch :: OnBitwiseShiftTooMuch
  , _onRightShiftNegative :: OnBitwiseRightShiftNegative
  }
  deriving (Show, Eq, Ord)

instance Default MachineDesc where
  def = MachineDesc
    { _charBits = 8
    , _shortBits = 16
    , _intBits = 32
    , _longBits = 64
    , _longlongBits = 64
    , _shortAddlPaddingBytes = 0
    , _intAddlPaddingBytes = 0
    , _longAddlPaddingBytes = 0
    , _longlongAddlPaddingBytes = 0
    , _sizetSize = CLong
    , _charSigned = True
    , _negativeRep = TwosComplement
    , _onSignedOverflow = SIOHalt
    , _onDivByZero = DBZHalt
    , _onShiftByNegative = BSBNHalt
    , _onShiftTooMuch = BSTMHalt
    , _onRightShiftNegative = ArithmeticShift
    }

$(makeLenses ''MachineDesc)

sizeToBits :: CIntegralSize -> Getting Int MachineDesc Int
sizeToBits CChar = charBits
sizeToBits CShort = shortBits
sizeToBits CInt = intBits
sizeToBits CLong = longBits
sizeToBits CLongLong = longlongBits

sizeToAddlPadding :: CIntegralSize -> Getting Int MachineDesc Int
sizeToAddlPadding CChar = to (const 0)
sizeToAddlPadding CShort = shortAddlPaddingBytes
sizeToAddlPadding CInt = intAddlPaddingBytes
sizeToAddlPadding CLong = longAddlPaddingBytes
sizeToAddlPadding CLongLong = longlongAddlPaddingBytes

validateMachineDesc :: MachineDesc -> Bool
validateMachineDesc MachineDesc{..} =
  -- 5.2.4.2.1/1
  _charBits >= 8 && _shortBits >= 16 && _intBits >= 16 && _longBits >= 32 && _longlongBits >= 64 &&
  -- integers with higher conversion rank must have at least as great a precision
  _charBits <= _shortBits && _shortBits <= _intBits && _intBits <= _longBits && _longBits <= _longlongBits
  -- the sizeof type must be enough to represent sizes of integers

-- | 6.3.1.1
conversionRank :: CIntegralType -> Int
conversionRank (CIntegralType sz _) = fromEnum sz

isSigned :: MachineDesc -> CIntegralType -> Bool
isSigned _ (CIntegralType _ Signed) = True
isSigned _ (CIntegralType _ Unsigned) = False
isSigned md (CIntegralType CChar Unspecified) = view charSigned md
isSigned _ (CIntegralType _ Unspecified) = True

representableRange :: MachineDesc -> CIntegralType -> (Integer, Integer)
representableRange md ty@(CIntegralType sz _) =
  if isSigned md ty
  then
    let p = 1 `shift` (view (sizeToBits sz) md - 1)
    in case view negativeRep md of
      TwosComplement -> (negate p, p - 1)
      _ -> (negate p + 1, p - 1)
  else (0, 1 `shift` view (sizeToBits sz) md - 1)

areAllValuesRepresentableIn :: MachineDesc -> CIntegralType -> CIntegralType -> Bool
areAllValuesRepresentableIn md a b =
  case (representableRange md a, representableRange md b) of
    ((aMin, aMax), (bMin, bMax)) -> aMin >= bMin && aMax <= bMax

-- * Evaluation and operators

data UndefinedBehavior
  = SignedIntegerOverflow
  | DivisionByZero
  | ShiftByNegative
  | ShiftTooMuch
  deriving (Show, Eq)

data EvaluationError
  = UndefinedBehaviorHalted UndefinedBehavior
  deriving (Show, Eq)

type Ev m = (MonadReader MachineDesc m, MonadError EvaluationError m)

integerPromoteType :: Ev m => CIntegralType -> m CIntegralType
integerPromoteType ty
  | conversionRank ty < conversionRank int =
      asks $ \md -> if areAllValuesRepresentableIn md ty int then int else unsigned
  | otherwise = pure ty

integerPromotion :: Ev m => CIntegral -> m CIntegral
integerPromotion (CIntegral ty val) =
  (`CIntegral` val) <$> integerPromoteType ty

integerConvertType :: Ev m => CIntegralType -> Integer -> m CIntegral
integerConvertType ty v = do
  md <- ask
  if isSigned md ty then
    case representableRange md ty of
      (tmin, tmax) ->
        if tmin <= v && v <= tmax then pure (CIntegral ty v)
        else
          case view onSignedOverflow md of
            SIOHalt -> throwError (UndefinedBehaviorHalted SignedIntegerOverflow)
            Saturate -> pure (CIntegral ty (if v > tmax then tmax else tmin))
            WrapAround ->
              case tmax - tmin + 1 of
                p -> if v > tmax
                     then pure (CIntegral ty (v + ((v - tmax) `quot` p + 1) * negate p))
                     else pure (CIntegral ty (v + ((tmin - v) `quot` p + 1) * p))
  else pure (CIntegral ty (v `mod` (1 + snd (representableRange md ty))))

-- | 6.3.1.8 Returns the /common real type/. Note that this type might be
-- different either of the types because of integer promotion rules.
getCommonRealType :: Ev m => CIntegralType -> CIntegralType -> m CIntegralType
getCommonRealType ty1' ty2' = do
  md <- ask
  ty1 <- integerPromoteType ty1'
  ty2 <- integerPromoteType ty2'
  case (isSigned md ty1, isSigned md ty2, conversionRank ty1, conversionRank ty2) of
    (ty1Signed, ty2Signed, ty1Rank, ty2Rank)
          -- Rule 1
          | ty1 == ty2 -> pure ty1
          -- Rule 2
          | ty1Signed == ty2Signed && ty1Rank > ty2Rank -> pure ty1
          | ty1Signed == ty2Signed -> pure ty2
          -- Rule 3
          | not ty1Signed && ty2Signed && ty1Rank >= ty2Rank -> pure ty1
          | ty1Signed && not ty2Signed && ty2Rank >= ty1Rank -> pure ty2
          -- Rule 4
          | not ty1Signed && ty2Signed && areAllValuesRepresentableIn md ty1 ty2 -> pure ty2
          | ty1Signed && not ty2Signed && areAllValuesRepresentableIn md ty2 ty1 -> pure ty1
          -- Rule 5
          | not ty1Signed && ty2Signed -> pure ty1
          | ty1Signed && not ty2Signed -> pure ty2
          | otherwise -> error "Internal error: could not perform usual arithmetic conversion"

-- | 6.3.1.8 Perform the usual arithmetic conversions.
usualArithmeticConversion :: Ev m => CIntegral -> CIntegral -> m (CIntegralType, Integer, Integer)
usualArithmeticConversion (CIntegral ty1 v1) (CIntegral ty2 v2) = do
  crt <- getCommonRealType ty1 ty2
  CIntegral _ a <- integerConvertType crt v1
  CIntegral _ b <- integerConvertType crt v2
  pure (crt, a, b)

sizeof :: Ev m => CIntegralType -> m Int
sizeof (CIntegralType sz _) = asks $ \md ->
  let bits = view (sizeToBits sz) md
      roundedUp =
        case bits `quotRem` view charBits md of
          (b, 0) -> b
          (b, _) -> 1 + b
  in roundedUp + view (sizeToAddlPadding sz) md

-- ** C Operators

-- | 6.5.3.4 The C @sizeof@ operator as applied to a type. Only integral types
-- are currently supported.
cSizeofOnType :: Ev m => CIntegralType -> m CIntegral
cSizeofOnType ty = do
  v <- sizeof ty
  sz <- view sizetSize
  pure $ CIntegral (CIntegralType sz Unsigned) (fromIntegral v)

cBinaryOp :: Ev m =>((CIntegralType, Integer, Integer) -> m CIntegral) -> CIntegral -> CIntegral -> m CIntegral
cBinaryOp f a b = usualArithmeticConversion a b >>= f

cSimpleBinaryOp :: Ev m => (Integer -> Integer -> Integer) -> CIntegral -> CIntegral -> m CIntegral
cSimpleBinaryOp f a b = do
  (ty, v1, v2) <- usualArithmeticConversion a b
  integerConvertType ty (f v1 v2)

cUnaryPlus, cUnaryMinus :: Ev m => CIntegral -> m CIntegral
cUnaryPlus = integerPromotion
cUnaryMinus a = do
  CIntegral ty v <- integerPromotion a
  integerConvertType ty (negate v)

cBinaryPlus, cBinaryMinus, cMult, cDiv, cMod, cShiftLeft, cShiftRight :: Ev m => CIntegral -> CIntegral -> m CIntegral
cBinaryPlus = cSimpleBinaryOp (+)
cBinaryMinus = cSimpleBinaryOp (-)

cMult = cSimpleBinaryOp (*)

cDivModHandlingZero :: Ev m => (Integer -> Integer -> Integer) -> CIntegral -> CIntegral -> m CIntegral
cDivModHandlingZero f = cBinaryOp $ \(ty, a, b) ->
  if b == 0
  then
    view onDivByZero >>= \case
      DBZHalt -> throwError (UndefinedBehaviorHalted DivisionByZero)
      ReturnDividend -> integerConvertType ty a
  else integerConvertType ty (f a b)

cDiv = cDivModHandlingZero quot
cMod = cDivModHandlingZero rem

data BitVector
  = BitVector
  { bvSize :: Int
  , bvBits :: Integer
  } deriving (Show, Eq)

allLowerBitsSet :: Int -> Integer
allLowerBitsSet w | w >= 0 = (1 `shiftL` w) - 1
                  | otherwise = 0

toBitVector :: Ev m => CIntegral -> m BitVector
toBitVector cint = asks $ \md ->
  let CIntegral (CIntegralType sz _) v = cint
      w = view (sizeToBits sz) md
  in case (v >= 0, view negativeRep md) of
    (True, _) -> BitVector w v
    (False, TwosComplement) -> BitVector w (v .&. allLowerBitsSet w)
    (False, OnesComplement _) -> BitVector w ((v + 1) .&. allLowerBitsSet w)
    (False, SignMagnitude _) -> BitVector w (negate v .|. bit (w - 1))

fromBitVector :: Ev m => CIntegralType -> BitVector -> m CIntegral
fromBitVector ty@(CIntegralType sz _) (BitVector w v) = asks $ \md -> assert (view (sizeToBits sz) md == w) $
  let signedType = isSigned md ty
      negative = signedType && testBit v (w - 1)
  in case (negative, view negativeRep md) of
    (False, _) -> CIntegral ty v
    (True, TwosComplement) -> CIntegral ty (v .|. ((-1) .&. complement (allLowerBitsSet w)))
    (True, OnesComplement _) -> CIntegral ty (1 + (v .|. ((-1) .&. complement (allLowerBitsSet w))))
    (True, SignMagnitude _) -> CIntegral ty (negate (clearBit v (w - 1)))

logicalShift :: BitVector -> Int -> BitVector
logicalShift (BitVector w v) i = BitVector w ((v `shift` i) .&. allLowerBitsSet w)

arithmeticShift :: BitVector -> Int -> BitVector
arithmeticShift b i
  | i >= 0 = logicalShiftResult
  | otherwise = -- sign extend the top i bits
      let signExtension = allLowerBitsSet w .&. complement (allLowerBitsSet (w - i))
      in BitVector w (lv .|. signExtension)
  where logicalShiftResult@(BitVector w lv) = logicalShift b i

cShiftLeft a b = do
  pa@(CIntegral ty1@(CIntegralType sz _) v1) <- integerPromotion a
  CIntegral ty2 v2 <- integerPromotion b
  md <- ask
  if | v2 < 0 ->
       view onShiftByNegative >>= \case
          BSBNHalt -> throwError (UndefinedBehaviorHalted ShiftByNegative)
          ShiftInOtherDirection -> cShiftRight pa (CIntegral ty2 (negate v2))
     | fromIntegral v2 >= view (sizeToBits sz) md ->
        view onShiftTooMuch >>= \case
          BSTMHalt -> throwError (UndefinedBehaviorHalted ShiftTooMuch)
          ShiftAsIfInfinitePrecision -> undefined
          ModuloShiftAmount -> integerConvertType ty1 (v1 `shiftL` (fromIntegral v2 `mod` view (sizeToBits sz) md))
     | otherwise -> do
         bv <- toBitVector pa
         fromBitVector ty1 (bv `logicalShift` fromIntegral v2)

cShiftRight a b = do
  pa@(CIntegral ty1@(CIntegralType sz _) v1) <- integerPromotion a
  CIntegral ty2 v2 <- integerPromotion b
  md <- ask
  if | v2 < 0 ->
       view onShiftByNegative >>= \case
         BSBNHalt -> throwError (UndefinedBehaviorHalted ShiftByNegative)
         ShiftInOtherDirection -> cShiftLeft pa (CIntegral ty2 (negate v2))
     | fromIntegral v2 >= view (sizeToBits sz) md ->
       view onShiftTooMuch >>= \case
         BSTMHalt -> throwError (UndefinedBehaviorHalted ShiftTooMuch)
         ShiftAsIfInfinitePrecision -> undefined
         ModuloShiftAmount -> integerConvertType ty1 (v1 `shiftR` (fromIntegral v2 `mod` view (sizeToBits sz) md))
     | otherwise -> do
         bv <- toBitVector pa
         view onRightShiftNegative >>= \case
           LogicalShift -> fromBitVector ty1 (bv `logicalShift` negate (fromIntegral v2))
           ArithmeticShift -> fromBitVector ty1 (bv `arithmeticShift` negate (fromIntegral v2))
