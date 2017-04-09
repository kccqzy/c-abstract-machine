{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

module Lib where

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
  , _negativeRep :: NegativeRepresentation
  , _onSignedOverflow :: OnSignedIntegerOverflow
  , _onDivByZero :: OnDivisionByZero
  , _sizetSize :: CIntegralSize
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
  else pure (CIntegral ty (v `mod` snd (representableRange md ty)))

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

cBinaryPlus, cBinaryMinus, cMult, cDiv, cMod :: Ev m => CIntegral -> CIntegral -> m CIntegral
cBinaryPlus = cSimpleBinaryOp (+)
cBinaryMinus = cSimpleBinaryOp (-)
cMult = cSimpleBinaryOp (*)
cDiv = cBinaryOp $ \(ty, a, b) ->
  if b == 0
  then
    view onDivByZero >>= \case
      DBZHalt -> throwError (UndefinedBehaviorHalted DivisionByZero)
      ReturnDividend -> integerConvertType ty a
  else integerConvertType ty (a `quot` b)
cMod = cBinaryOp $ \(ty, a, b) ->
  if b == 0
  then
    view onDivByZero >>= \case
      DBZHalt -> throwError (UndefinedBehaviorHalted DivisionByZero)
      ReturnDividend -> integerConvertType ty a
  else integerConvertType ty (a `rem` b)
