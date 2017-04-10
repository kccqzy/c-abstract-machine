{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE MultiWayIf       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TupleSections    #-}

module CMachine.Operators
  ( cSizeofOnType
  , cUnaryPlus
  , cUnaryMinus
  , cBinaryPlus
  , cBinaryMinus
  , cMult
  , cDiv
  , cMod
  , cShiftLeft
  , cShiftRight
  )where

import           CMachine.Basic
import           CMachine.Types
import           Control.Exception    (assert)
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Bits            hiding (isSigned)

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

cUnaryPlus :: Ev m => CIntegral -> m CIntegral
cUnaryPlus = integerPromotion

cUnaryMinus :: Ev m => CIntegral -> m CIntegral
cUnaryMinus a = do
  CIntegral ty v <- integerPromotion a
  integerConvertType ty (negate v)

cBinaryPlus :: Ev m => CIntegral -> CIntegral -> m CIntegral
cBinaryPlus = cSimpleBinaryOp (+)

cBinaryMinus :: Ev m => CIntegral -> CIntegral -> m CIntegral
cBinaryMinus = cSimpleBinaryOp (-)

cMult :: Ev m => CIntegral -> CIntegral -> m CIntegral
cMult = cSimpleBinaryOp (*)

cDivModHandlingZero :: Ev m => (Integer -> Integer -> Integer) -> CIntegral -> CIntegral -> m CIntegral
cDivModHandlingZero f = cBinaryOp $ \(ty, a, b) ->
  if b == 0
  then
    view onDivByZero >>= \case
      DBZHalt -> throwError (UndefinedBehaviorHalted DivisionByZero)
      ReturnDividend -> integerConvertType ty a
  else integerConvertType ty (f a b)

cDiv :: Ev m => CIntegral -> CIntegral -> m CIntegral
cDiv = cDivModHandlingZero quot

cMod :: Ev m => CIntegral -> CIntegral -> m CIntegral
cMod = cDivModHandlingZero rem

data BitVector
  = BitVector
  { bvSize :: Int
  , bvBits :: Integer
  } deriving (Eq)

showBits :: BitVector -> String
showBits (BitVector w b) = foldr (\i s -> (if testBit b i then '1' else '0') : s) "" [w - 1, w - 2 .. 0]

instance Show BitVector where
  showsPrec p b@BitVector{..} =
    showParen (p >= 11) (showString "BitVector {" . showString "bvSize = " . shows bvSize . showString ", " . showString "bvBits = " . showString ("0b" ++ showBits b) . showString "}")

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

cShiftLeft :: Ev m => CIntegral -> CIntegral -> m CIntegral
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
     | view onLeftShiftNegative md == JustShift || v1 >= 0 -> do
         bv <- toBitVector pa
         fromBitVector ty1 (bv `logicalShift` fromIntegral v2)
     | otherwise -> throwError (UndefinedBehaviorHalted LeftShiftNegative)

cShiftRight :: Ev m => CIntegral -> CIntegral -> m CIntegral
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
