{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
module CMachine.Basic where

import           CMachine.Types
import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.Bits            hiding (isSigned)

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
