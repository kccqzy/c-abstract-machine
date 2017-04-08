{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}

module Lib where

import           Control.Lens
import           Data.Bits
import           Data.Default

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

int :: CIntegralType
int = CIntegralType CInt Signed

unsigned :: CIntegralType
unsigned = CIntegralType CInt Unsigned

data OnSignedIntegerOverflow = SIOHalt | WrapAround | Saturate
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
    , _charSigned = True
    , _negativeRep = TwosComplement
    , _onSignedOverflow = SIOHalt
    }

$(makeLenses ''MachineDesc)

data CIntegral = CIntegral CIntegralType Integer
  deriving (Show)

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
  _charBits <= _shortBits && _shortBits <= _intBits && _intBits <= _longBits && _longBits <= _longlongBits

-- | 6.3.1.1
conversionRank :: CIntegralType -> Int
conversionRank (CIntegralType sz _) = fromEnum sz

representableRange :: MachineDesc -> CIntegralType -> (Integer, Integer)
representableRange md (CIntegralType CChar Unspecified) =
  representableRange md (CIntegralType CChar (if view charSigned md then Signed else Unsigned))
representableRange md (CIntegralType sz Unspecified) = representableRange md (CIntegralType sz Signed)
representableRange md (CIntegralType sz Unsigned) = (0, 1 `shift` view (sizeToBits sz) md - 1)
representableRange md (CIntegralType sz Signed) =
  case view negativeRep md of
    TwosComplement -> (negate p, p - 1)
    _ -> (negate p + 1, p - 1)
  where p = 1 `shift` (view (sizeToBits sz) md - 1)

areAllValuesRepresentableIn :: MachineDesc -> CIntegralType -> CIntegralType -> Bool
areAllValuesRepresentableIn md a b =
  case (representableRange md a, representableRange md b) of
    ((aMin, aMax), (bMin, bMax)) -> aMin >= bMin && aMax <= bMax

integerPromotion :: MachineDesc -> CIntegral -> CIntegral
integerPromotion md v@(CIntegral ty val)
  | conversionRank ty < conversionRank int =
      if areAllValuesRepresentableIn md ty int then CIntegral int val else CIntegral unsigned val
  | otherwise = v

sizeof :: MachineDesc -> CIntegralType -> Int
sizeof md (CIntegralType sz _) =
  let bits = view (sizeToBits sz) md
      roundedUp =
        case bits `quotRem` view charBits md of
          (b, 0) -> b
          (b, _) -> 1 + b
  in roundedUp + view (sizeToAddlPadding sz) md
