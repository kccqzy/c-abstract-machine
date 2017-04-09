{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# LANGUAGE MultiWayIf       #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE StrictData       #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE TupleSections    #-}

module CMachine.Types where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
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
