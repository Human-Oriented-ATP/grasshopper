
import Grasshopper.ProcessingAndAutomation

set_option grasshopper.add_theorems true

example -- 0
  (jumps : JumpSet)
  (mines : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  (Multiset.sizeOf jumps) <= 0 →
  False
:= by
  intros
  auto


example -- 1
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (Multiset.sizeOf jumpsr) = 0 →
  (¬ (JumpSet.sum (((JumpSet.singleton jumps_max) : JumpSet) - jumps)) = 0) →
  False
:= by
  intros
  auto


example -- 2
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (Multiset.sizeOf jumpsr) = 0 →
  (¬ (JumpSet.sum (jumps - ((JumpSet.singleton jumps_max) : JumpSet))) = 0) →
  False
:= by
  intros
  auto


example -- 3
  (boom : Int)
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (Multiset.sizeOf jumpsr) = 0 →
  (boom + -1*(Jump.length jumps_max) + 1) = 0 →
  ↑(List.getIndexD mines boom) →
  False
:= by
  intros
  auto


example -- 4
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  ((¬ 0 <= (Jump.length jumps_max)) ∨ (¬ (Jump.length jumps_max) <= (MineField.length mines))) →
  False
:= by
  intros
  auto


example -- 5
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  ((¬ 0 <= ((Jump.length jumps_max) + -1)) ∨ (¬ ((Jump.length jumps_max) + -1) <= (MineField.length mines0))) →
  False
:= by
  intros
  auto


example -- 6
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (¬ (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1)) →
  ((Multiset.sizeOf jumps) <= (Multiset.sizeOf jumpsr) ∨ (¬ (Multiset.Nodup jumpsr)) ∨ (¬ (JumpSet.sum jumpsr) = ((MineField.length mines1) + 1)) ∨ (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1)) →
  False
:= by
  intros
  auto


example -- 7
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (¬ (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines1 X)))) →
  (¬ (JumpSet.sum (((JumpSet.singleton jumps_max) + (Jumps.s jumps_ih) : JumpSet) - jumps)) = 0) →
  False
:= by
  intros
  auto


example -- 8
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (¬ (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines1 X)))) →
  (¬ (JumpSet.sum (jumps - ((JumpSet.singleton jumps_max) + (Jumps.s jumps_ih) : JumpSet))) = 0) →
  False
:= by
  intros
  auto


example -- 9
  (boom : Int)
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (¬ (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines1 X)))) →
  ((boom + -1*(Jump.length jumps_max) + 1) = 0 ∨ ↑(List.getIndexD (Jumps.landings jumps_ih) (boom + -1*(Jump.length jumps_max)))) →
  ↑(List.getIndexD mines boom) →
  False
:= by
  intros
  auto


example -- 10
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  (MineField.countMines mines1) <= 0 →
  False
:= by
  intros
  auto


example -- 11
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  ((Multiset.sizeOf jumps) <= (Multiset.sizeOf jumpsr) ∨ (¬ (Multiset.Nodup jumpsr)) ∨ (¬ (JumpSet.sum jumpsr) = ((MineField.length mines10) + (MineField.length mines11) + 2)) ∨ (Multiset.sizeOf jumpsr) <= ((MineField.countMines mines10) + (MineField.countMines mines11))) →
  False
:= by
  intros
  auto


example -- 12
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  (¬ ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10))) →
  (¬ (JumpSet.sum (((JumpSet.singleton jumps_max) + (Jumps.s jumps_ih) : JumpSet) - jumps)) = 0) →
  False
:= by
  intros
  auto


example -- 13
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  (¬ ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10))) →
  (¬ (JumpSet.sum (jumps - ((JumpSet.singleton jumps_max) + (Jumps.s jumps_ih) : JumpSet))) = 0) →
  False
:= by
  intros
  auto


example -- 14
  (boom : Int)
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  (¬ ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10))) →
  ((boom + -1*(Jump.length jumps_max) + 1) = 0 ∨ ↑(List.getIndexD (Jumps.landings jumps_ih) (boom + -1*(Jump.length jumps_max)))) →
  ↑(List.getIndexD mines boom) →
  False
:= by
  intros
  auto


example -- 15
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10)) →
  ((¬ 0 <= ((MineField.length mines10) + 1)) ∨ (JumpSet.sum (Jumps.s jumps_ih)) <= ((MineField.length mines10) + 1)) →
  False
:= by
  intros
  auto


example -- 16
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jumps)
  (jumps_ih1 : Jumps)
  (jumps_ih_mid : Jump)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10)) →
  jumps_ih = jumps_ih0 ++ [jumps_ih_mid] ++ jumps_ih1 →
  (JumpSet.sum (Jumps.s jumps_ih0)) <= ((MineField.length mines10) + 1) →
  (¬ ((JumpSet.sum (Jumps.s jumps_ih0)) + (Jump.length jumps_ih_mid)) <= ((MineField.length mines10) + 1)) →
  (¬ (JumpSet.sum (((Jumps.s jumps_ih0) + (JumpSet.singleton jumps_ih_mid) + (JumpSet.singleton jumps_max) + (Jumps.s jumps_ih1) : JumpSet) - jumps)) = 0) →
  False
:= by
  intros
  auto


example -- 17
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jumps)
  (jumps_ih1 : Jumps)
  (jumps_ih_mid : Jump)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10)) →
  jumps_ih = jumps_ih0 ++ [jumps_ih_mid] ++ jumps_ih1 →
  (JumpSet.sum (Jumps.s jumps_ih0)) <= ((MineField.length mines10) + 1) →
  (¬ ((JumpSet.sum (Jumps.s jumps_ih0)) + (Jump.length jumps_ih_mid)) <= ((MineField.length mines10) + 1)) →
  (¬ (JumpSet.sum (jumps - ((Jumps.s jumps_ih0) + (JumpSet.singleton jumps_ih_mid) + (JumpSet.singleton jumps_max) + (Jumps.s jumps_ih1) : JumpSet))) = 0) →
  False
:= by
  intros
  auto


example -- 18
  (boom : Int)
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jumps)
  (jumps_ih1 : Jumps)
  (jumps_ih_mid : Jump)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  (¬ ↑(List.getIndexD mines01 0)) →
  (Multiset.sizeOf jumpsr) <= (MineField.countMines mines1) →
  mines1 = mines10 ++ [true] ++ mines11 →
  (MineField.countMines mines10) = 0 →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines10 X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines10) + -1)))))) →
  ↑(List.getIndexD (Jumps.landings jumps_ih) (MineField.length mines10)) →
  jumps_ih = jumps_ih0 ++ [jumps_ih_mid] ++ jumps_ih1 →
  (JumpSet.sum (Jumps.s jumps_ih0)) <= ((MineField.length mines10) + 1) →
  (¬ ((JumpSet.sum (Jumps.s jumps_ih0)) + (Jump.length jumps_ih_mid)) <= ((MineField.length mines10) + 1)) →
  (↑(List.getIndexD (Jumps.landings jumps_ih0) boom) ∨ (boom + -1*(JumpSet.sum (Jumps.s jumps_ih0)) + -1*(Jump.length jumps_ih_mid) + 1) = 0 ∨ (boom + -1*(JumpSet.sum (Jumps.s jumps_ih0)) + -1*(Jump.length jumps_ih_mid) + -1*(Jump.length jumps_max) + 1) = 0 ∨ ↑(List.getIndexD (Jumps.landings jumps_ih1) (boom + -1*(JumpSet.sum (Jumps.s jumps_ih0)) + -1*(Jump.length jumps_ih_mid) + -1*(Jump.length jumps_max)))) →
  ↑(List.getIndexD mines boom) →
  False
:= by
  intros
  auto


example -- 19
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (MineField.length mines00) <= (MineField.length mines1) →
  ((¬ 0 <= (MineField.length mines00)) ∨ (¬ (MineField.length mines00) <= (MineField.length mines1))) →
  False
:= by
  intros
  auto


example -- 20
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (MineField.length mines00) <= (MineField.length mines1) →
  mines1 = mines10 ++ mines11 →
  (MineField.length mines10) = (MineField.length mines00) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines00 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines10 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines10) <= (MineField.length mines00)) ∨ (MineField.length mines_un) = (MineField.length mines00)) →
  ((¬ (MineField.length mines00) <= (MineField.length mines10)) ∨ (MineField.length mines_un) = (MineField.length mines10)) →
  (MineField.countMines mines00) <= (MineField.countMines mines_un) →
  (MineField.countMines mines10) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines00) + (MineField.countMines mines10)) →
  ((Multiset.sizeOf jumps) <= (Multiset.sizeOf jumpsr) ∨ (¬ (Multiset.Nodup jumpsr)) ∨ (¬ (JumpSet.sum jumpsr) = ((MineField.length mines_un) + (MineField.length mines11) + 1)) ∨ (Multiset.sizeOf jumpsr) <= ((MineField.countMines mines_un) + (MineField.countMines mines11))) →
  False
:= by
  intros
  auto


example -- 21
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (MineField.length mines00) <= (MineField.length mines1) →
  mines1 = mines10 ++ mines11 →
  (MineField.length mines10) = (MineField.length mines00) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines00 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines10 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines10) <= (MineField.length mines00)) ∨ (MineField.length mines_un) = (MineField.length mines00)) →
  ((¬ (MineField.length mines00) <= (MineField.length mines10)) ∨ (MineField.length mines_un) = (MineField.length mines10)) →
  (MineField.countMines mines00) <= (MineField.countMines mines_un) →
  (MineField.countMines mines10) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines00) + (MineField.countMines mines10)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines_un X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines_un))))))) →
  (Multiset.sizeOf (Jumps.s jumps_ih)) <= 0 →
  False
:= by
  intros
  auto


example -- 22
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jump)
  (jumps_ihr : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (MineField.length mines00) <= (MineField.length mines1) →
  mines1 = mines10 ++ mines11 →
  (MineField.length mines10) = (MineField.length mines00) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines00 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines10 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines10) <= (MineField.length mines00)) ∨ (MineField.length mines_un) = (MineField.length mines00)) →
  ((¬ (MineField.length mines00) <= (MineField.length mines10)) ∨ (MineField.length mines_un) = (MineField.length mines10)) →
  (MineField.countMines mines00) <= (MineField.countMines mines_un) →
  (MineField.countMines mines10) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines00) + (MineField.countMines mines10)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines_un X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines_un))))))) →
  jumps_ih = [jumps_ih0] ++ jumps_ihr →
  (¬ (JumpSet.sum (((JumpSet.singleton jumps_ih0) + (JumpSet.singleton jumps_max) + (Jumps.s jumps_ihr) : JumpSet) - jumps)) = 0) →
  False
:= by
  intros
  auto


example -- 23
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jump)
  (jumps_ihr : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (MineField.length mines00) <= (MineField.length mines1) →
  mines1 = mines10 ++ mines11 →
  (MineField.length mines10) = (MineField.length mines00) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines00 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines10 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines10) <= (MineField.length mines00)) ∨ (MineField.length mines_un) = (MineField.length mines00)) →
  ((¬ (MineField.length mines00) <= (MineField.length mines10)) ∨ (MineField.length mines_un) = (MineField.length mines10)) →
  (MineField.countMines mines00) <= (MineField.countMines mines_un) →
  (MineField.countMines mines10) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines00) + (MineField.countMines mines10)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines_un X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines_un))))))) →
  jumps_ih = [jumps_ih0] ++ jumps_ihr →
  (¬ (JumpSet.sum (jumps - ((JumpSet.singleton jumps_ih0) + (JumpSet.singleton jumps_max) + (Jumps.s jumps_ihr) : JumpSet))) = 0) →
  False
:= by
  intros
  auto


example -- 24
  (boom : Int)
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jump)
  (jumps_ihr : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines10 : MineField)
  (mines11 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (MineField.length mines00) <= (MineField.length mines1) →
  mines1 = mines10 ++ mines11 →
  (MineField.length mines10) = (MineField.length mines00) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines00 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines10 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines10) <= (MineField.length mines00)) ∨ (MineField.length mines_un) = (MineField.length mines00)) →
  ((¬ (MineField.length mines00) <= (MineField.length mines10)) ∨ (MineField.length mines_un) = (MineField.length mines10)) →
  (MineField.countMines mines00) <= (MineField.countMines mines_un) →
  (MineField.countMines mines10) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines00) + (MineField.countMines mines10)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ ((¬ ↑(List.getIndexD mines_un X)) ∧ (¬ ↑(List.getIndexD mines11 (X + -1*(MineField.length mines_un))))))) →
  jumps_ih = [jumps_ih0] ++ jumps_ihr →
  ((boom + -1*(Jump.length jumps_ih0) + 1) = 0 ∨ (boom + -1*(Jump.length jumps_ih0) + -1*(Jump.length jumps_max) + 1) = 0 ∨ ↑(List.getIndexD (Jumps.landings jumps_ihr) (boom + -1*(Jump.length jumps_ih0) + -1*(Jump.length jumps_max)))) →
  ↑(List.getIndexD mines boom) →
  False
:= by
  intros
  auto


example -- 25
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (¬ (MineField.length mines00) <= (MineField.length mines1)) →
  ((¬ 0 <= (MineField.length mines1)) ∨ (¬ (MineField.length mines1) <= (MineField.length mines00))) →
  False
:= by
  intros
  auto


example -- 26
  (jumps : JumpSet)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines000 : MineField)
  (mines001 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (¬ (MineField.length mines00) <= (MineField.length mines1)) →
  mines00 = mines000 ++ mines001 →
  (MineField.length mines000) = (MineField.length mines1) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines000 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines1 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines1) <= (MineField.length mines000)) ∨ (MineField.length mines_un) = (MineField.length mines000)) →
  ((¬ (MineField.length mines000) <= (MineField.length mines1)) ∨ (MineField.length mines_un) = (MineField.length mines1)) →
  (MineField.countMines mines000) <= (MineField.countMines mines_un) →
  (MineField.countMines mines1) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines000) + (MineField.countMines mines1)) →
  ((Multiset.sizeOf jumps) <= (Multiset.sizeOf jumpsr) ∨ (¬ (Multiset.Nodup jumpsr)) ∨ (¬ (JumpSet.sum jumpsr) = ((MineField.length mines_un) + 1)) ∨ (Multiset.sizeOf jumpsr) <= (MineField.countMines mines_un)) →
  False
:= by
  intros
  auto


example -- 27
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines000 : MineField)
  (mines001 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (¬ (MineField.length mines00) <= (MineField.length mines1)) →
  mines00 = mines000 ++ mines001 →
  (MineField.length mines000) = (MineField.length mines1) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines000 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines1 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines1) <= (MineField.length mines000)) ∨ (MineField.length mines_un) = (MineField.length mines000)) →
  ((¬ (MineField.length mines000) <= (MineField.length mines1)) ∨ (MineField.length mines_un) = (MineField.length mines1)) →
  (MineField.countMines mines000) <= (MineField.countMines mines_un) →
  (MineField.countMines mines1) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines000) + (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines_un X)))) →
  (Multiset.sizeOf (Jumps.s jumps_ih)) <= 0 →
  False
:= by
  intros
  auto


example -- 28
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jump)
  (jumps_ihr : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines000 : MineField)
  (mines001 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (¬ (MineField.length mines00) <= (MineField.length mines1)) →
  mines00 = mines000 ++ mines001 →
  (MineField.length mines000) = (MineField.length mines1) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines000 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines1 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines1) <= (MineField.length mines000)) ∨ (MineField.length mines_un) = (MineField.length mines000)) →
  ((¬ (MineField.length mines000) <= (MineField.length mines1)) ∨ (MineField.length mines_un) = (MineField.length mines1)) →
  (MineField.countMines mines000) <= (MineField.countMines mines_un) →
  (MineField.countMines mines1) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines000) + (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines_un X)))) →
  jumps_ih = [jumps_ih0] ++ jumps_ihr →
  (¬ (JumpSet.sum (((JumpSet.singleton jumps_ih0) + (JumpSet.singleton jumps_max) + (Jumps.s jumps_ihr) : JumpSet) - jumps)) = 0) →
  False
:= by
  intros
  auto


example -- 29
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jump)
  (jumps_ihr : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines000 : MineField)
  (mines001 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (¬ (MineField.length mines00) <= (MineField.length mines1)) →
  mines00 = mines000 ++ mines001 →
  (MineField.length mines000) = (MineField.length mines1) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines000 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines1 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines1) <= (MineField.length mines000)) ∨ (MineField.length mines_un) = (MineField.length mines000)) →
  ((¬ (MineField.length mines000) <= (MineField.length mines1)) ∨ (MineField.length mines_un) = (MineField.length mines1)) →
  (MineField.countMines mines000) <= (MineField.countMines mines_un) →
  (MineField.countMines mines1) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines000) + (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines_un X)))) →
  jumps_ih = [jumps_ih0] ++ jumps_ihr →
  (¬ (JumpSet.sum (jumps - ((JumpSet.singleton jumps_ih0) + (JumpSet.singleton jumps_max) + (Jumps.s jumps_ihr) : JumpSet))) = 0) →
  False
:= by
  intros
  auto


example -- 30
  (boom : Int)
  (jumps : JumpSet)
  (jumps_ih : Jumps)
  (jumps_ih0 : Jump)
  (jumps_ihr : Jumps)
  (jumps_max : Jump)
  (jumpsr : JumpSet)
  (mines : MineField)
  (mines0 : MineField)
  (mines00 : MineField)
  (mines000 : MineField)
  (mines001 : MineField)
  (mines01 : MineField)
  (mines1 : MineField)
  (mines_un : MineField)
  (size : Int)
: (Multiset.Nodup jumps) →
  (JumpSet.sum jumps) = (size + 1) →
  (MineField.length mines) = size →
  (¬ (Multiset.sizeOf jumps) <= (MineField.countMines mines)) →
  jumps = ((JumpSet.singleton jumps_max) + jumpsr : JumpSet) →
  (∀ (X : Jump), ((¬ X ∈ jumpsr) ∨ (Jump.length X) <= (Jump.length jumps_max))) →
  (¬ (Multiset.sizeOf jumpsr) = 0) →
  mines = mines0 ++ mines1 →
  (MineField.length mines0) = (Jump.length jumps_max) →
  mines0 = mines00 ++ mines01 →
  (MineField.length mines00) = ((Jump.length jumps_max) + -1) →
  ↑(List.getIndexD mines01 0) →
  (¬ (MineField.length mines00) <= (MineField.length mines1)) →
  mines00 = mines000 ++ mines001 →
  (MineField.length mines000) = (MineField.length mines1) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines000 X)) ∨ ↑(List.getIndexD mines_un X))) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD mines1 X)) ∨ ↑(List.getIndexD mines_un X))) →
  ((¬ (MineField.length mines1) <= (MineField.length mines000)) ∨ (MineField.length mines_un) = (MineField.length mines000)) →
  ((¬ (MineField.length mines000) <= (MineField.length mines1)) ∨ (MineField.length mines_un) = (MineField.length mines1)) →
  (MineField.countMines mines000) <= (MineField.countMines mines_un) →
  (MineField.countMines mines1) <= (MineField.countMines mines_un) →
  (MineField.countMines mines_un) <= ((MineField.countMines mines000) + (MineField.countMines mines1)) →
  jumpsr = (Jumps.s jumps_ih) →
  (∀ (X : Int), ((¬ ↑(List.getIndexD (Jumps.landings jumps_ih) X)) ∨ (¬ ↑(List.getIndexD mines_un X)))) →
  jumps_ih = [jumps_ih0] ++ jumps_ihr →
  ((boom + -1*(Jump.length jumps_ih0) + 1) = 0 ∨ (boom + -1*(Jump.length jumps_ih0) + -1*(Jump.length jumps_max) + 1) = 0 ∨ ↑(List.getIndexD (Jumps.landings jumps_ihr) (boom + -1*(Jump.length jumps_ih0) + -1*(Jump.length jumps_max)))) →
  ↑(List.getIndexD mines boom) →
  False
:= by
  intros
  auto

