import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Init.Classical
import Mathlib.Tactic

abbrev Jump := PNat
abbrev MineField := List Bool
abbrev Jumps := List Jump
abbrev JumpSet := Multiset Jump

abbrev Jumps.length (jumps : Jumps) := List.length jumps
abbrev MineField.length (mineField : MineField) := List.length mineField
abbrev Jump.length (j : Jump) : Int := j

def List.getIndexD [Inhabited α] (l : List α) (idx : Int) : α :=
  match idx with
  | .ofNat n => l.getD n default
  | .negSucc _ => default

instance [Inhabited α] : GetElem (List α) Int α (fun _ _ => True) where
  getElem l idx _ := List.getIndexD l idx

abbrev JumpSet.sum (jumps : JumpSet) : Int := (jumps.map Jump.length).sum
abbrev MineField.countMines (mines : MineField) : Nat := mines.count true

abbrev jumpOver (j : Jump) : MineField := List.replicate j.natPred false
abbrev Jumps.landings (jumps : Jumps) : MineField := jumps.bind (fun j => (jumpOver j).concat true)
abbrev Jumps.s (jumps : Jumps) : JumpSet := .ofList jumps
abbrev Jumps.sum (jumps : Jumps) : Int := jumps.s.sum
