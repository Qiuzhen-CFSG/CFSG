module
public import Theory.SpecificGroups.SymmetricSix.PolarAffine
public import Theory.SpecificGroups.SymmetricSix.HexadCubicWord
import all Theory.SpecificGroups.SymmetricSix.HexadCubicWord
open Equiv Subgroup Subgroup.CosetWordCertificate
open Matrix.PSL3Four.MathieuAmalgamMarking
namespace Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
open HexadCubicWord
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
private def decode (i : Fin 16) : NaturalModule :=
  vec (i.val:ZMod 2) ((i.val/2:Nat):ZMod 2) ((i.val/4:Nat):ZMod 2) ((i.val/8:Nat):ZMod 2)
private def plus (i j : Fin 16) : Fin 16 := Fin.ofNat 16 (i.val ^^^ j.val)
private def encodePoint (d : Duad) : Fin 16 :=
  ![8,2,14,11,15,10,6,3,7,12,9,13,5,1,4] d
private def duadOf (i : Fin 16) : Duad :=
  ![0,13,1,7,14,12,6,8,0,10,5,3,9,11,2,4] i
private def lo (d : Duad) : Letter := ![0,0,0,0,0,1,1,1,1,2,2,2,3,3,4] d
private def hi (d : Duad) : Letter := ![1,2,3,4,5,2,3,4,5,3,4,5,4,5,5] d
private def pairIdx (i j : Letter) : Duad :=
  ![![0,0,1,2,3,4],![0,0,5,6,7,8],![1,5,0,9,10,11],
    ![2,6,9,0,12,13],![3,7,10,12,0,14],![4,8,11,13,14,0]] i j
private def move (g : S6) (d : Duad) : Duad := pairIdx (g (lo d)) (g (hi d))
private theorem move_eq (g : S6) (d : Duad) : move g d=g • d := by
  apply duadSet_injective
  rw [duadSet_smul]
  have hp : ∀ i j : Letter, i≠j → duadSet (pairIdx i j)={i,j} := by decide +kernel
  have hd : ∀ d : Duad, duadSet d={lo d,hi d} ∧ lo d≠hi d := by decide +kernel
  rw [move,hp _ _ (g.injective.ne (hd d).2),(hd d).1]
  simp
private def act (g : S6) (i : Fin 16) : Fin 16 :=
  if i=0 then 0 else encodePoint (move g (duadOf i))
private theorem decode_zero : decode 0=0 := by decide +kernel
private theorem decode_plus : ∀ i j, decode (plus i j)=decode i+decode j := by decide +kernel
private theorem decode_neg : ∀ i, -decode i=decode i := by decide +kernel
private theorem decode_point : ∀ d, decode (encodePoint d)=(polarVector d).val := by decide +kernel
private theorem decode_of : ∀ i, i≠0 → decode i=(polarVector (duadOf i)).val := by decide +kernel
private theorem decode_surjective : Function.Surjective decode := by decide +kernel
private theorem decode_act (g : S6) (i : Fin 16) :
    decode (act g i)=polarAction g (decode i) := by
  by_cases hi : i=0
  · simp [act,hi,decode_zero]
  rw [act,if_neg hi,decode_point,move_eq,decode_of i hi,polarAction_vector]
private abbrev Raw := Fin 16 × S6
private def mul (x y : Raw) : Raw := (plus x.1 (act x.2 y.1),x.2*y.2)
private def inv (x : Raw) : Raw := (act x.2⁻¹ x.1,x.2⁻¹)
private def ev {α : Type*} (p : α→Raw) (w : Word α) : Raw :=
  w.foldl (fun x a => mul x (if a.2 then p a.1 else inv (p a.1))) (0,1)
private def pw (x : Raw) : Nat→Raw
  | 0 => (0,1)
  | n+1 => mul (pw x n) x
private def c1 : S6 := swap 1 3 * swap 3 5
private def c2 : S6 := swap 0 2 * swap 2 4 * (swap 1 5 * swap 5 3)
private def c3 : S6 := swap 0 4 * swap 4 2
local instance : Fintype S6 := fintypePerm

private theorem candidates : ∀ n : S6, n^3=1 →
    n * eval ![a0,b0] torusWord=eval ![a0,b0] torusWord * n →
    (b0*n*a0⁻¹)^4=1 → n=c1 ∨ n=c2 ∨ n=c3 := by decide +kernel
private def lin (a b c d v : Fin 16) : Fin 16 :=
  plus (plus (if v.val%2=1 then a else 0) (if (v.val/2)%2=1 then b else 0))
    (plus (if (v.val/4)%2=1 then c else 0) (if (v.val/8)%2=1 then d else 0))
private def u1 (v w : Fin 16) : Fin 16 := plus (lin 1 6 7 1 v) (lin 7 0 7 1 w)
private def u2 (v w : Fin 16) : Fin 16 := plus (lin 6 12 8 15 v) (lin 3 11 10 13 w)
private def u3 (v w : Fin 16) : Fin 16 := plus (lin 0 9 2 2 v) (lin 11 9 9 9 w)
private def shift (v : Fin 16) : Raw := (act a0 v,1)
private theorem normalize : ∀ v : Fin 16,
    mul (mul (shift v) (v,a0)) (inv (shift v))=(0,a0) := by decide +kernel
private theorem check1 : ∀ w : Fin 16,
    let a : Raw := (0,a0)
    let b : Raw := (w,b0)
    let n : Raw := (u1 0 w,c1)
    mul n (ev ![a,b] torusWord)=mul (ev ![a,b] torusWord) n ∧
    pw (mul (mul b n) (inv a)) 4=(0,1) := by
  decide +kernel
private theorem check2 : ∀ w : Fin 16,
    let a : Raw := (0,a0)
    let b : Raw := (w,b0)
    let n : Raw := (u2 0 w,c2)
    mul n (ev ![a,b] torusWord)=mul (ev ![a,b] torusWord) n ∧
    pw (mul (mul b n) (inv a)) 4=(0,1) := by
  decide +kernel
private theorem check3 : ∀ w : Fin 16,
    let a : Raw := (0,a0)
    let b : Raw := (w,b0)
    let n : Raw := (u3 0 w,c3)
    mul n (ev ![a,b] torusWord)=mul (ev ![a,b] torusWord) n ∧
    pw (mul (mul b n) (inv a)) 4=(0,1) := by
  decide +kernel

end Theory.SpecificGroups.SymmetricSix.HexadAffineNineteen
