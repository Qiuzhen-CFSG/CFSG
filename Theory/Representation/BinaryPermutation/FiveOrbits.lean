module
public import Theory.Representation.BinaryPermutation.FiveAction
public import Mathlib.GroupTheory.Index

/-!
# Nonzero orbits and stabilizers in the binary five-point core

The even-weight core is the four-dimensional natural deleted-permutation
module. Its nonzero vectors have weights two or four. Their symmetric
stabilizers have orders twelve and twenty-four, giving orbit sizes ten
and five. For a weight-two vector, restriction of its alternating
stabilizer to the three zero coordinates is faithful and onto S₃.
The existing minus quadratic form identifies weight two with nonsingularity.

The finite checks concern sixteen vectors and at most 120 permutations;
no subgroup lattice or larger matrix group is enumerated. The actual
zero-coordinate restriction supplies the S₃ equivalence, rather than
recognition from order alone.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §B.3 and
the S₅ case of 13.1.12, printed pp.872–873.
-/

@[expose] public section
namespace BinaryPermutation.FiveOrbits
open Subgroup
abbrev Space := core (Fin 5)
abbrev S5 := Equiv.Perm (Fin 5)
abbrev A5 := alternatingGroup (Fin 5)
abbrev rho := coreRepresentation (Fin 5)

local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype Space := Subtype.fintype _

def weight (v : Space) : ℕ := (Finset.univ.filter fun i => v.val i ≠ 0).card

def stabilizer (v : Space) : Subgroup S5 where
  carrier := {g | rho g v = v}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change rho (g*h) v = v
    rw [map_mul,Module.End.mul_apply,hh,hg]
  inv_mem' {g} hg := (rho.inv_apply_eq_iff).mpr hg.symm

def evenStabilizer (v : Space) : Subgroup A5 := (stabilizer v).comap (alternatingGroup (Fin 5)).subtype

local instance (v : Space) : DecidablePred (· ∈ stabilizer v) := fun g =>
  inferInstanceAs (Decidable (rho g v = v))
local instance (v : Space) : Fintype (stabilizer v) := Subtype.fintype _
local instance (v : Space) : DecidablePred (· ∈ evenStabilizer v) := fun g =>
  inferInstanceAs (Decidable (rho g.val v = v))
local instance (v : Space) : Fintype (evenStabilizer v) := Subtype.fintype _

theorem weight_nonzero (v : Space) (hv : v ≠ 0) : weight v = 2 ∨ weight v = 4 := by
  have h : ∀ v : Space, v ≠ 0 → weight v = 2 ∨ weight v = 4 := by decide +kernel
  exact h v hv

theorem stabilizer_card (v : Space) :
    Nat.card (stabilizer v) = if v = 0 then 120 else if weight v = 2 then 12 else 24 := by
  rw [Nat.card_eq_fintype_card]
  have h : ∀ v : Space, Fintype.card (stabilizer v) =
      if v = 0 then 120 else if weight v = 2 then 12 else 24 := by decide +kernel
  exact h v

theorem evenStabilizer_card (v : Space) :
    Nat.card (evenStabilizer v) = if v = 0 then 60 else if weight v = 2 then 6 else 12 := by
  rw [Nat.card_eq_fintype_card]
  have h : ∀ v : Space, Fintype.card (evenStabilizer v) =
      if v = 0 then 60 else if weight v = 2 then 6 else 12 := by decide +kernel
  exact h v


theorem weight_zero : weight (0 : Space) = 0 := by decide

theorem stabilizer_index (v : Space) (hv : v ≠ 0) :
    (stabilizer v).index = if weight v = 2 then 10 else 5 := by
  have hcard : Nat.card S5 = 120 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]; decide
  have hc := (stabilizer v).card_mul_index
  rw [stabilizer_card,if_neg hv,hcard] at hc
  split_ifs at hc ⊢ <;> omega

/-- The literal symmetric orbit has size ten or five, according to weight. -/
theorem orbit_card (v : Space) (hv : v ≠ 0) :
    (Set.range fun g : S5 => rho g v).ncard = if weight v = 2 then 10 else 5 := by
  let : MulAction S5 Space := {
    smul := fun g w => rho g w
    one_smul := fun w => by change rho 1 w = w; simp
    mul_smul := fun g h w => by change rho (g*h) w = rho g (rho h w); rw [map_mul,Module.End.mul_apply] }
  have hs : MulAction.stabilizer S5 v = stabilizer v := rfl
  rw [← show (MulAction.stabilizer S5 v).index =
    (Set.range fun g : S5 => rho g v).ncard from MulAction.index_stabilizer S5 v, hs]
  exact stabilizer_index v hv

private theorem fixes_coordinates (v : Space) (g : evenStabilizer v) (i : Fin 5) :
    v.val (g.val.val i) = v.val i := by
  have hh := congrArg (fun w : Space => w.val (g.val.val i)) g.property
  change v.val (g.val.val.symm (g.val.val i)) = v.val (g.val.val i) at hh
  simpa only [Equiv.symm_apply_apply] using hh.symm

/-- The actual action of the alternating vector stabilizer on its zero coordinates. -/
def zeroAction (v : Space) : evenStabilizer v →* Equiv.Perm {i : Fin 5 // v.val i = 0} where
  toFun g := g.val.val.subtypePerm (fun i => by rw [fixes_coordinates v g i])
  map_one' := by ext i; rfl
  map_mul' _ _ := by ext i; rfl

private theorem fix_zeros_eq_one : ∀ v : Space, weight v = 2 → ∀ g : A5,
    rho g.val v = v → (∀ i : Fin 5, v.val i = 0 → g.val i = i) → g = 1 := by
  decide +kernel

theorem zeroAction_injective (v : Space) (hw : weight v = 2) :
    Function.Injective (zeroAction v) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro g hg
  apply Subtype.ext
  apply fix_zeros_eq_one v hw g.val g.property
  intro i hi
  exact congrArg Subtype.val (DFunLike.congr_fun hg ⟨i,hi⟩)

theorem zero_card (v : Space) (hw : weight v = 2) :
    Fintype.card {i : Fin 5 // v.val i = 0} = 3 := by
  have hh : ∀ v : Space, weight v = 2 → Fintype.card {i : Fin 5 // v.val i = 0} = 3 := by
    decide +kernel
  exact hh v hw

/-- A nonsingular vector's alternating stabilizer is S₃ through its faithful
permutation action on the three zero coordinates. -/
noncomputable def evenStabilizerEquivS3 (v : Space) (hw : weight v = 2) :
    evenStabilizer v ≃* Equiv.Perm (Fin 3) := by
  have hv : v ≠ 0 := by intro he; rw [he,weight_zero] at hw; omega
  have hc : Nat.card (evenStabilizer v) =
      Nat.card (Equiv.Perm {i : Fin 5 // v.val i = 0}) := by
    rw [evenStabilizer_card,if_neg hv,if_pos hw,Nat.card_eq_fintype_card,Fintype.card_perm,zero_card v hw]
    decide
  let e := MulEquiv.ofBijective (zeroAction v)
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨zeroAction_injective v hw,hc⟩)
  exact e.trans ((Fintype.equivFinOfCardEq (zero_card v hw)).permCongrHom)

/-- The alternating stabilizer of a weight-two vector is nonabelian. -/
theorem evenStabilizer_not_commutative (v : Space) (hw : weight v = 2) :
    ¬ IsMulCommutative (evenStabilizer v) := by
  intro hc
  let e := evenStabilizerEquivS3 v hw
  have hab := (isMulCommutative_iff.mp hc)
    (e.symm (Equiv.swap 0 1)) (e.symm (Equiv.swap 1 2))
  have hh := congrArg e hab
  simp only [map_mul,e.apply_symm_apply] at hh
  have hn : (Equiv.swap 0 1 : Equiv.Perm (Fin 3))*Equiv.swap 1 2 ≠
      Equiv.swap 1 2*Equiv.swap 0 1 := by decide
  exact hn hh


/-- Nonsingular means exactly weight two for the existing minus form. -/
theorem nonsingular_iff_weight_two (v : Space) : FiveGeometry.form v ≠ 0 ↔ weight v = 2 := by
  constructor
  · intro hn
    have hv : v ≠ 0 := by intro hz; exact hn (hz ▸ FiveGeometry.form.map_zero)
    exact (weight_nonzero v hv).resolve_right (fun hw => hn ((FiveGeometry.singular_iff v).mpr (Or.inr hw)))
  · intro hw hz
    rcases (FiveGeometry.singular_iff v).mp hz with hv | hv
    · rw [hv,weight_zero] at hw; omega
    · change weight v = 4 at hv; omega

end BinaryPermutation.FiveOrbits
