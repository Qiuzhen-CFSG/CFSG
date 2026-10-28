module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.Models
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic

/-!
# Cores and conjugation in the three-block model

Projection of C₂ wr S₃ onto S₃ has the three-dimensional binary base as its
kernel. Its even subgroup has the even-parity base. These are the intrinsic
two-cores, since S₃ has no nontrivial normal two-subgroup. Finite kernel-checked
calculations establish self-centralization and transitivity on the three
nonidentity even vectors. The constant nonzero vector gives the invariant
line in the full wreath product.

All finite calculations take place on 48 model elements (24 in the even
subgroup); the preceding module identifies these with the actual parabolics.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.7,
printed pp. 420–421.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix.SynthemeCalculation

-- The derived equality for this structure transports over function equalities.
-- Testing its two components avoids those casts in kernel reduction.
local instance : DecidableEq Model := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
      fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩

abbrev quotientHom : Model →* Three := SemidirectProduct.rightHom
abbrev core : Subgroup Model := quotientHom.ker

def evenQuotientHom : evenModel →* Three := quotientHom.comp evenModel.subtype
abbrev evenCore : Subgroup evenModel := evenQuotientHom.ker

local instance : DecidablePred (· ∈ evenCore) := fun x =>
  inferInstanceAs (Decidable (x.val.right = 1))

theorem quotientHom_surjective : Function.Surjective quotientHom :=
  SemidirectProduct.rightHom_surjective

theorem evenQuotientHom_surjective : Function.Surjective evenQuotientHom := by
  intro g
  refine ⟨⟨SemidirectProduct.inr g, ?_⟩, rfl⟩
  rw [mem_evenModel]
  rfl

/-- Each kernel element is its vector of three independent within-block swaps. -/
def binaryEquiv : Binary ≃* core where
  toFun v := ⟨SemidirectProduct.inl v, rfl⟩
  invFun g := g.val.left
  left_inv _ := rfl
  right_inv g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact g.2.symm
  map_mul' x y := Subtype.ext (map_mul SemidirectProduct.inl x y)

instance : IsElementaryAbelian 2 core where
  is_comm.comm := by decide +kernel
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

instance : IsElementaryAbelian 2 evenCore where
  is_comm.comm := by decide +kernel
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

theorem core_card : Nat.card core = 8 := by
  rw [Nat.card_congr binaryEquiv.symm.toEquiv, Nat.card_eq_fintype_card]
  decide

theorem evenCore_card : Nat.card evenCore = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem core_eq : core = pCore 2 Model :=
  ker_eq_twoCore_of_surjective_perm_three _ quotientHom_surjective
    (IsElementaryAbelian.isPGroup 2 core)

theorem evenCore_eq : evenCore = pCore 2 evenModel :=
  ker_eq_twoCore_of_surjective_perm_three _ evenQuotientHom_surjective
    (IsElementaryAbelian.isPGroup 2 evenCore)

/-- The third swap is the sum of the first two, enforcing even parity. -/
def binaryFourHom : Multiplicative (Fin 2 → ZMod 2) →* Model where
  toFun v := SemidirectProduct.inl
    (Multiplicative.ofAdd ![v.toAdd 0, v.toAdd 1, v.toAdd 0 + v.toAdd 1])
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def binaryFourToCore : Multiplicative (Fin 2 → ZMod 2) →* evenCore :=
  (binaryFourHom.codRestrict evenModel (by decide +kernel)).codRestrict _ (by decide +kernel)

noncomputable def binaryFourEquiv : Multiplicative (Fin 2 → ZMod 2) ≃* evenCore :=
  MulEquiv.ofBijective binaryFourToCore (by decide +kernel)

/-- Conjugation permutes the three swap coordinates. -/
theorem conjugate_inl (g : Model) (v : Binary) :
    g * SemidirectProduct.inl v * g⁻¹ = SemidirectProduct.inl (permute g.right v) := by
  apply SemidirectProduct.ext
  · simp [mul_comm, mul_assoc]
  · simp

theorem centralizer_core : Subgroup.centralizer (core : Set Model) = core := by
  ext g
  rw [Subgroup.mem_centralizer_iff]
  exact (show ∀ g : Model, (∀ h ∈ core, h * g = g * h) ↔ g ∈ core by decide +kernel) g

theorem centralizer_evenCore : Subgroup.centralizer (evenCore : Set evenModel) = evenCore := by
  ext g
  rw [Subgroup.mem_centralizer_iff]
  exact (show ∀ g : evenModel, (∀ h ∈ evenCore, h * g = g * h) ↔ g ∈ evenCore
    by decide +kernel) g

theorem evenCore_conjugate : ∀ x ∈ evenCore, x ≠ 1 → ∀ y ∈ evenCore, y ≠ 1 →
    ∃ g : evenModel, g * x * g⁻¹ = y := by decide +kernel

theorem normal_subgroup_evenCore (N : Subgroup evenModel) [N.Normal]
    (hle : N ≤ evenCore) : N = ⊥ ∨ N = evenCore := by
  by_cases h : N = ⊥
  · exact Or.inl h
  right
  have hex : ∃ x ∈ N, x ≠ (1 : evenModel) := by
    by_contra! hh
    apply h
    apply le_antisymm _ bot_le
    intro x hx
    exact hh x hx
  obtain ⟨x,hx,hne⟩ := hex
  apply le_antisymm hle
  intro y hy
  by_cases hy1 : y = 1
  · subst y; exact N.one_mem
  obtain ⟨g,rfl⟩ := evenCore_conjugate x (hle hx) hne y hy hy1
  exact Subgroup.Normal.conj_mem inferInstance x hx g

def diagonal : Model := SemidirectProduct.inl (Multiplicative.ofAdd (fun _ => 1))

theorem diagonal_conjugate : ∀ g : Model, g * diagonal * g⁻¹ = diagonal := by decide +kernel

def invariantLine : Subgroup Model where
  carrier := {g | g = 1 ∨ g = diagonal}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> decide +kernel
  inv_mem' := by
    rintro x (rfl | rfl) <;> decide +kernel

instance : DecidablePred (· ∈ invariantLine) := fun g =>
  inferInstanceAs (Decidable (g = 1 ∨ g = diagonal))

instance : invariantLine.Normal where
  conj_mem := by
    rintro x (rfl | rfl) g
    · exact Or.inl (by simp)
    · exact Or.inr (diagonal_conjugate g)

theorem invariantLine_eq_zpowers : invariantLine = Subgroup.zpowers diagonal := by
  apply le_antisymm
  · rintro x (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.mpr (Or.inr rfl)

theorem invariantLine_card : Nat.card invariantLine = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem invariantLine_lt_core : invariantLine < core := by
  apply lt_of_le_of_ne
  · rintro x (rfl | rfl) <;> rfl
  · intro he
    have hh := congrArg (fun H : Subgroup Model => Nat.card H) he
    rw [invariantLine_card, core_card] at hh
    contradiction

end Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
