module
public import Theory.SpecificGroups.SymplecticFour.QuadraticFixedPlane
public import Theory.Representation.FirstCohomologyDuality.QuotientGeometry

/-!
# Fixed subgroups of large quadratic symplectic actors

A quadratic subgroup of Sp4(4) of order greater than four has the same
self-orthogonal plane as its fixed and displacement spaces. The faithful
ambient natural marking first places the actor in the symplectic component.
The embedded form then lifts every fixed vector to the actual commutator,
using the complete action kernel and the literal conjugation map.

Source: the fixed-space calculation in MS93 (5.10), printed p.922.
The original tensor application uses it on the backward critical root.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F J D : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group J] [Group D]
open scoped commutatorElement in
/-- Every fixed element of the full embedded natural module belongs to the
commutator of a quadratic actor with more than four actual images. -/
theorem large_quadratic_embedded_fixed_le_commutator
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (N A : Subgroup D) (q : D →* J) [Finite (A.map q)]
    (j : Multiplicative (Vector F) →* D) (hj : Function.Injective j) (hjr : j.range=N)
    (hact : ∀ x v, j (Multiplicative.ofAdd (ρ (q x) v)) =
      x*j (Multiplicative.ofAdd v)*x⁻¹)
    (hq : ⁅A,N⁆ ≤ centralizer (A : Set D)) (hlarge : 4 < Nat.card (A.map q)) :
    N ⊓ centralizer (A : Set D) ≤ ⁅A,N⁆ := by
  have hquad : IsQuadratic ρ (A.map q) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    apply Multiplicative.ofAdd.injective
    apply hj
    have hd : j (Multiplicative.ofAdd (ρ (q b) v-v)) = ⁅b,j (Multiplicative.ofAdd v)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    have hc := hq (commutator_mem_commutator hb (show j (Multiplicative.ofAdd v) ∈ N from hjr ▸ ⟨_,rfl⟩)) a ha
    rw [hact,hd,hc,mul_inv_cancel_right]
  have hAB := SymplecticNaturalNormalizer.le_component_of_quadratic_two_lt_card
    hF B hcent e ρ hfaith hB (A.map q) hquad (by omega)
  let E := ((A.map q).subgroupOf B).map e.toMonoidHom
  have hqE : ∀ x ∈ E, ∀ y ∈ E, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    have h := hquad x.val hx y.val hy v
    simpa only [hB,Representation.symplecticNatural_apply,smul_eq_mulVec,
      MulEquiv.coe_toMonoidHom] using h
  have hEc : Nat.card F < Nat.card E := by
    rw [hF,card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv]
    exact hlarge
  have heq : TwoLocalCover.fixedSpace E = displacementSpace E :=
    (orthogonal_displacementSpace E).symm.trans
      (large_quadratic_displacement_self_orthogonal E hqE hEc)
  let P : Submodule (ZMod 2) (Vector F) :=
    AddSubgroup.toZModSubmodule 2 ((⁅A,N⁆).comap j).toAddSubgroup'
  have hP : (displacementSpace E).restrictScalars (ZMod 2) ≤ P := by
    rw [show displacementSpace E = Coinvariants.ker ((symplecticNatural 2).comp E.subtype) from rfl,
      ←coinvariants_restrictScalars]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,v⟩,rfl⟩
    obtain ⟨b,hb,hbx⟩ := x.property
    obtain ⟨a,ha,hab⟩ := hb
    change q a = (b : J) at hab
    change j (Multiplicative.ofAdd (x.val • v-v)) ∈ ⁅A,N⁆
    rw [←hbx]
    change j (Multiplicative.ofAdd (symplecticNatural 2 (e b) v-v)) ∈ _
    rw [←hB,←hab,ofAdd_sub,map_div,div_eq_mul_inv,hact]
    exact commutator_mem_commutator ha (show j (Multiplicative.ofAdd v) ∈ N from hjr ▸ ⟨_,rfl⟩)
  rintro x ⟨hx,hc⟩
  obtain ⟨v,rfl⟩ := (show x ∈ j.range from hjr.symm ▸ hx)
  have hv : v.toAdd ∈ TwoLocalCover.fixedSpace E := by
    rintro _ ⟨b,hb,rfl⟩
    obtain ⟨a,ha,hab⟩ := hb
    change q a = (b : J) at hab
    change symplecticNatural 2 (e b) v.toAdd = v.toAdd
    rw [←hB,←hab]
    apply Multiplicative.ofAdd.injective
    apply hj
    rw [hact,ofAdd_toAdd,hc a ha,mul_inv_cancel_right]
  exact hP (heq ▸ hv)
end Theory.SpecificGroups.SymplecticFour
