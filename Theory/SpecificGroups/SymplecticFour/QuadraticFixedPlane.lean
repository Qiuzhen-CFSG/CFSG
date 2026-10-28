module
public import Theory.SpecificGroups.SymplecticFour.QuadraticSmallMovers

/-!
# Fixed planes of large quadratic subactors in Sp₄

A quadratic actor of order larger than the field has a self-orthogonal
plane as both displacement and fixed space. For nested quadratic actors,
monotonicity of displacement and fixed spaces forces these planes to agree.
The ambient and embedded forms retain the literal representation and
conjugation map, so an actor is measured by its image, including its full
kernel.

This is the natural fixed-plane calculation used in MS93 (5.11), printed
p.924. The original-geometry application is in
Sp4Four.SourceComparison.OriginalFixedPlane; the selected-generator and
critical-commutator insertion steps are separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F] [Finite F]

/-- A subgroup larger than the field fixes the full quadratic actor's plane. -/
theorem large_quadratic_subactor_fixed_eq
    (A E : Subgroup (Sp F)) (hAE : A ≤ E)
    (hq : ∀ x ∈ E, ∀ y ∈ E, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hlarge : Nat.card F < Nat.card A) :
    TwoLocalCover.fixedSpace A = TwoLocalCover.fixedSpace E := by
  have hqA : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v :=
    fun x hx y hy v => hq x (hAE hx) y (hAE hy) v
  have hself := large_quadratic_displacement_self_orthogonal A hqA hlarge
  have hDAE : displacementSpace A ≤ displacementSpace E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp E.subtype)
      ⟨x.val,hAE x.property⟩ v
  have hDE : displacementSpace E ≤ TwoLocalCover.fixedSpace A :=
    (displacementSpace_le_fixedSpace_of_quadratic E hq).trans
      (fun v hv a ha => hv a (hAE ha))
  have heq : displacementSpace A = displacementSpace E :=
    le_antisymm hDAE (hDE.trans_eq ((orthogonal_displacementSpace A).symm.trans hself))
  rw [←orthogonal_displacementSpace,←orthogonal_displacementSpace,heq]

variable {J : Type*} [Group J] [CharP F 2] [Algebra (ZMod 2) F]
/-- The same fixed-plane equality in a faithful binary ambient marking. -/
theorem large_quadratic_ambient_subactor_fixed_eq
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (A E : Subgroup J) [Finite E] (hAE : A ≤ E)
    (hq : IsQuadratic ρ E) (hlarge : 4 < Nat.card A) :
    BinaryOffender.fixedSpace ρ A = BinaryOffender.fixedSpace ρ E := by
  have hEc : 2 < Nat.card E := lt_of_lt_of_le (by omega : 2 < Nat.card A)
    (Nat.card_le_card_of_injective (inclusion hAE) (inclusion_injective _))
  have hEB := SymplecticNaturalNormalizer.le_component_of_quadratic_two_lt_card
    hF B hcent e ρ hfaith hB E hq hEc
  have hAB := hAE.trans hEB
  let A' := (A.subgroupOf B).map e.toMonoidHom
  let E' := (E.subgroupOf B).map e.toMonoidHom
  have hA'E' : A' ≤ E' := map_mono (fun _ hx => hAE hx)
  have hqE : ∀ x ∈ E', ∀ y ∈ E', ∀ v : Vector F, x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    have h := hq x.val hx y.val hy v
    simpa only [hB,Representation.symplecticNatural_apply,smul_eq_mulVec,
      MulEquiv.coe_toMonoidHom] using h
  have hAc : Nat.card F < Nat.card A' := by
    rw [hF,card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv]
    exact hlarge
  have heq := large_quadratic_subactor_fixed_eq A' E' hA'E' hqE hAc
  ext v
  constructor
  · intro hv x
    have hv' : v ∈ TwoLocalCover.fixedSpace A' := by
      rintro _ ⟨a,ha,rfl⟩
      change symplecticNatural 2 (e a) v = v
      rw [←hB]
      exact hv ⟨a.val,ha⟩
    have hh := (heq ▸ hv') (e ⟨x.val,hEB x.property⟩)
      (mem_map_of_mem e.toMonoidHom x.property)
    change ρ x.val v = v
    rw [hB ⟨x.val,hEB x.property⟩ v]
    exact hh
  · intro hv x
    exact hv ⟨x.val,hAE x.property⟩

variable {D : Type*} [Group D]
open scoped commutatorElement in
/-- The fixed-subgroup equality through an embedded natural module and its
exact conjugation action, measured on the actor's actual quotient image. -/
theorem large_quadratic_embedded_subactor_fixed_eq
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (N A E : Subgroup D) (hAE : A ≤ E)
    (q : D →* J) [Finite (E.map q)]
    (j : Multiplicative (Vector F) →* D) (hj : Function.Injective j) (hjr : j.range=N)
    (hact : ∀ x v, j (Multiplicative.ofAdd (ρ (q x) v)) =
      x*j (Multiplicative.ofAdd v)*x⁻¹)
    (hq : ⁅E,N⁆ ≤ centralizer (E : Set D)) (hlarge : 4 < Nat.card (A.map q)) :
    N ⊓ centralizer (A : Set D) = N ⊓ centralizer (E : Set D) := by
  have hquad : IsQuadratic ρ (E.map q) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    apply Multiplicative.ofAdd.injective
    apply hj
    have hd : j (Multiplicative.ofAdd (ρ (q b) v-v)) = ⁅b,j (Multiplicative.ofAdd v)⁆ := by
      rw [ofAdd_sub,map_div,div_eq_mul_inv,hact]
      rfl
    have hc := hq (commutator_mem_commutator hb (show j (Multiplicative.ofAdd v) ∈ N from hjr ▸ ⟨_,rfl⟩)) a ha
    rw [hact,hd,hc,mul_inv_cancel_right]
  have heq := large_quadratic_ambient_subactor_fixed_eq hF B hcent e ρ hfaith hB
    (A.map q) (E.map q) (map_mono hAE) hquad hlarge
  apply le_antisymm
  · rintro n ⟨hn,hc⟩
    obtain ⟨v,rfl⟩ := (show n ∈ j.range from hjr.symm ▸ hn)
    refine ⟨hn,?_⟩
    have hv : v.toAdd ∈ BinaryOffender.fixedSpace ρ (A.map q) := by
      rintro ⟨_,⟨a,ha,rfl⟩⟩
      change ρ (q a) v.toAdd = v.toAdd
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,ofAdd_toAdd,hc a ha,mul_inv_cancel_right]
    intro x hx
    have hh := hact x v.toAdd
    have hvE := (heq ▸ hv) ⟨q x,mem_map_of_mem q hx⟩
    change ρ (q x) v.toAdd = v.toAdd at hvE
    rw [hvE,ofAdd_toAdd] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  · exact inf_le_inf_left _ (centralizer_le hAE)
end Theory.SpecificGroups.SymplecticFour
