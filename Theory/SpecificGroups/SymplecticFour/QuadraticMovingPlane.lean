module
public import Theory.SpecificGroups.SymplecticFour.QuadraticFixedPlane

/-!
# Fixed planes from strict quadratic movement

A quadratic symplectic actor has isotropic displacement of dimension at
most two. If its fixed quotient has more elements than the field, that
dimension is two. Its fixed space then agrees with that of any quadratic
overactor. The ambient and embedded versions retain the full action kernel.

This is the moving-index form of the plane calculation used to identify
neighboring seed intersections in MS93 (5.6), (5.9)--(5.11), pp.917--924.
The original application is SourceComparison.OriginalMovingPlane and
GenerationTwoSymplecticIntermediateSeeds.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F] [Finite F]

/-- A quadratic subactor moving more cosets than the field fixes the full actor's plane. -/
theorem moving_quadratic_subactor_fixed_eq
    (A E : Subgroup (Sp F)) (hAE : A ≤ E)
    (hq : ∀ x ∈ E, ∀ y ∈ E, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hmove : Nat.card F < Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace A)) :
    TwoLocalCover.fixedSpace A = TwoLocalCover.fixedSpace E := by
  have hqA : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v :=
    fun x hx y hy v => hq x (hAE hx) y (hAE hy) v
  have hle := TwoLocalCover.finrank_le_two_of_isotropic (displacementSpace A)
    (quadratic_displacement_isotropic A hqA)
  have hperp := LinearMap.BilinForm.finrank_orthogonal
    (W := displacementSpace A) TwoLocalCover.form_nondegenerate
  rw [orthogonal_displacementSpace] at hperp
  have hquot := (TwoLocalCover.fixedSpace A).finrank_quotient_add_finrank
  have hdimle := (displacementSpace A).finrank_le
  have hdim : Module.finrank F (Vector F ⧸ TwoLocalCover.fixedSpace A) =
      Module.finrank F (displacementSpace A) := by omega
  have hd : Module.finrank F (displacementSpace A) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := Vector F ⧸ TwoLocalCover.fixedSpace A),hdim] at hmove
    have hp : 0 < Nat.card F := Nat.card_pos
    by_contra hne
    have hsmall : Module.finrank F (displacementSpace A) ≤ 1 := by omega
    have hc := Nat.pow_le_pow_right hp hsmall
    rw [pow_one] at hc
    omega
  have hself : (form F).orthogonal (displacementSpace A) = displacementSpace A := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [orthogonal_displacementSpace]
      exact displacementSpace_le_fixedSpace_of_quadratic A hqA
    · rw [LinearMap.BilinForm.finrank_orthogonal TwoLocalCover.form_nondegenerate,hd]
      simp [Vector]
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
/-- Strict movement gives the same fixed-plane equality in a faithful ambient marking. -/
theorem moving_quadratic_ambient_subactor_fixed_eq
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (A E : Subgroup J) [Finite E] (hAE : A ≤ E)
    (hq : IsQuadratic ρ E) (hEc : 2 < Nat.card E)
    (hmove : 4 < Nat.card (Vector F ⧸ BinaryOffender.fixedSpace ρ A)) :
    BinaryOffender.fixedSpace ρ A = BinaryOffender.fixedSpace ρ E := by
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
  have hfix : BinaryOffender.fixedSpace ρ A =
      (TwoLocalCover.fixedSpace A').restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv
      rintro _ ⟨a,ha,rfl⟩
      change symplecticNatural 2 (e a) v = v
      rw [←hB]
      exact hv ⟨a.val,ha⟩
    · intro hv a
      have hh := hv (e ⟨a.val,hAB a.property⟩)
        (mem_map_of_mem e.toMonoidHom a.property)
      change ρ a.val v = v
      rw [hB ⟨a.val,hAB a.property⟩ v]
      exact hh
  have hAm : Nat.card F < Nat.card (Vector F ⧸ TwoLocalCover.fixedSpace A') := by
    rw [hF]
    rw [hfix,Nat.card_congr
      (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) (TwoLocalCover.fixedSpace A')).toEquiv] at hmove
    exact hmove
  have heq := moving_quadratic_subactor_fixed_eq A' E' hA'E' hqE hAm
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
exact conjugation action, using strict movement on the full embedded seed. -/
theorem moving_quadratic_embedded_subactor_fixed_eq
    (hF : Nat.card F = 4) (B : Subgroup J) [B.Normal]
    (hcent : centralizer (B : Set J) ≤ B) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) J (Vector F)) (hfaith : Function.Injective ρ)
    (hB : ∀ b : B, ∀ v, ρ (b:J) v = symplecticNatural 2 (e b) v)
    (N A E : Subgroup D) (hAE : A ≤ E)
    (q : D →* J) [Finite (E.map q)]
    (j : Multiplicative (Vector F) →* D) (hj : Function.Injective j) (hjr : j.range=N)
    (hact : ∀ x v, j (Multiplicative.ofAdd (ρ (q x) v)) =
      x*j (Multiplicative.ofAdd v)*x⁻¹)
    (hq : ⁅E,N⁆ ≤ centralizer (E : Set D)) (hlarge : 2 < Nat.card (E.map q))
    (hmove : 4 < (centralizer (A : Set D)).relIndex N) :
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
  have hi := embedded_centralizer_index ρ N A j hj hjr (q.comp A.subtype)
    (fun a v => hact a.val v)
  rw [MonoidHom.range_comp,range_subtype] at hi
  have hAm : 4 < Nat.card (Vector F ⧸ BinaryOffender.fixedSpace ρ (A.map q)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rwa [hi] at hmove
  have heq := moving_quadratic_ambient_subactor_fixed_eq hF B hcent e ρ hfaith hB
    (A.map q) (E.map q) (map_mono hAE) hquad hlarge hAm
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
