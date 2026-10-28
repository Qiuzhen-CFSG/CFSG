module
public import Theory.GroupTheory.PResidual.ActionKernel
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Representation.FrattiniAction
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryResidualSection
public import Theory.Representation.NormalPKernelDescent
public import Theory.Representation.SL2.TwoSubgroupFixedIndex
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryGeneration
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.Representation.SU3.BinaryDegree

/-!
# Unitary displacement on a residually moved two-group

In a nontrivial binary action of SU₃(2ⁿ), n ≥ 2, an elementary actor
conjugates into the center of a root Sylow. Its involutions survive the odd
scalar kernel and lie in the actual SL₂ fixed-field block. The SL₂ bound
therefore gives fixed codimension at least n. An elementary lift through the
scalar quotient gives the projective version. Irreducible-section descent
removes normal two-kernels, and the Frattini action transfers the bound to
arbitrary finite two-groups.

Source: DGS, *Groups and Graphs* (1985), 5.7 and the end of 8.4,
printed pp.108,138. This uses only the field-order bound required by
`DGS85.CommutingNontrivial.RadiusThreeUnitary`, without an extra quadratic
hypothesis on its literal residual section.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.BinaryFixedPoints
open BenderSuzuki.MatrixGroups
open Representation.RankOne.QuadraticRecognition
open Representation.SU3.CubicDegree.InnerActors
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
open HermitianForm.BorelTorus.EvenCenterAction
open scoped IsMulCommutative MatrixGroups
namespace Representation.SU3

/-- Every nontrivial elementary actor moves at least one fixed-field degree. -/
theorem elementary_fixedCodim_lower
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup W) (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup J.specialSubgroup) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    n ≤ fixedCodim ρ A := by
  let : CharP K 2 := charTwo_of_card hK
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hK hconj
  let J₀ := standardForm J
  obtain ⟨C,hC⟩ := exists_standard_basis J (2^n) hK hfixed
  let e := specialEquiv J C hC
  let A₀ := A.map e.toMonoidHom
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A₀).exists_le_sylow
  have hAZ : A₀ ≤ sylowCenter P := by
    rw [sylowCenter,←(HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl P).1]
    rw [←omegaOneAmbient_eq_self A₀]
    exact omegaOneAmbient_mono hAP
  obtain ⟨R,hR⟩ := exists_sylowCenter_containing_central J₀ rfl hn hK hfixed
  have hcentralcard : Nat.card (central J₀ rfl) = 2^n := by
    let f := (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl).comp
      (HermitianForm.BorelTorus.EvenCenterAction.centralCoord J₀)
    have hu : Function.Injective (BenderSuzuki.External.hermitianUnipotentSU J₀ rfl) := by
      intro z w he
      apply Subtype.ext
      exact Prod.ext (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 1) he)
        (congrArg (fun x : J₀.specialSubgroup => x.val.val 0 2) he)
    have hf : Function.Injective f := hu.comp
      (HermitianForm.BorelTorus.EvenCenterAction.centralCoord_injective J₀)
    change Nat.card f.range = 2^n
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      Nat.card_congr Multiplicative.toAdd]
    exact hfixed
  have hRcard : Nat.card (sylowCenter R) = 2^n := by
    rw [sylowCenter,←(HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R).1]
    exact (HermitianForm.SylowOmega.special_sylow_omega J₀ hn hK hfixed rfl R).2.2
  have hReq : sylowCenter R = central J₀ rfl :=
    (eq_of_le_of_card_ge hR (hRcard.trans hcentralcard.symm).le).symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J₀.specialSubgroup P R
  let f := e.trans (MulAut.conj g)
  have hAf : A.map f.toMonoidHom ≤ central J₀ rfl := by
    have hz : (sylowCenter P).map (MulAut.conj g).toMonoidHom = sylowCenter R := by
      rw [sylowCenter,map_embeddedCenter _ _ (MulAut.conj g).injective]
      exact congrArg (fun T : Subgroup J₀.specialSubgroup => (center T).map T.subtype)
        (congrArg Sylow.toSubgroup hg)
    rw [show f.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,←map_map]
    exact (map_mono hAZ).trans_eq (hz.trans hReq)
  let σ := ρ.comp f.symm.toMonoidHom
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    refine ⟨f x,?_⟩
    change ρ (f.symm (f x)) ≠ 1
    simpa only [f.symm_apply_apply] using hx
  let A₁ := A.map f.toMonoidHom
  let : IsElementaryAbelian 2 A₁ := IsElementaryAbelian.map _
  have hA₁ : A₁ ≠ ⊥ := by
    change A.map f.toMonoidHom ≠ ⊥
    exact fun he => hne ((Subgroup.map_eq_bot_iff_of_injective A f.injective).mp he)
  obtain ⟨t,ht,htne⟩ := A₁.bot_or_exists_ne_one.resolve_left hA₁
  have ht2 : t^2=1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hq : 2 < 2^n := (by decide : 2<2^2).trans_le (Nat.pow_le_pow_right (by decide) hn)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective J₀.specialToProjective J₀.specialToProjective_surjective
  let : Group.IsPerfect J₀.specialSubgroup :=
    BinaryDegree.isPerfect_specialSubgroup J₀ hn hK hconj
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    BenderSuzuki.External.huppert_II_10_13 J₀ (2^n) hq hK hfixed
  have hk := BinaryDegree.ker_le_of_perfect_central_cover
    J₀.specialToProjective J₀.specialToProjective_surjective
    J₀.specialToProjective_ker_le_center σ hσ
  have htmove : σ t ≠ 1 := by
    intro hh
    have ht3 : t^3=1 := congrArg Subtype.val (J₀.specialToProjective_ker_cube ⟨t,hk hh⟩)
    have ht1 : t=1 := by simpa only [pow_succ,ht2,one_mul] using ht3
    exact htne ht1
  let j := block J₀ rfl
  have hj : Function.Injective j :=
    (J₀.specialGraphAut rfl).fixedSubgroup.subtype_injective.comp
      (J₀.specialGraphFixedEquivSL2 rfl).symm.injective
  obtain ⟨s,hs⟩ := (hAf.trans (su3_central_le_block J₀ rfl)) ht
  have hsne : s≠1 := fun hh => htne (by rw [←hs,hh,map_one])
  have hs2 : s^2=1 := by
    apply hj
    rw [map_pow,map_one]
    exact hs ▸ ht2
  have hτ : ∃ x, (σ.comp j) x ≠ 1 := ⟨s,by change σ (j s) ≠ 1; rwa [hs]⟩
  have hl := Representation.SL2.involution_fixedCodim_lower (σ.comp j) hτ
    (by omega : 1<n) (show Nat.card (fixedField J₀)=2^n from hfixed) s hsne hs2
  have hl' : n ≤ fixedCodim σ (zpowers t) := by
    rw [fixedCodim,fixedSpace_comp_map,MonoidHom.map_zpowers,hs] at hl
    exact hl
  have hfin := hl'.trans (NaturalTensor.fixedCodim_mono σ (zpowers_le.mpr ht))
  change n ≤ fixedCodim (ρ.comp f.symm.toMonoidHom) (A.map f.toMonoidHom) at hfin
  rw [fixedCodim,fixedSpace_comp_map,Subgroup.map_map] at hfin
  have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    exact f.symm_apply_apply x
  rw [he,Subgroup.map_id] at hfin
  exact hfin

/-- The same bound for the projective carrier, lifting through its odd scalar kernel. -/
theorem projective_elementary_fixedCodim_lower
    {K W : Type*} [Field K] [Finite K] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) W)
    (hnt : ∃ g, ρ g ≠ 1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    n ≤ fixedCodim ρ A := by
  let σ := ρ.comp J.specialToProjective
  have hσ : ∃ x, σ x ≠ 1 := by
    obtain ⟨x,hx⟩ := hnt
    obtain ⟨y,rfl⟩ := J.specialToProjective_surjective x
    exact ⟨y,hx⟩
  obtain ⟨D,hD,hDA,_⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    J.specialToProjective J.specialToProjective_surjective
    (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker) A
  let : IsElementaryAbelian 2 D := hD
  have hDne : D ≠ ⊥ := by
    intro hh
    apply hne
    rw [hh,Subgroup.map_bot] at hDA
    exact hDA.symm
  have hb := elementary_fixedCodim_lower J hn hK hconj σ hσ D hDne
  change n ≤ fixedCodim (ρ.comp J.specialToProjective) D at hb
  rw [fixedCodim,fixedSpace_comp_map,hDA] at hb
  exact hb

variable {U D M : Type*} [Group U] [Group D] [Finite D]
  [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

/-- The field-degree displacement bound survives a normal two-kernel; residual
movement supplies a nontrivial irreducible quotient action. -/
theorem extension_fixedCodim_lower {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : Nonempty (U ≃* J.specialSubgroup) ∨
      Nonempty (U ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (π : D →* U) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (ρ : Representation (ZMod 2) D M)
    (hmove : fixedSpace ρ (pResidual 2 D) ≠ ⊤)
    (A : Subgroup D) [IsElementaryAbelian 2 A] (hne : A.map π ≠ ⊥) :
    n ≤ fixedCodim ρ A := by
  have hnot : ¬ pResidual 2 D ≤ ρ.ker := by
    intro hh
    apply hmove
    apply top_unique
    intro v _ a
    exact DFunLike.congr_fun (hh a.property) v
  obtain ⟨B,N,hi,hmoving⟩ := exists_irreducible_section_surviving_twoPerfect
    (pResidual 2 D) (isPPerfect_pResidual 2) hnot
  let := hi
  obtain ⟨τ,hτ,_⟩ := exists_irreducible_descent_of_pGroup_kernel
    N.quotientRepresentation π hπ hk
  have hτnt : ∃ g, τ g ≠ 1 := by
    by_contra! hh
    apply hmoving
    intro a ha
    rw [MonoidHom.mem_ker,←hτ a,hh]
  let : Finite (B.toSubmodule ⧸ N.toSubmodule) :=
    Finite.of_surjective N.toSubmodule.mkQ (Submodule.mkQ_surjective _)
  let A₀ := A.map π
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.map _
  have hl : n ≤ fixedCodim τ A₀ := by
    rcases e with he | he
    all_goals
      obtain ⟨f⟩ := he
      let σ := τ.comp f.symm.toMonoidHom
      have hσ : ∃ x, σ x ≠ 1 := by
        obtain ⟨x,hx⟩ := hτnt
        refine ⟨f x,?_⟩
        change τ (f.symm (f x)) ≠ 1
        simpa only [f.symm_apply_apply] using hx
      let A₁ := A₀.map f.toMonoidHom
      let : IsElementaryAbelian 2 A₁ := IsElementaryAbelian.map _
      have hA₁ : A₁ ≠ ⊥ := by
        change A₀.map f.toMonoidHom ≠ ⊥
        exact fun he => hne ((Subgroup.map_eq_bot_iff_of_injective A₀ f.injective).mp he)
    · have hl := elementary_fixedCodim_lower J hn hK hconj σ hσ A₁ hA₁
      change n ≤ fixedCodim (τ.comp f.symm.toMonoidHom) (A₀.map f.toMonoidHom) at hl
      rw [fixedCodim,fixedSpace_comp_map,Subgroup.map_map] at hl
      have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        exact f.symm_apply_apply x
      rw [he,Subgroup.map_id] at hl
      exact hl
    · have hl := projective_elementary_fixedCodim_lower J hn hK hconj σ hσ A₁ hA₁
      change n ≤ fixedCodim (τ.comp f.symm.toMonoidHom) (A₀.map f.toMonoidHom) at hl
      rw [fixedCodim,fixedSpace_comp_map,Subgroup.map_map] at hl
      have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
        apply MonoidHom.ext
        intro x
        exact f.symm_apply_apply x
      rw [he,Subgroup.map_id] at hl
      exact hl
  have he : τ.comp π = N.quotientRepresentation := MonoidHom.ext hτ
  have hcod : fixedCodim τ (A.map π) = fixedCodim N.quotientRepresentation A := by
    rw [←he,fixedCodim,fixedCodim,fixedSpace_comp_map]
  have hq := fixedCodim_quotient_add_subrepresentation_le B.toRepresentation N A
  have hu := fixedCodim_subrepresentation_le ρ B A
  change n ≤ fixedCodim τ (A.map π) at hl
  rw [hcod] at hl
  omega

variable {X : Type*} [Group X] [Finite X]

/-- An escaping elementary subgroup has fixed index at least the unitary
fixed-field order on every residually moved finite two-group. -/
theorem twoGroup_fixedIndex_lower_of_residual_moves {K : Type*} [Field K] [Finite K]
    (J : HermitianForm 3 K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : Nonempty (U ≃* J.specialSubgroup) ∨
      Nonempty (U ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (π : D →* U) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker)
    (hp : IsPGroup 2 X) (α : D →* MulAut X)
    (hr : ¬ pResidual 2 D ≤ α.ker)
    (A : Subgroup D) [IsElementaryAbelian 2 A] (hne : A.map π ≠ ⊥) :
    let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
    2^n ≤ (FixedPoints.subgroup A X).index := by
  let _ := MulDistribMulAction.compHom X (α.comp A.subtype)
  let : Fact (IsPGroup 2 X) := ⟨hp⟩
  let Y := X ⧸ frattini X
  let : IsElementaryAbelian 2 Y := isElementaryAbelian_quotient_frattini
  let β := (quotientAut (frattini X)).comp α
  let ρ := Representation.FrattiniAction.ofAutomorphismHom β
  have hβ := MonoidHom.residual_not_le_frattini_action_kernel hp α hr
  have hmove : fixedSpace ρ (pResidual 2 D) ≠ ⊤ := by
    intro he
    apply hβ
    intro r hr
    apply MulEquiv.ext
    intro x
    have hx : Additive.ofMul x ∈ fixedSpace ρ (pResidual 2 D) := he ▸ Submodule.mem_top
    exact congrArg Additive.toMul (hx ⟨r,hr⟩)
  have hl := extension_fixedCodim_lower J hn hK hconj e π hπ hk ρ hmove A hne
  let τ := ρ.comp A.subtype
  let := action τ
  let f : X →* Multiplicative (Additive Y) := {
    toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini X) x))
    map_one' := (QuotientGroup.mk' (frattini X)).map_one
    map_mul' := (QuotientGroup.mk' (frattini X)).map_mul }
  have heq (a : A) (x : X) : f (a • x) = a • f x := by
    change QuotientGroup.mk' (frattini X) (α a.val x) =
      quotientAut (frattini X) (α a.val) (QuotientGroup.mk' (frattini X) x)
    rw [quotientAut_apply_mk]
  have hi : fixedIndex τ ≤ (FixedPoints.subgroup A X).index :=
    fixedPoints_index_le_of_surjective_equivariant f
      (QuotientGroup.mk'_surjective (frattini X)) heq
  rw [Representation.FrattiniAction.fixedIndex_eq_two_pow_fixedCodim ρ A] at hi
  exact (Nat.pow_le_pow_right (by decide) hl).trans hi

end Representation.SU3
