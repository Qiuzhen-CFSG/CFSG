module

public import Theory.Representation.BinaryOffender.CubicOrbitSection

/-!
# Cubic restriction through a homogeneous orbit's central quotient

The two-subgroup centralizing the component fixes the homogeneous seed,
then its entire orbit. Consequently the original actor has the same
kernel on the orbit span and on its central quotient. The two literal
images have equal ranks. Fixed codimension decreases on quotienting,
so the restricted cubic bound passes to the original kernel quotient.
This supplies the section step needed after minimal-offender restriction,
including when the actor is not faithful on the component.

Source: Aschbacher--Smith A.1.42, D.2.7 and 5.1.23, printed
pp.32,180,645--646, refs/quasithin.pdf.
-/

open Subgroup Theory.GroupTheory Representation
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
public noncomputable section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
theorem orbitSpan_fixed_by_two_centralizer
    {K P : Subgroup G} (hP : IsPGroup 2 P)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I) :
    orbitSpan ρ P I ≤ fixedSpace ρ (P ⊓ centralizer (K : Set G)) := by
  let B := P ⊓ centralizer (K : Set G)
  have hn : P ≤ normalizer (B : Set G) :=
    (le_inf P.le_normalizer (hI.normalizes.trans (normalizer_le_normalizer_centralizer K))).trans
      inf_normalizer_le_normalizer_inf
  apply orbitSpan_le_fixedSpace_of_normalizes ρ hn
  exact IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hI.isIrrPlus
    (hP.to_le inf_le_left) inf_le_right
    ((le_inf (inf_le_left.trans le_sup_right) inf_le_right).trans (hI.centralizer_stabilizes ρ))

omit [Finite G] in
theorem orbitSection_image_rank
    {K P A : Subgroup G} (hP : IsPGroup 2 P)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I)
    [IsQuasisimple K] (hAP : A ≤ P) :
    rank ((A.subgroupOf (K ⊔ P)).map
      (KernelQuotient.projection (orbitSectionRepresentation ρ hI))) =
      rank (restrictedSubgroup ρ (orbitSpan ρ P I) A) := by
  let J := K ⊔ P
  let W := orbitSpan ρ P I
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  have hAJ : A ≤ J := hAP.trans le_sup_right
  have hAW : A ≤ subspaceStabilizer ρ W := hAP.trans (orbitSpan_invariant ρ P I)
  let f : A →* KernelQuotient.Actor σ := q.comp (inclusion hAJ)
  let r := subgroupActionHom ρ W A hAW
  have hk := centralSection_kernel_le_centralizer_of_not_fixed ρ K J le_sup_left W
    (fun hh => hI.isIrrPlus.not_le_fixedSpace ρ ((le_orbitSpan ρ P I).trans hh))
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le K.le_normalizer hI.normalizes)
  have hker : f.ker = r.ker := by
    ext a
    constructor
    · intro ha
      have hs : σ (inclusion hAJ a) = 1 := by
        have he := congrArg (KernelQuotient.action σ) ha
        simpa only [f,q,MonoidHom.comp_apply,KernelQuotient.action_projection,
          MonoidHom.map_one] using he
      have hcent : (a : G) ∈ centralizer (K : Set G) :=
        (hk (mem_map_of_mem J.subtype hs)).2
      apply subspaceImageRepresentation_injective ρ W
      ext w
      exact orbitSpan_fixed_by_two_centralizer ρ hP hI w.property ⟨a,hAP a.property,hcent⟩
    · intro ha
      apply (QuotientGroup.eq_one_iff _).mpr
      apply (actionHom_eq_one_iff σ _).mpr
      intro v
      obtain ⟨w,rfl⟩ := ((fixedSpace ρ K).comap W.subtype).mkQ_surjective v
      have hw := congrArg (fun a => subspaceImageRepresentation ρ W a w) ha
      change (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
      exact congrArg ((fixedSpace ρ K).comap W.subtype).mkQ hw
  have hrange : f.range = (A.subgroupOf J).map q := by
    ext y
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inclusion hAJ a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  have he : f.range ≃* r.range :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange r))
  unfold rank
  rw [←hrange,←subgroupActionHom_range ρ W A hAW]
  exact congrArg (Nat.log 2) (Nat.card_congr he.toEquiv)

theorem orbitSection_cubicRatio_le_restricted_actionRatio
    {K P A : Subgroup G} (hP : IsPGroup 2 P)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I)
    [IsQuasisimple K] (hAP : A ≤ P) (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hm : ¬ orbitSpan ρ P I ≤ fixedSpace ρ A) :
    cubicRatio (KernelQuotient.action (orbitSectionRepresentation ρ hI)) ≤
      actionRatio (subspaceImageRepresentation ρ (orbitSpan ρ P I))
        (restrictedSubgroup ρ (orbitSpan ρ P I) A) := by
  let J := K ⊔ P
  let W := orbitSpan ρ P I
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  let A₀ := A.subgroupOf J
  let E := A₀.map q
  have hAJ : A ≤ J := hAP.trans le_sup_right
  have hAW : A ≤ subspaceStabilizer ρ W := hAP.trans (orbitSpan_invariant ρ P I)
  have hr : rank E = rank (restrictedSubgroup ρ W A) := orbitSection_image_rank ρ hP hI hAP
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hAJ
  have hE : IsElementaryTwo E := by
    refine ⟨?_,IsElementaryAbelian.map q⟩
    intro hz
    have hp := (hA.restrictedSubgroup ρ W hAW hm).rank_pos
    have hzero : rank E = 0 := by simp [rank,hz]
    omega
  let τ := ρ.comp J.subtype
  let U := invariantSubspace ρ J W (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
  let N := centralSectionFixedSubspace ρ K J W
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le K.le_normalizer hI.normalizes)
  have hcu : IsCubic U.toRepresentation A₀ := cubic_subrepresentation τ U
    (fun a ha b hb c hc' v => hc a ha b hb c hc' v)
  have hσ : IsCubic σ A₀ := cubic_quotient U.toRepresentation N hcu
  have hce : IsCubic (KernelQuotient.action σ) E :=
    hσ.map_equivariant σ (KernelQuotient.action σ) q (LinearEquiv.refl _ _) (fun _ _ => rfl)
  have hfixed : fixedSpace U.toRepresentation A₀ =
      fixedSpace (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
    rw [fixedSpace_restrictedSubgroup ρ W A hAW]
    ext w
    constructor
    · intro hw a
      exact congrArg Subtype.val (hw ⟨⟨a,hAJ a.property⟩,a.property⟩)
    · intro hw a
      exact Subtype.ext (hw ⟨a,a.property⟩)
  have hdu : fixedCodim U.toRepresentation A₀ =
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) :=
    congrArg (fun Q => Module.finrank (ZMod 2) (W ⧸ Q)) hfixed
  have hd : fixedCodim (KernelQuotient.action σ) E ≤
      fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) := by
    have he := fixedCodim_map_equivariant σ (KernelQuotient.action σ) q
      (LinearEquiv.refl _ _) (fun _ _ => rfl) A₀
    rw [←he,←hdu]
    exact (Nat.le_add_right _ _).trans
      (fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A₀)
  apply (iInf_le_of_le E (iInf_le_of_le ⟨hE,hce⟩ le_rfl)).trans
  unfold actionRatio
  rw [hr]
  exact ENNReal.div_le_div_right (by exact_mod_cast hd) _

end Representation.BinaryOffender
