module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverPlane
public import Theory.Representation.NormalPKernelDescent

/-!
# The cover seed generates the whole original L-span

Assuming U₀ < U_L, the constructed point and line parabolics act
irreducibly on generating planes in U_L/U₀. Pass to an irreducible
quotient. The actual six-letter actor has kernel O₂(LT), which acts
trivially on that simple binary module. The simultaneous original
parabolic markings therefore recognize a Steinberg quotient.

An involution from Uγ moves at most five dimensions on U_L/U₀: mutual
normalization puts its commutator in U_L ∩ Uγ, and the common line V₁
lies in U₀. Every Steinberg involution moves at least six dimensions.
This contradiction proves U₀ = U_L, with the whole augmentation cover,
its constant line, and the original actor kernel retained.

The earlier ordinary setup and 13.5.4/13.7.6 inputs remain explicit.
The whole-module comparison, 13.4.1 application and strict-denominator
assembly are subsequent steps; this is not full 13.8.33 or 13.8.34.
Source: Aschbacher--Smith, proof of 13.8.33, printed p.967,
combined manuscript of 1 March 2004.
-/

public section
open scoped IsMulCommutative Pointwise commutatorElement
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionParabolic TransvectionQuotients BinaryAlternatingSix Theory.SpecificGroups.SymmetricSix

private theorem tensor_quotient_of_cover_planes
    {B X : Type*} [Group B] [Finite B] [AddCommGroup X] [Module (ZMod 2) X]
    [Finite X] [Nontrivial X]
    (ρ : Representation (ZMod 2) B X) (π : B →* S6)
    (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (P₁ P₂ : Subgroup B)
    (S₁ : Subrepresentation (ρ.comp P₁.subtype))
    (S₂ : Subrepresentation (ρ.comp P₂.subtype))
    [IsIrreducible S₁.toRepresentation] [IsIrreducible S₂.toRepresentation]
    (hgen₁ : Submodule.span (ZMod 2) {x | ∃ a : B, ∃ s : S₁, x = ρ a (s : X)} = ⊤)
    (hgen₂ : Submodule.span (ZMod 2) {x | ∃ a : B, ∃ s : S₂, x = ρ a (s : X)} = ⊤)
    (hdim₁ : Module.finrank (ZMod 2) S₁.toSubmodule = 2)
    (hdim₂ : Module.finrank (ZMod 2) S₂.toSubmodule = 2)
    (hP₁ : BinaryFlags.H1 ≤ P₁.map π)
    (hP₂ : BinaryFlags.H2 ≤ P₂.map π) :
    ∃ q : ρ.IntertwiningMap (tensorAction.comp π), Function.Surjective q := by
  obtain ⟨W,hW,hi⟩ := exists_irreducible_quotient ρ
  let _ := hi
  obtain ⟨τ,hτ,hτirr⟩ := exists_irreducible_descent_of_pGroup_kernel W.quotientRepresentation π hπ hker
  let _ := hτirr
  have h₁ : HasInvariantLine τ BinaryFlags.H1 := by
    refine ⟨(localQuotientMap ρ P₁ S₁ W).range.toSubmodule,
      localQuotientMap_finrank ρ P₁ S₁ hgen₁ W hW hdim₁, ?_⟩
    intro g hg v hv
    obtain ⟨b,hb,rfl⟩ := hP₁ hg
    rw [hτ]
    exact (localQuotientMap ρ P₁ S₁ W).range.apply_mem_toSubmodule ⟨b,hb⟩ hv
  have h₂ : HasInvariantLine τ BinaryFlags.H2 := by
    refine ⟨(localQuotientMap ρ P₂ S₂ W).range.toSubmodule,
      localQuotientMap_finrank ρ P₂ S₂ hgen₂ W hW hdim₂, ?_⟩
    intro g hg v hv
    obtain ⟨b,hb,rfl⟩ := hP₂ hg
    rw [hτ]
    exact (localQuotientMap ρ P₂ S₂ W).range.apply_mem_toSubmodule ⟨b,hb⟩ hv
  obtain ⟨F⟩ := tensor_of_parabolic_planes τ h₁ h₂
  let q : ρ.IntertwiningMap (tensorAction.comp π) := {
    toLinearMap := F.toLinearMap.comp W.toSubmodule.mkQ
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change F (W.toSubmodule.mkQ (ρ g v)) = tensorAction (π g) (F (W.toSubmodule.mkQ v))
      have hh := IntertwiningMap.isIntertwining _ _ F.toIntertwiningMap
        (π g) (W.toSubmodule.mkQ v)
      rw [hτ] at hh
      exact hh }
  exact ⟨q,F.toLinearEquiv.surjective.comp W.toSubmodule.mkQ_surjective⟩

open TransvectionQuotients.FourLocalFactors
open Representation.BinaryOffender.NaturalTensor

private theorem cover_section_displacement_bound {G A : Type*} [Group G] [Finite G] [Group A]
    (R Z P : Subgroup G) [(Z.subgroupOf R).Normal]
    [IsElementaryAbelian 2 (R ⧸ Z.subgroupOf R)]
    (π : P →* A) (hPR : P ≤ normalizer (R : Set G))
    (ρ : Representation (ZMod 2) A (Additive (R ⧸ Z.subgroupOf R)))
    (hρ : SectionConjugationAlong P R Z π hPR ρ)
    (p : P) :
    operatorFixedCodim (ρ (π p)) ≤
      Module.finrank (ZMod 2) (sectionImage R Z ⁅R, zpowers (p : G)⁆) := by
  apply Submodule.finrank_mono
  rintro _ ⟨x, rfl⟩
  obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf R) x.toMul
  have hx : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) r) = x := hr
  rw [← hx]
  change ρ (π p) (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) r)) -
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) r) ∈ _
  rw [hρ]
  have hc : ⁅(p : G), (r : G)⁆ ∈ ⁅R,zpowers (p : G)⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_zpowers _) r.property
  have hcR : ⁅(p : G), (r : G)⁆ ∈ R := by
    exact le_normalizer_iff_commutator_le_left.mp
      (zpowers_le.mpr (hPR p.property)) hc
  refine ⟨⟨⁅(p : G),(r : G)⁆,hcR⟩,hc,?_⟩
  change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) _) =
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf R) _ /
      QuotientGroup.mk' (Z.subgroupOf R) r)
  rw [← map_div]
  congr 2
  apply Subtype.ext
  simp only [commutatorElement_def,div_eq_mul_inv]
  rfl


open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients.FourLocalFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K L₂ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The literal cover quotient retains the ambient displacement bound. -/
theorem full_denominators_cover_displacement
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : A6Endgame.IntersectionBalance.CompatibleModel H V₃ V₁ a e)
    (hab : IsMulCommutative (Source.UL L H V₃))
    (s : CoverQuotientAction L H K (T : Subgroup G) L₂ V V₂ V₃)
    (hVN : V ≤ Source.U0 L H K V₃)
    (p : (L ⊔ (T : Subgroup G) : Subgroup G)) (hp : (p : G) ∈ c.Ugamma V₃) :
    let _ := s.normal; let _ := s.elementary;
    operatorFixedCodim (s.action p) ≤ 5 := by
  let _ := s.normal
  let _ := s.elementary
  let R := Source.UL L H V₃
  let I := R ⊓ c.Ugamma V₃
  have hline : V₁ ≤ V := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hI : V₁ ≤ I := le_inf (hline.trans (hVN.trans (Source.U0_le_UL L H K V₃)))
    (ComponentSieve.SixAndG2.Overgroup.full_denominators_commutator d h c hDH hDg).2.2
  have hcard : Nat.card (c.Ugamma V₃) ≤ 64 := by
    change Nat.card ((Source.UH H V₃).map (MulAut.conj (c.gb : G)).toMonoidHom) ≤ 64
    rw [card_map_of_injective (MulAut.conj (c.gb : G)).injective]
    exact compatible_UH_card_le_sixtyFour d a e model
  have hIcard : Nat.card I ≤ 64 := (card_le_of_le inf_le_right).trans hcard
  have hmul := relIndex_mul_card_of_le hI
  rw [d.line_card] at hmul
  have hi : V₁.relIndex I ≤ 32 := by omega
  have hvi : (Source.U0 L H K V₃).relIndex I ≤ 32 :=
    (relIndex_le_of_le_left (hline.trans hVN) index_ne_zero_of_finite).trans hi
  have hdim : Module.finrank (ZMod 2) (sectionImage R (Source.U0 L H K V₃) I) ≤ 5 := by
    rw [← pow_finrank_sectionImage R (Source.U0 L H K V₃) I inf_le_left] at hvi
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hvi
  have hcomm : ⁅R,zpowers (p : G)⁆ ≤ I :=
    (commutator_mono le_rfl (zpowers_le.mpr hp)).trans
      (full_denominators_span_quadratic d h c hH hDH hDg hcentral hab).2.2.1
  have hsub : sectionImage R (Source.U0 L H K V₃) ⁅R,zpowers (p : G)⁆ ≤ sectionImage R (Source.U0 L H K V₃) I := by
    rintro _ ⟨r,hr,rfl⟩
    exact ⟨r,hcomm hr,rfl⟩
  exact (cover_section_displacement_bound R (Source.U0 L H K V₃) (L ⊔ (T : Subgroup G))
    (MonoidHom.id _)
    s.normalizes s.action s.conjugation p).trans ((Submodule.finrank_mono hsub).trans hdim)


omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
/-- The two actual local planes construct a Steinberg quotient of U_L/U₀.
The ordinary two-core is killed on an irreducible quotient, not discarded
from the original whole module. -/
theorem original_cover_tensor_quotient
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (s : CoverQuotientAction L H K (T : Subgroup G) (EarlierCore.localResidual L V₂) V V₂ V₃)
    (h₁ : s.FirstPlane (sourceOne L T V₁)) (h₂ : s.SecondPlane) :
    let _ := s.normal; let _ := s.elementary;
    ∃ d' : LocalSetup T L V V₁ V₂ V₃ M G₁,
      ∃ q : s.action.IntertwiningMap (BinaryAlternatingSix.tensorAction.comp
        (Section07.NaturalAction.permutation (localNaturalSetup d'))), Function.Surjective q := by
  let _ := s.normal
  let _ := s.elementary
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d h c hDH hDg
  have hL₂ : EarlierCore.localResidual L V₂ = BarQuotients.sourceResidual L T V₂ :=
    (EarlierCore.residual_relative_normalizer_eq L T V₂ T.isPGroup'
      d.normalizes_L d.plane_stable).symm
  obtain ⟨d',hpar,hplane⟩ := exists_original_parabolic_coordinates d hH eb
    (EarlierCore.localResidual L V₂) hL₂
  let π := Section07.NaturalAction.permutation (localNaturalSetup d')
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨x,hx⟩ := (barMap (L ⊔ (T : Subgroup G)) V d'.normalizes_V).rangeRestrict_surjective
      ((original_bar_equiv d' eb).symm g)
    refine ⟨x,?_⟩
    rw [← original_bar_equiv_apply d' eb x,hx,MulEquiv.apply_symm_apply]
  have hk : IsPGroup 2 π.ker := by
    rw [show π.ker = pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) from
      ordinary_natural_kernel d' h eL]
    exact pCore_isPGroup
  obtain ⟨hn₁,hd₁,hirr₁,hgen₁⟩ := h₁
  let P₁ := (((sourceOne L T V₁) ⊔ (T : Subgroup G)).subgroupOf
    (L ⊔ (T : Subgroup G))).map (MonoidHom.id _)
  let P₂ := (((EarlierCore.localResidual L V₂) ⊔ (T : Subgroup G)).subgroupOf
    (L ⊔ (T : Subgroup G))).map (MonoidHom.id _)
  let S₁ := localImage (Source.UL L H V₃) (Source.U0 L H K V₃) (L ⊔ (T : Subgroup G))
    (MonoidHom.id _) s.normalizes s.action s.conjugation
    ((sourceOne L T V₁) ⊔ (T : Subgroup G)) (Source.UH H V₃) hn₁
  let : IsIrreducible S₁.toRepresentation := hirr₁
  let : IsIrreducible s.second.toRepresentation := h₂.2.2.1
  let : Nontrivial (Additive ((Source.UL L H V₃) ⧸
      (Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃))) :=
    Module.nontrivial_of_finrank_pos (lt_of_lt_of_le
      (by change 0 < Module.finrank (ZMod 2) S₁.toSubmodule; rw [hd₁]; decide)
      S₁.toSubmodule.finrank_le)
  have hp₁ : BinaryFlags.H1 ≤ P₁.map π := by
    dsimp only [P₁]
    rw [map_id,original_point_parabolic_eq d' hH]
    exact hpar.ge
  have hp₂ : BinaryFlags.H2 ≤ P₂.map π := by
    dsimp only [P₂]
    rw [map_id]
    exact hplane.ge
  obtain ⟨q,hq⟩ := tensor_quotient_of_cover_planes s.action π hπ hk P₁ P₂ S₁ s.second
    hgen₁ h₂.2.2.2 hd₁ h₂.2.1 hp₁ hp₂
  exact ⟨d',q,hq⟩

/-- The proper cover quotient is impossible by the genuine ambient
involution displacement comparison. Thus U₀ is the whole L-span. -/
theorem full_denominators_U0_eq_UL
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (model : CompatibleModel H V₃ V₁ a e)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁) :
    Source.U0 L H K V₃ = Source.UL L H V₃ := by
  by_contra hne
  have hproper := lt_of_le_of_ne (Source.U0_le_UL L H K V₃) hne
  obtain ⟨s,h₁,h₂⟩ := full_denominators_proper_local_planes d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief hproper
  let _ := s.normal
  let _ := s.elementary
  obtain ⟨d',q,hq⟩ := original_cover_tensor_quotient d h c hDH hDg hH eL s h₁ h₂
  obtain ⟨hab,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  obtain ⟨eb⟩ := exists_full_denominators_bar_equiv d' h c hDH hDg
  obtain ⟨u,hu,ho⟩ := full_denominators_bar_mover d' h c hDH hDg (original_bar_equiv d' eb)
  rw [original_bar_equiv_apply] at ho
  have hsmall := full_denominators_cover_displacement d h c hH hDH hDg hcentral
    a e model hab s p.contains u hu
  have hle := operatorFixedCodim_le_of_surjective (s.action u)
    (BinaryAlternatingSix.tensorAction (Section07.NaturalAction.permutation (localNaturalSetup d') u))
    q.toLinearMap hq (IntertwiningMap.isIntertwining _ _ q u)
  have hlo := BinaryAlternatingSix.tensor_involution_displacement_ge_six _ ho
  omega

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
