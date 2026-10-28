module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne.OriginalCoverPoint
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.SourceDecomposition
public import Theory.GroupTheory.Commutator.ConjugateLines
/-!
# The two local planes in the proper cover quotient

Write N = U₀ and B = ⟨V₃^{K₂}⟩ in the five-dimensional cover branch of
13.8.33. The earlier marked local action supplies an actual r in L₂
with U₂ = B join Bʳ. When N < U_L, the previously constructed seed orbit
has image of order two modulo N. Its two conjugate images generate the
U₂-image, while U₂ = [U₂,L₂] excludes an image of order two. The second
local image therefore has order four, just like the first.

We construct conjugation on the literal U_L/N, with relative normality
and elementary abelianness. Commutator generation makes the second plane
irreducible. The marked point-parabolic dichotomy proves irreducibility
of the first plane by pulling invariant subspaces back to ambient subgroups.
Both images generate the entire quotient under LT. The covering constant
line stays in U₁ throughout; neither plane nor its dimension is assumed.

The Steinberg comparison proving U₀ = U_L, whole-module permutation
comparison, 13.4.1 application, strict denominators and terminal assembly
remain with qt-d-138-a6-endgame-source. The earlier ordinary setup remains
with qt-d-138-six-g2-source; earlier 13.5.4 and 13.7.6 inputs stay explicit.
The proper-quotient hypothesis is a branch assumption. This is not full
13.8.33 or 13.8.34.

Source: Aschbacher--Smith, 13.8.6(5) and proof of 13.8.33, printed pp.948,967,
combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
open TransvectionRecognition.Component.ModelExtension A6Endgame.IntersectionBalance
open TransvectionQuotients TransvectionQuotients.FourLocalFactors TransvectionParabolic
open TransvectionParabolic.RankDoubling
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The marked earlier action supplies the actual second conjugate, with
its original L₂ and V₂-normalizer placement. -/
theorem original_second_two_conjugates
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (earlier1354 : EarlierCore.Earlier1354 T L V) :
    ∃ r : G, r ∈ EarlierCore.localResidual L V₂ ∧ r ∈ normalizer (V₂ : Set G) ∧
      Source.U2 H V V₂ = conjugateSpanBy V₃ (Source.K2 H V₂) ⊔
        (conjugateSpanBy V₃ (Source.K2 H V₂)).map (MulAut.conj r).toMonoidHom := by
  let _ := local_elementary d
  let _ := d.abelian_span
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hHz.2.1
  let flag : Marking.StandingFlag T L V V₁ V₂ V₃ :=
    ⟨d.normalizes_L,d.normalizes_V,d.line_le_plane,d.plane_le_seed,d.seed_le,
      ⟨d.line_card,d.plane_card,d.seed_card⟩,d.line_stable,d.plane_stable,d.seed_stable⟩
  have natural : Marking.StandingNatural L V (le_sup_left.trans flag.normalizes_V) :=
    ⟨6,Or.inr rfl,d.local_quotient.toMonoidHom.comp (QuotientGroup.mk' _),
      d.local_quotient.surjective.comp (QuotientGroup.mk'_surjective _),d.coordinate,d.conjugation⟩
  let en := (flag.componentSetup (Marking.standing_natural_earlier natural) ⟨eL⟩).extend
  let ρ := tildeRepresentation H _ V₁ a
  have hρ : TransvectionRecognition.IsConjugation H V₃ V₁ ρ :=
    fun x u => congrArg Additive.ofMul (a.conjugation x u)
  let ld := SourceAssembly.localData_of_naturalSetup (H := H) en earlier1354 h.T_le_H
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) ρ hρ
  obtain ⟨lm⟩ := LocalMarking.nonempty_compatibleMarking en ld
  obtain ⟨r,hr,hgen⟩ := SourceAction.source_two_conjugates H V V₁ V₂ V₃
    (EarlierCore.localI L V₁ V₂) (EarlierCore.localResidual L V₂) ld lm
    (SourceAssembly.seed_core_commutator (H := H) en h.T_le_H)
    (SourceAssembly.flag_index_two d.plane_le_seed (by decide : (4 : ℕ) ≠ 0)
      d.plane_card d.seed_card)
  exact ⟨r,hr,ld.I2_le_G2 r.property,hgen⟩

/-- The second local subgroup has a literal four-group image modulo U₀. -/
theorem original_cover_proper_plane
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
    (hDH : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) = Source.UH H V₃)
    (hDg : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ = c.Ugamma V₃)
    (hH : H = G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (K : Subgroup G) (hK : (K.subgroupOf H).IsCComponent)
    (hprod : (H : Set G) = (K : Set G) * (T : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* Equiv.Perm (Fin 6))
    (F : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 6))
    (hF : ∀ g v, F (tildeRepresentation H _ V₁ a g v) =
      BinaryPermutation.coreRepresentation (Fin 6) (e g) (F v))
    (hp : (quotientSpace (Source.UH H V₃) V₁ V₃).map F.toLinearMap =
      Representation.SixLetterRadicalDisplacement.W)
    (earlier1354 : EarlierCore.Earlier1354 T L V)
    (earlier1376 : Marking.NaturalSection.Earlier1376 L (EarlierCore.localResidual L V₁)
      T (normalizer (V₁ : Set G)) M V₂ V₃ V₁)
    (hproper : Source.U0 L H K V₃ < Source.UL L H V₃) :
    (Source.U0 L H K V₃).relIndex (Source.U2 H V V₂) = 4 := by
  let _ := local_elementary d
  let _ := d.abelian_span
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hHz.2.1
  obtain ⟨_,_,_,_,_,hline⟩ := original_cover_proper_point d h c hDH hDg hH hHz
    K hK hprod eL a e F hF hp earlier1354 earlier1376 hproper
  obtain ⟨_,_,_,_,hgen,hcomm,_⟩ := original_cover_orbit d h c hDH hDg hHz
    K hK hprod eL a e F hF hp earlier1354 earlier1376
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  obtain ⟨r,hr,_,hsplit⟩ := original_second_two_conjugates d h hHz eL a earlier1354
  have hRU : EarlierCore.localResidual L V₂ ≤ normalizer (Source.U2 H V V₂ : Set G) := by
    rw [hgen]
    exact le_normalizer_conjugateSpanBy _ _
  have hRN : EarlierCore.localResidual L V₂ ≤ normalizer (Source.U0 L H K V₃ : Set G) :=
    ((EarlierCore.localResidual_le L V₂).trans le_sup_left).trans p.normalizes
  exact quotient_card_four_of_conjugate_lines (Source.U2 H V V₂)
    (conjugateSpanBy V₃ (Source.K2 H V₂)) (Source.U0 L H K V₃)
    (EarlierCore.localResidual L V₂) hRU hRN hcomm.symm ⟨r,hr⟩ hsplit hline

/-- The constructed action on the literal cover quotient. This records
only its maps and normalization; the local-plane assertions are proved below. -/
structure CoverQuotientAction (L H K T L₂ V V₂ V₃ : Subgroup G) where
  normal : ((Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)).Normal
  elementary : let _ := normal; IsElementaryAbelian 2 ((Source.UL L H V₃) ⧸
    (Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃))
  normalizes : L ⊔ T ≤ normalizer (Source.UL L H V₃ : Set G)
  normalizes_second : L₂ ⊔ T ≤ normalizer (Source.U2 H V V₂ : Set G)
  action : let _ := normal; let _ := elementary;
    Representation (ZMod 2) (L ⊔ T : Subgroup G)
      (Additive ((Source.UL L H V₃) ⧸ (Source.U0 L H K V₃).subgroupOf (Source.UL L H V₃)))
  conjugation : let _ := normal; let _ := elementary;
    SectionConjugationAlong (L ⊔ T) (Source.UL L H V₃)
      (Source.U0 L H K V₃) (MonoidHom.id _) normalizes action

omit [Finite G] [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem localImage_irreducible_of_intersections {A : Type*} [Group A]
    (B Z P R D : Subgroup G) [(Z.subgroupOf B).Normal]
    [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)]
    (π : P →* A) (hPB : P ≤ normalizer (B : Set G))
    (ρ : Representation (ZMod 2) A (Additive (B ⧸ Z.subgroupOf B)))
    (hρ : SectionConjugationAlong P B Z π hPB ρ)
    (hRD : R ≤ normalizer (D : Set G)) (hRP : R ≤ P) (hZB : Z ≤ B)
    (hd : Module.finrank (ZMod 2) (sectionImage B Z D) = 2)
    (hinter : ∀ W : Subgroup G, R ≤ normalizer (W : Set G) → Z ≤ W →
      D ⊓ W ≤ Z ∨ D ≤ W) :
    (localImage B Z P π hPB ρ hρ R D hRD).toRepresentation.IsIrreducible := by
  let S := localImage B Z P π hPB ρ hρ R D hRD
  let : Nontrivial S.toSubmodule := Module.nontrivial_of_finrank_pos
    (by change 0 < Module.finrank (ZMod 2) (sectionImage B Z D); rw [hd]; decide)
  refine ⟨?_⟩
  intro W
  let W' := W.toSubmodule.map S.toSubmodule.subtype
  let J := sectionPreimage B Z W'
  have hRJ : R ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    rintro r hr x ⟨u,hu,rfl⟩
    let p : P := ⟨r,hRP hr⟩
    let g : (R.subgroupOf P).map π := ⟨π p,p,hr,rfl⟩
    let v : B := ⟨r * (u : G) * r⁻¹,(mem_normalizer_iff.mp (hPB (hRP hr)) u).mp u.property⟩
    refine ⟨v,?_,rfl⟩
    change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) v) ∈ W'
    have he := hρ p u
    change ρ (π p) (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) u)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) v) at he
    rw [← he]
    obtain ⟨w,hw,hwq⟩ := hu
    change w.val = Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) u) at hwq
    rw [← hwq]
    exact ⟨S.toRepresentation g w,W.apply_mem_toSubmodule g hw,rfl⟩
  rcases hinter J hRJ (denominator_le_sectionPreimage B Z hZB W') with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    apply le_bot_iff.mp
    intro w hw
    obtain ⟨u,hu,he⟩ := w.property
    have he := congrArg Additive.ofMul he
    change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) u) = w.val at he
    have hJ : (u : G) ∈ J := (mem_sectionPreimage B Z W' u).mpr
      ⟨w,hw,he.symm⟩
    have hz : QuotientGroup.mk' (Z.subgroupOf B) u = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hbot ⟨hu,hJ⟩)
    apply Subtype.ext
    exact he.symm.trans (congrArg Additive.ofMul hz)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    obtain ⟨u,hu,he⟩ := w.property
    have he := congrArg Additive.ofMul he
    change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) u) = w.val at he
    have hw : (w : Additive (B ⧸ Z.subgroupOf B)) ∈ W' := by
      rw [← he]
      exact (mem_sectionPreimage B Z W' u).mp (htop hu)
    obtain ⟨v,hv,hvw⟩ := hw
    exact (Subtype.ext hvw : v = w) ▸ hv

namespace CoverQuotientAction
variable {L H K T L₂ V V₂ V₃ : Subgroup G}
/-- The actual second local subrepresentation. -/
@[expose] def second (s : CoverQuotientAction L H K T L₂ V V₂ V₃) :=
  let _ := s.normal
  let _ := s.elementary
  localImage (Source.UL L H V₃) (Source.U0 L H K V₃) (L ⊔ T)
    (MonoidHom.id _) s.normalizes s.action s.conjugation (L₂ ⊔ T)
    (Source.U2 H V V₂) s.normalizes_second

/-- The two image dimensions and the generating irreducible second plane. -/
@[expose] def SecondPlane (s : CoverQuotientAction L H K T L₂ V V₂ V₃) : Prop :=
  let _ := s.normal
  let _ := s.elementary
  Module.finrank (ZMod 2) (sectionImage (Source.UL L H V₃) (Source.U0 L H K V₃)
    (Source.UH H V₃)) = 2 ∧
  Module.finrank (ZMod 2) s.second.toSubmodule = 2 ∧
  s.second.toRepresentation.IsIrreducible ∧
  Submodule.span (ZMod 2) {x | ∃ g : (L ⊔ T : Subgroup G),
    ∃ v : s.second, x = s.action g v.val} = ⊤
/-- The generating first plane under the actual point parabolic. -/
@[expose] def FirstPlane (s : CoverQuotientAction L H K T L₂ V V₂ V₃) (L₁ : Subgroup G) : Prop :=
  let _ := s.normal
  let _ := s.elementary
  ∃ h₁ : L₁ ⊔ T ≤ normalizer (Source.UH H V₃ : Set G),
    let S₁ := localImage (Source.UL L H V₃) (Source.U0 L H K V₃) (L ⊔ T)
      (MonoidHom.id _) s.normalizes s.action s.conjugation (L₁ ⊔ T) (Source.UH H V₃) h₁
    Module.finrank (ZMod 2) S₁.toSubmodule = 2 ∧ S₁.toRepresentation.IsIrreducible ∧
      Submodule.span (ZMod 2) {x | ∃ g : (L ⊔ T : Subgroup G),
        ∃ v : S₁, x = s.action g v.val} = ⊤

end CoverQuotientAction

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem second_plane_of_indices
    (K L₂ : Subgroup G) [IsElementaryAbelian 2 (Source.UL L H V₃)]
    (hUL : L ⊔ (T : Subgroup G) ≤ normalizer (Source.UL L H V₃ : Set G))
    (hN : L ⊔ (T : Subgroup G) ≤ normalizer (Source.U0 L H K V₃ : Set G))
    (h₂ : L₂ ⊔ (T : Subgroup G) ≤ normalizer (Source.U2 H V V₂ : Set G))
    (hR₂ : L₂ ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))
    (hU₂ : Source.U2 H V V₂ ≤ Source.UL L H V₃)
    (hi₁ : (Source.U0 L H K V₃).relIndex (Source.UH H V₃) = 4)
    (hi₂ : (Source.U0 L H K V₃).relIndex (Source.U2 H V V₂) = 4)
    (hcommR : Source.U2 H V V₂ = ⁅Source.U2 H V V₂,L₂ ⊔ (T : Subgroup G)⁆)
    (hUspan : Source.UL L H V₃ = conjugateSpanBy (Source.U2 H V V₂) (L ⊔ (T : Subgroup G))) :
    ∃ s : CoverQuotientAction L H K (T : Subgroup G) L₂ V V₂ V₃, s.SecondPlane := by
  let P := L ⊔ (T : Subgroup G)
  let R₂ := L₂ ⊔ (T : Subgroup G)
  let U := Source.UL L H V₃
  let N := Source.U0 L H K V₃
  let hn : (N.subgroupOf U).Normal := inferInstance
  let _ := hn
  let helem : IsElementaryAbelian 2 (U ⧸ N.subgroupOf U) := inferInstance
  let _ := helem
  obtain ⟨action,haction⟩ := exists_quotient_conjugation_action P U N hUL hN hn
  let ρ : Representation (ZMod 2) P (Additive (U ⧸ N.subgroupOf U)) := {
    toFun := fun g => (MonoidHom.toAdditive (action g).toMonoidHom).toZModLinearMap 2
    map_one' := by ext x; exact DFunLike.congr_fun (action.map_one) x.toMul
    map_mul' := by intro g k; ext x; exact DFunLike.congr_fun (action.map_mul g k) x.toMul }
  have hρ : SectionConjugationAlong P U N (MonoidHom.id _) hUL ρ := by
    intro g u
    exact congrArg Additive.ofMul (haction g u)
  let S₂ := localImage U N P (MonoidHom.id _) hUL ρ hρ R₂ (Source.U2 H V V₂) h₂
  have hd₁ : Module.finrank (ZMod 2) (sectionImage U N (Source.UH H V₃)) = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact (pow_finrank_sectionImage U N (Source.UH H V₃) (le_conjugateSpanBy _ _)).trans hi₁
  have hd₂ : Module.finrank (ZMod 2) S₂.toSubmodule = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact (pow_finrank_sectionImage U N (Source.U2 H V V₂) hU₂).trans hi₂
  have hirr : S₂.toRepresentation.IsIrreducible :=
    Representation.BinaryPlaneRecognition.irreducible_of_generating_plane S₂.toRepresentation hd₂
      (localImage_coinvariants_eq_top U N P (MonoidHom.id _) hUL ρ hρ R₂
        (Source.U2 H V V₂) h₂ hR₂ hU₂ hcommR)
  let s : CoverQuotientAction L H K (T : Subgroup G) L₂ V V₂ V₃ := {
    normal := hn
    elementary := helem
    normalizes := hUL
    normalizes_second := h₂
    action := ρ
    conjugation := hρ }
  exact ⟨s,hd₁,hd₂,hirr,
    localImage_spans_of_conjugateSpan U N P (MonoidHom.id _) hUL ρ hρ
      (Source.U2 H V V₂) P R₂ h₂ le_rfl hUspan⟩

/-- Both literal local images have dimension two. The second image is
irreducible under L₂T and generates the entire proper quotient. -/
theorem full_denominators_proper_second_plane
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hproper : Source.U0 L H K V₃ < Source.UL L H V₃) :
    ∃ s : CoverQuotientAction L H K (T : Subgroup G) (EarlierCore.localResidual L V₂) V V₂ V₃,
      s.SecondPlane := by
  obtain ⟨hab,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  let _ := hab
  let _ := local_elementary d
  let _ := d.abelian_span
  let _ := SectionStructure.VH_commutative_of_global_span G₁ H V hHz.2.1
  let _ : IsMulCommutative (conjugateSpanBy (Source.UH H V₃) L) := hab
  let _ : IsElementaryAbelian 2 (Source.UL L H V₃) :=
    RankDoubling.elementary_conjugateSpan (Source.UH H V₃) L
  let P := L ⊔ (T : Subgroup G)
  let R₂ := EarlierCore.localResidual L V₂ ⊔ (T : Subgroup G)
  let U := Source.UL L H V₃
  let N := Source.U0 L H K V₃
  have hUL : P ≤ normalizer (U : Set G) :=
    SectionStructure.LT_normalizes_UL L H T V₃ h.T_le_H d.normalizes_L
  obtain ⟨_,hi₁,hspan,_,_,_⟩ := original_cover_proper_point d h c hDH hDg hH hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376 hproper
  have hi₂ := original_cover_proper_plane d h c hDH hDg hH hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376 hproper
  obtain ⟨_,_,_,_,hgen,hcomm,hU₂⟩ := original_cover_orbit d h c hDH hDg hHz K hK hprod
    eL a e F hF hp earlier1354 earlier1376
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  have hL₂ : EarlierCore.localResidual L V₂ ≤ L := EarlierCore.localResidual_le L V₂
  have hR₂ : R₂ ≤ P := sup_le_sup hL₂ le_rfl
  have hnL₂ : EarlierCore.localResidual L V₂ ≤ normalizer (Source.U2 H V V₂ : Set G) := by
    rw [hgen]
    exact le_normalizer_conjugateSpanBy _ _
  have hnT : (T : Subgroup G) ≤ normalizer (Source.U2 H V V₂ : Set G) := by
    have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := le_sup_right.trans d.normalizes_V
    have hTK : (T : Subgroup G) ≤ normalizer (Source.K2 H V₂ : Set G) :=
      SectionStructure.T_normalizes_K2 H (T : Subgroup G) V₂ h.T_le_H d.plane_stable
    exact normalizes_conjugate_span (T : Subgroup G) V (Source.K2 H V₂) hTV hTK
  have h₂ : R₂ ≤ normalizer (Source.U2 H V V₂ : Set G) := sup_le hnL₂ hnT
  have hcommR : Source.U2 H V V₂ = ⁅Source.U2 H V V₂,R₂⁆ := by
    apply le_antisymm
    · exact hcomm.le.trans (commutator_mono le_rfl (show EarlierCore.localResidual L V₂ ≤ R₂ from le_sup_left))
    · exact le_normalizer_iff_commutator_le_left.mp h₂
  have hUspan : U = conjugateSpanBy (Source.U2 H V V₂) P := by
    apply le_antisymm _ (conjugateSpanBy_le hU₂ hUL)
    apply conjugateSpanBy_le
    · rw [hspan]
      apply conjugateSpanBy_le
      · exact (conjugateSpanBy_mono d.seed_le le_rfl).trans (le_conjugateSpanBy _ _)
      · have hR₁ : sourceOne L T V₁ ⊔ (T : Subgroup G) ≤ P :=
          (original_point_parabolic_eq d hH).le.trans inf_le_left
        exact hR₁.trans (le_normalizer_conjugateSpanBy _ _)
    · exact le_sup_left.trans (le_normalizer_conjugateSpanBy _ _)
  exact second_plane_of_indices K (EarlierCore.localResidual L V₂) hUL p.normalizes h₂ hR₂ hU₂
    hi₁ hi₂ hcommR hUspan

/-- Both original parabolics act irreducibly on generating planes in the
literal proper quotient U_L/U₀. The cover and both planes are constructed. -/
theorem full_denominators_proper_local_planes
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
    (chief : ChiefGeneration.Earlier1376ChiefFactors (sourceOne L T V₁) T G₁ M V₃ V₁)
    (hproper : Source.U0 L H K V₃ < Source.UL L H V₃) :
    ∃ s : CoverQuotientAction L H K (T : Subgroup G) (EarlierCore.localResidual L V₂) V V₂ V₃,
      s.FirstPlane (sourceOne L T V₁) ∧ s.SecondPlane := by
  obtain ⟨s,hs⟩ := full_denominators_proper_second_plane d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief hproper
  let _ := s.normal
  let _ := s.elementary
  obtain ⟨_,F,hF,hp⟩ := full_denominators_abelian_cover d h c hDH hDg hH hcentral hHz
    K hK hprod eL a e model earlier1354 earlier1376 chief
  obtain ⟨hseed,_,_,_,_⟩ := original_cover_seed d h c hDH hDg hHz K hK hprod a e F hF hp
  have hpar := original_cover_star_parabolic d h c hDH hDg hH a e F hF hp
  obtain ⟨p⟩ := original_cover_permutation d h c hDH hDg hHz K hK hprod eL a e F hF hp
  let R := sourceOne L T V₁ ⊔ (T : Subgroup G)
  let P := L ⊔ (T : Subgroup G)
  let U := Source.UL L H V₃
  let N := Source.U0 L H K V₃
  have hRP : R ≤ P := (original_point_parabolic_eq d hH).le.trans inf_le_left
  have h₁ : R ≤ normalizer (Source.UH H V₃ : Set G) :=
    hHz.1.2.trans (le_normalizer_conjugateSpanBy _ _)
  have hCN : V₃ ⊔ Source.U1 H K V₃ ≤ N :=
    sup_le (d.seed_le.trans p.contains) (le_conjugateSpanBy _ _)
  have hinter : ∀ J : Subgroup G, R ≤ normalizer (J : Set G) → N ≤ J →
      Source.UH H V₃ ⊓ J ≤ N ∨ Source.UH H V₃ ≤ J := by
    intro J hRJ hNJ
    rcases cover_point_dichotomy K R J (d.line_le_plane.trans d.plane_le_seed)
      hRJ (hCN.trans hNJ) a e F hF hpar hseed hp with he | he
    · exact Or.inl (he.le.trans hCN)
    · exact Or.inr he
  have hirr := localImage_irreducible_of_intersections U N P R (Source.UH H V₃)
    (MonoidHom.id _) s.normalizes s.action s.conjugation h₁ hRP
    (Source.U0_le_UL L H K V₃) hs.1 hinter
  exact ⟨s,⟨h₁,hs.1,hirr,localImage_spans_of_conjugateSpan U N P (MonoidHom.id _)
    s.normalizes s.action s.conjugation (Source.UH H V₃) L R h₁ le_sup_left rfl⟩,hs⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CaseOne
