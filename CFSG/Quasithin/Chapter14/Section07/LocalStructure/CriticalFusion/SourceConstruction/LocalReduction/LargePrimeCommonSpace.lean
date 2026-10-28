module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.LargePrimeCriticalFactor
public import Theory.Representation.CyclicFixedRank

/-!
# The common three-space at the selected quintic endpoint

F.9.13(6) identifies the denominator commutator with the opposite point:
its codimension is one, while the selected actor moves two dimensions.
The actual rank-one reversal then places both distinct point lines in
C = [U,Uᶜ]. The literal central quotient identifies its image with the
two-dimensional displacement, so C is elementary abelian of order eight.

C is the full preimage of that plane and lies on the selected quintic
support with the entire central attachment retained. The original normal
point residual preserves the plane and hence C. At the reciprocal endpoint
we prove normalization again, then transport it to the same C using the
original residual's normality. Returning normalized labels is not used as
an unsupported assertion that I normalizes C. The point cubic's fixed-free
quotient action also identifies the exact fixed line upstairs.

LargePrimeCommonSpaceSource applies these results to the original minimal
five-core witness and its specified factor. The Sylow and A4/S4 endpoint
actions and both ambient five-core exclusions remain to be proved.
Source: Aschbacher–Smith, F.9.13(6), F.9.17 and 14.7.6, printed
pp.322–324 and1044–1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source ChapterD
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion
universe u
variable {G : Type u} [Group G] [Finite G]

private def binarySection {H U Z : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (HStar H) W}
    (s : ConjugationSection H U Z ρ) :
    BinaryConjugationSection H U Z (ρ.comp (QuotientGroup.mk' (pCore 2 H))) where
  section_le := s.le
  kernel_le := s.line_le
  normalized := s.normalizes
  coordinates := s.quotient
  onto := s.surjective
  kernel_eq := s.kernel
  equivariant x v := (s.conjugates x v).symm

omit [Finite G] in
private theorem image_commutator {H U Z : Subgroup G} {W : Type*}
    [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) (HStar H) W}
    (s : ConjugationSection H U Z ρ) (B : Subgroup G) (hB : B ≤ H) :
    s.image ⁅U,B⁆ = subspaceCommutator ρ ⊤ (actorImage H B) := by
  have ht : s.image U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u,hu⟩ := s.surjective (Multiplicative.ofAdd v)
    exact ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hh := (binarySection s).imageSpace_commutator B U hB le_rfl
  change s.image ⁅B,U⁆ = subspaceCommutator
    (ρ.comp (QuotientGroup.mk' (pCore 2 H))) (s.image U) (B.subgroupOf H) at hh
  rw [ht,subspaceCommutator_comp_map,commutator_comm] at hh
  exact hh

private theorem cyclic_moved_rank {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A : Subgroup D) (hc : Nat.card A = 2) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) = fixedCodim ρ A := by
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  rw [←ht,CyclicFixedRank.commutator_eq_range,fixedCodim_zpowers_eq_displacement_rank]

private theorem selected_displacement_two
    {D : ChapterF.Section09.Setup G} {hf : D.Hypothesis}
    [IsElementaryAbelian 2 D.UH] {a : LocalQuotientAction D.H D.UH D.V₁}
    (c : SelectedQuadraticEndpoint hf a)
    (hno : ∀ t, fixedCodim a.representation (zpowers t) ≠ 1)
    (hc : Nat.card (actorImage D.H (c.endpoint.conjugate D.UH)) = 2)
    (hr : rank (actorImage D.H (c.endpoint.conjugate D.UH)) = 1) :
    fixedCodim a.representation (actorImage D.H (c.endpoint.conjugate D.UH)) = 2 := by
  let A := actorImage D.H (c.endpoint.conjugate D.UH)
  change fixedCodim a.representation A = 2
  let : IsCyclic A := isCyclic_of_prime_card hc
  obtain ⟨t,ht⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hne : t ≠ 1 := by
    intro he
    rw [he,zpowers_one_eq_bot] at ht
    exact c.quadratic.1.1 ht.symm
  have hpos : 0 < fixedCodim a.representation A := by
    rw [←ht,fixedCodim_zpowers_eq_displacement_rank]
    by_contra hh
    have hz : a.representation t - LinearMap.id = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))
    apply hne
    apply a.faithful
    rw [map_one]
    change a.representation t = LinearMap.id
    exact sub_eq_zero.mp hz
  have hbound := c.quadratic.2.2
  change fixedCodim a.representation A ≤ 2 * rank A at hbound
  rw [hr] at hbound
  have hn := hno t
  rw [ht] at hn
  omega

/-- F.9.13(6) on this precise selected endpoint: the denominator moves the
whole opposite point, which is distinct from the original central point. -/
theorem local_selected_point_commutator
    {D : ChapterF.Section09.Setup G} (hf : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (a : LocalQuotientAction D.H D.UH D.V₁)
    (c : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (hd : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1)
    (hm : fixedCodim a.representation (actorImage D.H (c.endpoint.conjugate D.UH)) = 2) :
    ⁅commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁),c.endpoint.conjugate D.UH⁆ = c.endpoint.conjugate D.V₁ ∧
    c.endpoint.conjugate D.V₁ ≤ ⁅D.UH,c.endpoint.conjugate D.UH⁆ ∧
    D.V₁ ≠ c.endpoint.conjugate D.V₁ := by
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono hf.plus_le le_rfl
  have hBH : c.endpoint.conjugate D.UH ≤ D.H :=
    (map_mono hUV).trans (c.endpoint.large_le hb)
  have hUC : D.UH ≤ normalizer (c.endpoint.conjugate D.V₁ : Set G) := by
    have hn := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom)
      (hf.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact (hUV.trans (c.endpoint.reverse_le hb)).trans hn
  have hC : Nat.card (c.endpoint.conjugate D.V₁) = 2 :=
    (card_map_of_injective (MulAut.conj c.endpoint.representative).injective).trans hf.point_card
  have hstrict : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) <
      fixedCodim a.representation (actorImage D.H (c.endpoint.conjugate D.UH)) := by
    rw [hd,hm]
    decide
  have he := f9_denominator_commutator_eq_point s hBH hUC hC hstrict
  change ⁅commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁),c.endpoint.conjugate D.UH⁆ = c.endpoint.conjugate D.V₁ at he
  refine ⟨he,he.ge.trans (commutator_mono (commutatorPreimage_le _ _ _) le_rfl),?_⟩
  intro hsame
  have hi : s.image (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)) ≤ fixedSpace a.representation
        (actorImage D.H (c.endpoint.conjugate D.UH)) := by
    intro v hv t
    have hh := s.displacement_mem _ _ D.V₁ (by rw [commutator_comm,he,←hsame])
      t t.property v hv
    obtain ⟨x,hx,hxv⟩ := hh
    have hz := (s.quotient_eq_zero_iff x).mpr hx
    exact sub_eq_zero.mp (hxv.symm.trans hz)
  have hdim := Submodule.finrank_mono hi
  have hsum := fixedCodim_add_finrank a.representation (actorImage D.H (c.endpoint.conjugate D.UH))
  have hquot := (s.image (commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
    (c.endpoint.conjugate D.V₁))).finrank_quotient_add_finrank
  have hdq := s.quotient_finrank
    (commutatorPreimage D.UH (c.endpoint.conjugate D.UH) (c.endpoint.conjugate D.V₁))
    (s.line_le_DH _ _ hBH)
  rw [hdq,hd] at hquot
  rw [hm] at hsum
  omega


/-- Both original endpoint lines lie in the same elementary commutator of
order eight. Its literal image is the actor's two-dimensional moved space. -/
theorem local_selected_common_space
    {D : ChapterF.Section09.Setup G} (hf : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (a : LocalQuotientAction D.H D.UH D.V₁)
    (c r : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (hno : ∀ t, fixedCodim a.representation (zpowers t) ≠ 1)
    (hlabels : ∀ B : Subgroup G, D.H ≤ normalizer (B : Set G) →
      r.endpoint.conjugate (c.endpoint.conjugate B) = B)
    (hc : Nat.card (actorImage D.H (c.endpoint.conjugate D.UH)) = 2)
    (hm : fixedCodim a.representation (actorImage D.H (c.endpoint.conjugate D.UH)) = 2)
    (hd : Nat.log 2 ((commutatorPreimage D.UH (c.endpoint.conjugate D.UH)
      (c.endpoint.conjugate D.V₁)).relIndex D.UH) = 1)
    (hr : rank (actorImage D.H (r.endpoint.conjugate D.UH)) = 1)
    (hrd : Nat.log 2 ((commutatorPreimage D.UH (r.endpoint.conjugate D.UH)
      (r.endpoint.conjugate D.V₁)).relIndex D.UH) = 1) :
    let C := ⁅D.UH,c.endpoint.conjugate D.UH⁆
    let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
    D.V₁ ≤ C ∧ c.endpoint.conjugate D.V₁ ≤ C ∧
    D.V₁ ≠ c.endpoint.conjugate D.V₁ ∧ C ≤ D.UH ∧
    C ≤ c.endpoint.conjugate D.UH ∧ IsElementaryAbelian 2 C ∧ Nat.card C = 8 ∧
    s.image C = subspaceCommutator a.representation ⊤
      (actorImage D.H (c.endpoint.conjugate D.UH)) ∧
    Module.finrank (ZMod 2) (s.image C) = 2 ∧
    C = Chapter14.Section06.OddNormalizer.supportPreimage a (s.image C) := by
  let C := ⁅D.UH,c.endpoint.conjugate D.UH⁆
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  have hrc : Nat.card (actorImage D.H (r.endpoint.conjugate D.UH)) = 2 := by
    rw [r.quadratic.1.card_eq_two_pow_rank,hr]
    rfl
  have hrm := selected_displacement_two r hno hrc hr
  obtain ⟨_,hpoint,hne⟩ := local_selected_point_commutator hf a c hb hd hm
  obtain ⟨_,hrpoint,_⟩ := local_selected_point_commutator hf a r hb hrd hrm
  have hret := hlabels D.UH (le_normalizer_conjugateSpanBy D.Vplus D.H)
  have hbase : D.V₁ ≤ C := by
    apply (map_le_map_iff_of_injective (f := (MulAut.conj r.endpoint.representative).toMonoidHom)
      (MulAut.conj r.endpoint.representative).injective).mp
    change r.endpoint.conjugate D.V₁ ≤ (⁅D.UH,c.endpoint.conjugate D.UH⁆).map _
    rw [map_commutator,show (c.endpoint.conjugate D.UH).map _ = D.UH from hret,commutator_comm]
    exact hrpoint
  have hUV : D.UH ≤ D.VH := conjugateSpanBy_mono hf.plus_le le_rfl
  have hBH : c.endpoint.conjugate D.UH ≤ D.H :=
    (map_mono hUV).trans (c.endpoint.large_le hb)
  have hCU : C ≤ D.UH := le_normalizer_iff_commutator_le_left.mp (hBH.trans a.normalizes)
  have hCB : C ≤ c.endpoint.conjugate D.UH := by
    apply le_normalizer_iff_commutator_le_right.mp
    have hn := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom) a.normalizes
    rw [map_equiv_normalizer_eq] at hn
    exact (hUV.trans (c.endpoint.reverse_le hb)).trans hn
  have hCE : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCU) (inclusion_injective hCU)
  have himage := image_commutator s (c.endpoint.conjugate D.UH) hBH
  have hdim : Module.finrank (ZMod 2) (s.image C) = 2 := by
    rw [himage,cyclic_moved_rank _ _ hc,hm]
  have hidx : D.V₁.relIndex C = 4 := by
    have hh := relIndex_ker (C.subgroupOf D.UH) s.quotient
    rw [s.kernel,relIndex_subgroupOf hCU] at hh
    change D.V₁.relIndex C = Nat.card (s.image C) at hh
    rw [hh,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    rfl
  have hcard : Nat.card C = 8 := by
    have hh := (D.V₁.subgroupOf C).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hbase).toEquiv,hf.point_card] at hh
    change 2 * D.V₁.relIndex C = Nat.card C at hh
    rw [hidx] at hh
    exact hh.symm
  have hpre : C = Chapter14.Section06.OddNormalizer.supportPreimage a (s.image C) := by
    apply le_antisymm
    · intro x hx
      apply (Chapter14.Section06.OddNormalizer.mem_supportPreimage a _ ⟨x,hCU hx⟩).mpr
      exact ⟨⟨x,hCU hx⟩,hx,rfl⟩
    · intro x hx
      have hxU := Chapter14.Section06.OddNormalizer.supportPreimage_le a (s.image C) hx
      exact (s.quotient_mem_image_iff C hbase ⟨x,hxU⟩).mp
        ((Chapter14.Section06.OddNormalizer.mem_supportPreimage a _ ⟨x,hxU⟩).mp hx)
  exact ⟨hbase,hpoint,hne,hCU,hCB,hCE,hcard,himage,hdim,hpre⟩

local instance {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (I : Subgroup G) [hU : IsElementaryAbelian 2 (F.UH I)] :
    IsElementaryAbelian 2 (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).UH := hU

/-- The original cubic normalizes the common three-space through the exact
central preimage; its quotient plane lies on the selected quintic support. -/
theorem local_common_space_point_action
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (I : Subgroup G) [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c : SelectedQuadraticEndpoint hf a) (X : Subgroup (HStar I))
    (hLI : F.Li L 1 ≤ I)
    (hcentral : actorImage I (F.Li L 1) ≤
      centralizer (actorImage I (c.endpoint.conjugate (F.UH I)) : Set (HStar I)))
    (hpre : ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ =
      Chapter14.Section06.OddNormalizer.supportPreimage a
        (subspaceCommutator a.representation ⊤ (actorImage I (c.endpoint.conjugate (F.UH I)))))
    (hcompl : IsCompl
      (subspaceCommutator a.representation ⊤ ⁅X,actorImage I (c.endpoint.conjugate (F.UH I))⁆)
      (fixedSpace a.representation (⁅X,actorImage I (c.endpoint.conjugate (F.UH I))⁆ ⊔
        actorImage I (c.endpoint.conjugate (F.UH I))))) :
    F.Li L 1 ≤ normalizer ((⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) : Set G) ∧
    F.Li L 1 ≤ centralizer (F.Vi 1 : Set G) ∧
    ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ ≤
      Chapter14.Section06.OddNormalizer.supportPreimage a
        (subspaceCommutator a.representation ⊤ ⁅X,actorImage I (c.endpoint.conjugate (F.UH I))⁆) := by
  let A := actorImage I (c.endpoint.conjugate (F.UH I))
  let W := subspaceCommutator a.representation ⊤ ⁅X,A⁆
  have hstable : A ≤ subspaceStabilizer a.representation W :=
    subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial)) (normalizer_commutator_ge_right X A)
  have hmove : subspaceCommutator a.representation ⊤ A ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,v,_,rfl⟩
    have hv : v ∈ W ⊔ fixedSpace a.representation (⁅X,A⁆ ⊔ A) :=
      hcompl.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
    have htz : a.representation t z = z := hz ⟨t,mem_sup_right ht⟩
    rw [map_add,htz,add_sub_add_right_eq_sub]
    exact W.sub_mem ((hstable ht w).mpr hw) hw
  refine ⟨?_,hLI.trans hf.H_centralizes,?_⟩
  · rw [hpre]
    apply Chapter14.Section06.OddNormalizer.supportPreimage_normalized a _ _ hLI
    exact subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
      (hcentral.trans (Subgroup.centralizer_le_normalizer _))
  · rw [hpre]
    intro x hx
    have hxU := Chapter14.Section06.OddNormalizer.supportPreimage_le a _ hx
    exact (Chapter14.Section06.OddNormalizer.mem_supportPreimage a _ ⟨x,hxU⟩).mpr
      (hmove ((Chapter14.Section06.OddNormalizer.mem_supportPreimage a _ ⟨x,hxU⟩).mp hx))

private theorem point_normalizes_commutator
    {D : ChapterF.Section09.Setup G} (hf : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] (a : LocalQuotientAction D.H D.UH D.V₁)
    (i : hf.CriticalEndpoint) (hb : 3 ≤ hf.b)
    (B : Subgroup G) (hBH : B ≤ D.H)
    (hBA : actorImage D.H B ≤ centralizer (actorImage D.H (i.conjugate D.UH) : Set _))
    (hbase : D.V₁ ≤ ⁅D.UH,i.conjugate D.UH⁆) :
    B ≤ normalizer ((⁅D.UH,i.conjugate D.UH⁆ : Subgroup G) : Set G) := by
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  let C := ⁅D.UH,i.conjugate D.UH⁆
  have hAH : i.conjugate D.UH ≤ D.H :=
    (map_mono (conjugateSpanBy_mono hf.plus_le le_rfl)).trans (i.large_le hb)
  have hCU : C ≤ D.UH := le_normalizer_iff_commutator_le_left.mp (hAH.trans a.normalizes)
  have he : s.image C = subspaceCommutator a.representation ⊤ (actorImage D.H (i.conjugate D.UH)) :=
    image_commutator s _ hAH
  have hstable : actorImage D.H B ≤ subspaceStabilizer a.representation (s.image C) := by
    rw [he]
    exact subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
      (hBA.trans (Subgroup.centralizer_le_normalizer _))
  apply le_normalizer_iff.mpr
  intro b hb x hx
  let bH : D.H := ⟨b,hBH hb⟩
  let xU : D.UH := ⟨x,hCU hx⟩
  have hh := (hstable (mem_map_of_mem _ (show bH ∈ B.subgroupOf D.H from hb))
    (s.quotient xU).toAdd).mpr ((s.quotient_mem_image_iff C hbase xU).mpr hx)
  rw [s.conjugates] at hh
  exact (s.quotient_mem_image_iff C hbase _).mp hh

/-- Normalization at the reversed endpoint is transported onto the original
common commutator. The normality of the original point residual is essential. -/
theorem local_common_space_opposite_point_action
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (c r : SelectedQuadraticEndpoint hf a) (hb : 3 ≤ hf.b)
    (X : Subgroup (HStar I)) [X.Normal]
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤)
    (hlabels : ∀ B : Subgroup G, I ≤ normalizer (B : Set G) →
      r.endpoint.conjugate (c.endpoint.conjugate B) = B)
    (hopp : c.endpoint.conjugate (F.Vi 1) ≤ ⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆) :
    c.endpoint.conjugate (F.Li L 1) ≤
      normalizer ((⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆ : Subgroup G) : Set G) ∧
    c.endpoint.conjugate (F.Li L 1) ≤ centralizer (c.endpoint.conjugate (F.Vi 1) : Set G) := by
  have hU := hlabels (F.UH I) (le_normalizer_conjugateSpanBy V I)
  have hZ := hlabels (F.Vi 1) (hf.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hLI := F.Li_one_le_of_mem_Hz hI
  have hL := hlabels (F.Li L 1) ((normal_subgroupOf_iff_le_normalizer hLI).mp hn)
  have hcomm : r.endpoint.conjugate (⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆) =
      ⁅F.UH I,r.endpoint.conjugate (F.UH I)⁆ := by
    change (⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆).map _ = _
    rw [map_commutator,show (c.endpoint.conjugate (F.UH I)).map _ = F.UH I from hU,commutator_comm]
  have hbase : F.Vi 1 ≤ ⁅F.UH I,r.endpoint.conjugate (F.UH I)⁆ := by
    have hh := map_mono (f := (MulAut.conj r.endpoint.representative).toMonoidHom) hopp
    change r.endpoint.conjugate _ ≤ r.endpoint.conjugate _ at hh
    rwa [hZ,hcomm] at hh
  obtain ⟨hAP,_⟩ := local_critical_actor_control h structural previous I hI hn hf r.endpoint hb X hgen
  have hN := point_normalizes_commutator hf a r.endpoint hb (F.Li L 1)
    hLI (le_centralizer_iff.mp hAP) hbase
  constructor
  · apply (map_le_map_iff_of_injective (f := (MulAut.conj r.endpoint.representative).toMonoidHom)
      (MulAut.conj r.endpoint.representative).injective).mp
    rw [map_equiv_normalizer_eq]
    change r.endpoint.conjugate (c.endpoint.conjugate (F.Li L 1)) ≤
      normalizer (r.endpoint.conjugate (⁅F.UH I,c.endpoint.conjugate (F.UH I)⁆) : Set G)
    rw [hL,hcomm]
    exact hN
  · rintro _ ⟨x,hx,rfl⟩ _ ⟨z,hz,rfl⟩
    simpa only [map_mul,MulEquiv.coe_toMonoidHom] using
      congrArg (MulAut.conj c.endpoint.representative)
        ((hLI.trans hf.H_centralizes) hx z hz)

/-- The normal point cubic has exactly the original central line as its
fixed subgroup in every literal subspace containing that line. -/
theorem local_common_space_fixed_line
    {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (hf : (Chapter12.Section09.NaturalSource.naturalF9Setup F L I).Hypothesis)
    (C : Subgroup G) (hZC : F.Vi 1 ≤ C) (hCU : C ≤ F.UH I) :
    C ⊓ centralizer (F.Li L 1 : Set G) = F.Vi 1 := by
  let s := ModuleBound.OriginalF916.conjugationSection a hf.H_centralizes
  have hfix := local_point_fixedSpace_eq_bot h structural I hLI hn a
  apply le_antisymm
  · intro x hx
    let xU : F.UH I := ⟨x,hCU hx.1⟩
    have hv : (s.quotient xU).toAdd ∈ fixedSpace a.representation (actorImage I (F.Li L 1)) := by
      rintro ⟨_,b,hb,rfl⟩
      change a.representation (QuotientGroup.mk' (pCore 2 I) b) (s.quotient xU).toAdd = _
      rw [s.conjugates]
      apply congrArg (fun u => (s.quotient u).toAdd)
      apply Subtype.ext
      change (b : G) * x * (b : G)⁻¹ = x
      rw [hx.2 b hb,mul_inv_cancel_right]
    rw [show fixedSpace a.representation (actorImage I (F.Li L 1)) = ⊥ from hfix] at hv
    exact (s.quotient_eq_zero_iff xU).mp hv
  · exact le_inf hZC (le_centralizer_iff.mp (hLI.trans hf.H_centralizes))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
