module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.NonSubnormal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryNonSubnormal
public import Theory.GroupTheory.PResidual.PlaneCentralizer

/-!
# The original reciprocal-plane centralizer residual

For the same selected critical path used by the weak-closure construction,
the actual reciprocal plane P gives the intrinsic point-core pair Y₀.
Its full normalizer normalizes Y₀. Hence C_{L₁}(P) normalizes both Y₀ and
the normal span R, and therefore Y = Y₀R. Its commutators with Y lie in
C_Y(P) = O₂(Y) ≤ R. Since R normalizes C_{L₁}(P), the two-group kernel
argument proves that Y normalizes the literal L_Y = O²(C_{L₁}(P)).

The application retains the same Y, I₀ and reduced point span, together
with the nontrivial, non-subnormal image of L₁ on that span. All plane
normalization and two-core premises are discharged from the original
exchanged-component hypotheses. The further equality L₁ = L_Y O₂(L₁),
exclusion of Y₀ ≤ M, and Thompson/cubic contradiction remain unproved.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. Earlier source inputs retain their existing interfaces;
the guarded same-G,T specialization and all later obligations through
14.7.52 remain with the original local assembly.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The full normalizer of the actual reciprocal plane normalizes its
point-core pair, for any selected critical path in the original exchanged branch. -/
theorem local_nonnormal_component_selected_plane_normalizers_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (hE : IsElementaryAbelian 2 (F.Vi 1 ⊔ c.Zα : Subgroup G))
    (hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4) :
    (F.H.pCoreIn 2 ⊔ c.Qα : Subgroup G) ≤
        normalizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) ∧
      normalizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) ≤
        normalizer ((F.H.pCoreIn 2 ⊔ c.Qα : Subgroup G) : Set G) := by
  obtain ⟨hU,a,hm,_⟩ := local_nonnormal_component_whole_orthogonal_at d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let := hU
  let s₀ := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s₀.le
    kernel_le := s₀.line_le
    normalized := s₀.normalizes
    coordinates := s₀.quotient
    onto := s₀.surjective
    kernel_eq := s₀.kernel
    equivariant := fun x v => (s₀.conjugates x v).symm }
  let := local_nonnormal_component_section_irreducible_at d h hab structural previous
    faithful earlier I K hI hKI hK hnormal s
  have hk : (a.representation.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change a.representation (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (a.faithful (hx.trans a.representation.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  have hnormalOrbit : (Chapter13.Section08.Source.starImage F.H
      (conjugateSpanBy K (T : Subgroup G))).Normal := by
    obtain ⟨t,ht,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
      local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
        I K hI hKI hK hnormal
    rw [←horbit]
    exact b.orbit_normal
  let := hnormalOrbit
  obtain ⟨f,e,he⟩ := hm
  have hn (x : F.H) : fixedCodim (a.representation.comp (starMap F)) (zpowers x) ≠ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact OrthogonalEight.equivariant_extension_no_transvection
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp
        a.representation.asGroupHom) _ f e he (starMap F x)
  have hcross := critical_cross_core_commutator_of_irreducible_at h hab structural hk hn s c hs ha
  have hreverse := critical_reverse_cross_core_commutator_of_irreducible_at h hab structural hk hn s c hs ha
  have hdisj := critical_points_disjoint_of_no_transvections_at h hab structural hk hn s c hs ha
  let := hE
  obtain ⟨v₁,v₂,hpair,hcore₁,hcore₂⟩ :=
    critical_fourGroupCorePair c hcross hreverse hdisj hfour
  have hy : FourGroupCorePair.generated v₁ v₂ = F.H.pCoreIn 2 ⊔ c.Qα := by
    simp only [FourGroupCorePair.generated,hcore₁,hcore₂]
  exact ⟨hy ▸ hpair.generated_le_normalizer,hy ▸ hpair.normalizer_le_normalizer_generated⟩


/-- The actual plane centralizer residual is normalized by the constructed Y.
The hypotheses on the selected path and Y are supplied together by the
original weak-closure construction below. -/
theorem local_nonnormal_component_plane_residual_normalized_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (hE : IsElementaryAbelian 2 (F.Vi 1 ⊔ c.Zα : Subgroup G))
    (hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4)
    (hR : c.Uα ≤ F.Ri L 1) :
    let P := F.Vi 1 ⊔ c.Zα
    let J := F.Li L 1 ⊔ (T : Subgroup G)
    let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
    let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
    R ≤ normalizer (P : Set G) → Chapter1.IsSylowIn 2 R Y →
      Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 →
      Y ≤ normalizer ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
        (F.Li L 1 ⊓ centralizer (P : Set G)).subtype : Set G) := by
  dsimp only
  intro hRN hSylow hkernel
  let P := F.Vi 1 ⊔ c.Zα
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let Y := Y₀ ⊔ R
  obtain ⟨hYP,hNY⟩ := local_nonnormal_component_selected_plane_normalizers_at
    d h hab structural previous faithful earlier I K hI hKI hK hnormal c hs ha hE hfour
  obtain ⟨_,hRT,hJR⟩ := critical_plane_normal_span c hR
  have hRY : Y.pCoreIn 2 ≤ R := by
    obtain ⟨S,hS⟩ := hSylow
    exact (pCoreIn_le_sylow Y S).trans_eq hS
  have hCP : F.Li L 1 ⊓ centralizer (P : Set G) ≤ normalizer (P : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hCY : F.Li L 1 ⊓ centralizer (P : Set G) ≤ normalizer (Y : Set G) :=
    (le_inf (hCP.trans hNY) (inf_le_left.trans (le_sup_left.trans hJR))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact normalizes_plane_centralizer_residual (F.Li L 1) P Y R hCY
    (sup_le hYP hRN) hkernel hRY
    (hRT.trans (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural))) hRN

/-- The original weak-closure construction, now with its actual plane
centralizer residual normalized by Y. No additional normalization premise
remains in this original-local application. -/
theorem local_nonnormal_component_weakClosure_residual_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let J := F.Li L 1 ⊔ (T : Subgroup G)
      let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
      let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
      let I₀ := J ⊔ Y
      let W₀ := ChapterE.indexedWeakClosure V R 0
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      R ≤ (T : Subgroup G) ∧ J ≤ normalizer (R : Set G) ∧
      R ≤ normalizer (P : Set G) ∧ Chapter1.IsSylowIn 2 R Y ∧
      Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
      Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
      V ≤ W₀ ∧ W₀ ≤ R ∧ I₀ ≤ normalizer (W₀ : Set G) ∧
      IsTwoLocal (normalizer (W₀ : Set G)) ∧ normalizer (W₀ : Set G) ≠ ⊤ ∧
      I₀ = J ⊔ c.Qα ∧ HasCharacteristicTwo I₀ ∧
      IsSQTK KnownSimple.IsKnownSimple I₀ ∧
      IsPReduced 2 ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀) ∧
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ ∧
      letI : ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀).Normal :=
        normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk'
        (centralizer ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀))
      ¬ (((F.Li L 1).subgroupOf I₀).map q).IsSubnormal ∧
        ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) ∧
        Y ≤ normalizer ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype : Set G) := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hsub,hne,hYn⟩ :=
    local_nonnormal_component_weakClosure_non_subnormal_at d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  have hres := local_nonnormal_component_plane_residual_normalized_at d h hab structural
    previous faithful earlier I K hI hKI hK hnormal c hs ha hE hfour hR hRN hSylow hcore
  exact ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hsub,hne,hYn,hres⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
