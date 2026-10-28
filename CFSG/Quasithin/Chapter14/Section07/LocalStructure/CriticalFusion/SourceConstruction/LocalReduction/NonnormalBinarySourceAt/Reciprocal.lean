module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Critical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryReciprocal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryCritical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NormalPointRankOne
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual reciprocal plane in the exchanged orthogonal branch

The two-dimensional displacement and index-two reciprocal intersection force
its commutator to be the reciprocal central point. Reverse the same critical
path to obtain the original point as the opposite commutator. These distinct
points lie in the elementary full commutator of order eight, and their join
is the actual order-four plane used in the source weak-closure construction.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1057–1058,
refs/quasithin.pdf. This supplies the plane, not the subsequent construction
of Y and its Sylow subgroup or the final contradiction.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) F.H W}

/-- Every nontrivial selected actor has displacement exactly two on the literal section. -/
theorem critical_displacement_two_of_no_transvections_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (a : F.H) (haA : (a : G) ∈ c.Uα) (haQ : a ∉ pCore 2 F.H) :
    Module.finrank (ZMod 2) (ρ a - LinearMap.id).range = 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk := hkernel
  have hb := (critical_fixedCodim_bounds_of_kernel_at h hab structural hk s c).2 a haA
  rw [selected_critical_indices_of_card_two h hab c hs ha] at hb
  norm_num at hb
  have hne : Module.finrank (ZMod 2) (ρ a - LinearMap.id).range ≠ 0 := by
    intro hz
    have he : ρ a = 1 := sub_eq_zero.mp
      (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    exact haQ (hk ▸ (show a ∈ ρ.ker from he))
  have hone := hno a
  rw [fixedCodim_zpowers_eq_displacement_rank] at hone
  omega

/-- The reciprocal core intersection has commutator exactly the reciprocal point. -/
theorem critical_intersection_commutator_of_no_transvections_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hk := hkernel
  have hle : ⁅F.U ⊓ c.Qα,c.Uα⁆ ≤ c.Zα :=
    (commutator_mono inf_le_right le_rfl).trans (reciprocal_core_commutator_le_point h s c)
  have hcard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply eq_of_le_of_card_ge hle
  rw [hcard]
  apply (one_lt_card_iff_ne_bot _).mpr
  intro hz
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hdim := critical_displacement_two_of_no_transvections_at h hab structural hkernel hno s c hs ha a haA haQ
  have hfix : s.imageSpace (F.U ⊓ c.Qα) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
    intro v hv
    apply sub_eq_zero.mpr
    exact s.fixed_on_imageSpace_of_commutator_le c.Uα (F.U ⊓ c.Qα)
      (by rw [commutator_comm,hz]; exact bot_le) a haA v hv
  have hpoint : F.Vi 1 ≤ F.U ⊓ c.Qα :=
    le_inf ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
      (point_le_reciprocal_core_of_kernel_at h structural hk s c)
  have hc := s.imageSpace_codimension_of_index (F.U ⊓ c.Qα) inf_le_left hpoint 1
    (by simpa using selected_critical_indices_of_card_two h hab c hs ha)
  have hb := Submodule.finrank_mono hfix
  have hr := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
  omega


/-- Reversing the selected pair recovers the original point as a commutator. -/
theorem critical_reverse_intersection_commutator_of_no_transvections_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 := by
  have hAH := (critical_le_Q_at h structural c).trans (Q_le_H F)
  obtain ⟨r⟩ := exists_reversal_of_star_ne_bot_at h structural c hAH (c.star_ne_bot hs)
  have hrCard : Nat.card (star F r.path.Uα) = 2 := by
    rw [r.reverse_star_of_placement ((critical_le_Q_at h structural r.path).trans (Q_le_H F))]
    exact selected_critical_indices_of_card_two h hab c hs ha
  have hrSel : r.path.RankSelection :=
    ⟨critical_index_positive r.path,by
      rw [r.reverse_index_of_placement hAH,ha,hrCard]⟩
  have he := congrArg (fun B : Subgroup G => conjugate B r.conjugator)
    (critical_intersection_commutator_of_no_transvections_at h hab structural hkernel hno s r.path hrSel hrCard)
  have hm (A B : Subgroup G) : conjugate ⁅A,B⁆ r.conjugator =
      ⁅conjugate A r.conjugator,conjugate B r.conjugator⁆ := map_commutator _ _ _
  rw [hm,conjugate_inf,r.base_U,r.tip_core,r.tip_U,r.tip_point] at he
  exact he

/-- The full critical commutator has image of dimension two in the original section. -/
theorem critical_commutator_image_rank_of_no_transvections_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,c.Uα⁆) = 2 := by
  have hAH := (critical_le_Q_at h structural c).trans (Q_le_H F)
  obtain ⟨σ,hσ⟩ := exists_star_representation h s
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨x,hx⟩ := exists_ne (1 : A)
  obtain ⟨a,haA,he⟩ := x.property
  have haQ : a ∉ pCore 2 F.H := by
    intro hq
    apply hx
    apply Subtype.ext
    rw [←he]
    exact (QuotientGroup.eq_one_iff _).mpr hq
  have hz : zpowers (x : HStar F.H) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card ha hx)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have ht : s.imageSpace F.U = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨y,hy⟩ := s.onto (Multiplicative.ofAdd v)
    exact (s.mem_imageSpace_iff _ _).mpr ⟨y,y.property,congrArg Multiplicative.toAdd hy⟩
  rw [commutator_comm,s.imageSpace_commutator c.Uα F.U hAH le_rfl,ht,←hσ,
    subspaceCommutator_comp_map]
  change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ A) = 2
  rw [←hz,CyclicFixedRank.commutator_eq_range,←he]
  change Module.finrank (ZMod 2) (σ.comp (starMap F) a - LinearMap.id).range = 2
  rw [hσ]
  exact critical_displacement_two_of_no_transvections_at h hab structural hkernel hno s c hs ha a haA haQ

/-- The full critical commutator has order eight, including the original point. -/
theorem critical_commutator_card_of_no_transvections_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) :
    Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hpoint : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_reverse_intersection_commutator_of_no_transvections_at h hab structural hkernel hno s c hs ha,
      commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have hCU : ⁅F.U,c.Uα⁆ ≤ F.U := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans s.normalized)
  have he := s.imageSpace_card_eq_relIndex ⁅F.U,c.Uα⁆ hCU
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    critical_commutator_image_rank_of_no_transvections_at h hab structural hkernel hno s c hs ha] at he
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (F.Vi 1) ⁅F.U,c.Uα⁆ bot_le hpoint
  rw [relIndex_bot_left,relIndex_bot_left,←he] at hc
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  norm_num [hp] at hc
  exact hc.symm


/-- The original and reciprocal points are distinct and have trivial intersection. -/
theorem critical_points_disjoint_of_no_transvections_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hkernel : ρ.ker = pCore 2 F.H)
    (hno : ∀ a : F.H, fixedCodim ρ (zpowers a) ≠ 1)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) : Disjoint (F.Vi 1) c.Zα := by
  have hnle : ¬ c.Zα ≤ F.Vi 1 := by
    intro hle
    let A := star F c.Uα
    let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
    obtain ⟨x,hx⟩ := exists_ne (1 : A)
    obtain ⟨a,haA,he⟩ := x.property
    have haQ : a ∉ pCore 2 F.H := by
      intro hq
      apply hx
      apply Subtype.ext
      rw [←he]
      exact (QuotientGroup.eq_one_iff _).mpr hq
    have hd := critical_displacement_two_of_no_transvections_at h hab structural hkernel hno s c hs ha a haA haQ
    let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
      (Multiplicative.toAdd.surjective.comp s.onto)
    have hfix : s.imageSpace (F.U ⊓ c.Qα) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
      intro v hv
      apply sub_eq_zero.mpr
      exact s.fixed_on_imageSpace_of_commutator_le c.Uα (F.U ⊓ c.Qα)
        (by rw [commutator_comm,critical_intersection_commutator_of_no_transvections_at h hab structural hkernel hno s c hs ha]; exact hle)
        a haA v hv
    have hpoint : F.Vi 1 ≤ F.U ⊓ c.Qα := le_inf s.kernel_le
      (point_le_reciprocal_core_of_kernel_at h structural
        (hkernel) s c)
    have hc := s.imageSpace_codimension_of_index (F.U ⊓ c.Qα) inf_le_left hpoint 1
      (by simpa using selected_critical_indices_of_card_two h hab c hs ha)
    have hb := Submodule.finrank_mono hfix
    have hr := LinearMap.finrank_range_add_finrank_ker (ρ a - LinearMap.id)
    omega
  have hzCard : Nat.card c.Zα = 2 := by
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  apply disjoint_iff.mpr
  by_contra hb
  have hlo := (one_lt_card_iff_ne_bot _).mpr hb
  have he : F.Vi 1 ⊓ c.Zα = c.Zα := eq_of_le_of_card_ge inf_le_right (by omega)
  exact hnle (he ▸ (inf_le_left : F.Vi 1 ⊓ c.Zα ≤ F.Vi 1))



open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components

/-- The original exchanged component supplies the actual reciprocal plane,
with both points, both core-intersection commutators and the full moved
order-eight subgroup. No local point-containment premise is assumed. -/
theorem local_nonnormal_component_reciprocal_plane_at
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
    ∃ hU : IsElementaryAbelian 2 F.U,
      letI := hU
      ∃ a : LocalQuotientAction F.H F.U (F.Vi 1),
        HasOrthogonalFourOrbit a.representation
          (Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))) ∧
        ∃ s : BinaryConjugationSection F.H F.U (F.Vi 1)
            (a.representation.comp (starMap F)),
        ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
          Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
          fixedCodim a.representation (star F c.Uα) = 2 ∧
          ⁅F.U ⊓ c.Qα,c.Uα⁆ = c.Zα ∧
          ⁅c.Uα ⊓ F.H.pCoreIn 2,F.U⁆ = F.Vi 1 ∧
          Disjoint (F.Vi 1) c.Zα ∧
          (F.Vi 1 ⊔ c.Zα : Subgroup G) ≤ ⁅F.U,c.Uα⁆ ∧
          ⁅F.U,c.Uα⁆ ≤ F.U ⊓ c.Uα ∧
          IsElementaryAbelian 2 (F.Vi 1 ⊔ c.Zα : Subgroup G) ∧
          Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4 ∧
          Nat.card (⁅F.U,c.Uα⁆ : Subgroup G) = 8 ∧
          Module.finrank (ZMod 2) (s.imageSpace ⁅F.U,c.Uα⁆) = 2 := by
  obtain ⟨hU,a,hm,c,hs,hR,hV,hA,hquad,hr,hi,hcod,hcard,hindex,hl,hb,hno,hd⟩ :=
    local_nonnormal_component_selected_critical_rank_one_at d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
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
  have hk : (a.representation.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change a.representation (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (a.faithful (hx.trans a.representation.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  have hn (x : F.H) : fixedCodim (a.representation.comp (starMap F)) (zpowers x) ≠ 1 := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (a.representation.comp (starMap F)) _) ≠ 1
    rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
    exact hno (starMap F x)
  have he := critical_intersection_commutator_of_no_transvections_at h hab structural hk hn s c hs hcard
  have her := critical_reverse_intersection_commutator_of_no_transvections_at h hab structural hk hn s c hs hcard
  have hz := critical_points_disjoint_of_no_transvections_at h hab structural hk hn s c hs hcard
  have hP : F.Vi 1 ≤ ⁅F.U,c.Uα⁆ := by
    rw [←her,commutator_comm]
    exact commutator_mono le_rfl inf_le_left
  have hZ : c.Zα ≤ ⁅F.U,c.Uα⁆ := by
    rw [←he]
    exact commutator_mono inf_le_left le_rfl
  have hCU : ⁅F.U,c.Uα⁆ ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    (((critical_le_Q_at h structural c).trans (Q_le_H F)).trans s.normalized)
  have hCA : ⁅F.U,c.Uα⁆ ≤ c.Uα :=
    le_normalizer_iff_commutator_le_right.mp (G2Source.normalizes_partner h c)
  have hplane := sup_le hP hZ
  have hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((hZ.trans hCU).trans s.section_le) hz]
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hzc : Nat.card c.Zα = 2 := by
      rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
      exact hp
    rw [hp,hzc]
  exact ⟨hU,a,hm,s,c,hs,hR,hcard,hindex,hcod,he,her,hz,hplane,le_inf hCU hCA,
    IsElementaryAbelian.of_injective (inclusion (hplane.trans hCU)) (inclusion_injective _),
    hfour,critical_commutator_card_of_no_transvections_at h hab structural hk hn s c hs hcard,
    critical_commutator_image_rank_of_no_transvections_at h hab structural hk hn s c hs hcard⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
