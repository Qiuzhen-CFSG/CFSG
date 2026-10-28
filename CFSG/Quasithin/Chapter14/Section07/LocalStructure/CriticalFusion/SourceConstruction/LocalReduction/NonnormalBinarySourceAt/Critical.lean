module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.Orthogonal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryCritical
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Offender
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Selection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.CriticalActors
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryOrthogonal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CriticalOffender
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.OrthogonalEight.ActualConsequences
public import Theory.Representation.OrthogonalFourPlusMatrix.NormalizerNonFF
public import Theory.Representation.OrthogonalFourPlusMatrix.QuadraticNormalizerRank
public import Theory.Representation.OrthogonalFourPlusMatrix.QuadraticCommonLine

/-!
# Critical actor geometry on the exchanged orthogonal section

The original exchanged component identifies the entire literal section with
the binary determinant module. This construction transports the selected
critical path into the actual full normalizer, excludes transvections by the
marked exchanged component, and proves the actor is a nontrivial quadratic
subgroup. The common displacement line on the literal reciprocal subspace
excludes rank three. The per-element displacement bound and factor permutation
then exclude rank two. Thus the actual actor and reciprocal quotient both have
order two, and the common fixed codimension is exactly two.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1057–1058,
refs/quasithin.pdf. The subsequent reciprocal-plane construction and
14.7.31 weak-closure contradiction remain separate source steps.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.BinaryOffender.NaturalTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components

private theorem orthogonal_coordinates {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (hf : Function.Injective σ)
    (N : Subgroup D) [N.Normal] (hm : HasOrthogonalFourOrbit σ N) :
    ∃ (E : W ≃ₗ[ZMod 2] ClassicalOrthogonal.FourPlusMatrix.Binary.V)
      (j : D →* linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action),
      Function.Injective j ∧ ∀ g v, E (σ g v) =
        normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action (j g) (E v) := by
  obtain ⟨f,e,he⟩ := hm
  let a := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  have hE (g : N) (v : W) : E (σ g v) =
      ClassicalOrthogonal.FourPlusMatrix.Binary.action (a g) (E v) := by
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates (e (σ g v)) = _
    rw [he,OrthogonalEight.binaryCoordinates_equivariant]
    rfl
  let γ : Representation (ZMod 2) D ClassicalOrthogonal.FourPlusMatrix.Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp σ
  have he' (g : D) (v : W) : E (σ g v) = γ g (E v) := by
    change E (σ g v) = E (σ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hres (g : N) : γ g = ClassicalOrthogonal.FourPlusMatrix.Binary.action (a g) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [←he']
    exact hE g w
  have him : N.map γ.asGroupHom = actionImage ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
    ext z
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨a ⟨g,hg⟩,Units.ext (hres ⟨g,hg⟩).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := a.surjective g
      exact ⟨g,g.property,Units.ext (hres g)⟩
  have hn (g : D) : γ.asGroupHom g ∈ linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
    change γ.asGroupHom g ∈ normalizer (actionImage ClassicalOrthogonal.FourPlusMatrix.Binary.action : Set _)
    rw [←him]
    exact N.le_normalizer_map γ.asGroupHom (mem_map_of_mem _
      (show g ∈ normalizer (N : Set D) from le_normalizer_of_normal (mem_top g)))
  let j := γ.asGroupHom.codRestrict _ hn
  refine ⟨E,j,?_,he'⟩
  intro x y heq
  exact hf (E.conjRingEquiv.injective (congrArg (fun z : linearNormalizer
    ClassicalOrthogonal.FourPlusMatrix.Binary.action => z.val.val) heq))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem critical_star_nontrivial_of_no_transvections
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (σ : Representation (ZMod 2) (HStar F.H) W) (hf : Function.Injective σ)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (hno : ∀ x : F.H, fixedCodim (σ.comp (starMap F)) (zpowers x) ≠ 1)
    (c : CriticalPath (L := L) F) : star F c.Uα ≠ ⊥ := by
  intro hz
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  have hcomm : ⁅F.U,c.Uα⁆ ≤ F.Vi 1 := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha v hv
    have he : starMap F (⟨a,hAH ha⟩ : F.H) = 1 := by
      have hh := mem_map_of_mem (starMap F) (show (⟨a,hAH ha⟩ : F.H) ∈
        c.Uα.subgroupOf F.H from ha)
      change starMap F ⟨a,hAH ha⟩ ∈ star F c.Uα at hh
      simpa only [hz,mem_bot] using hh
    apply (s.action_mem_ker_iff ⟨a,hAH ha⟩).mp _ v hv
    change σ (starMap F ⟨a,hAH ha⟩) = 1
    rw [he,map_one]
  obtain ⟨g,hUg,hHg,hAR⟩ := exists_terminal_edge_transport_at h structural c
  let f := (MulAut.conj g).toMonoidHom
  let A := F.U.map f
  let C := (F.Vi 1).map f
  have hc : ⁅A,F.U⁆ ≤ C := by
    have hm := map_mono (f := f) hcomm
    change c.Uα.map f = F.U at hUg
    rwa [map_commutator,hUg] at hm
  have hC : Nat.card C = 2 := by
    rw [card_map_of_injective (MulAut.conj g).injective]
    simpa using F.card 1 (by decide)
  have hA : A ≤ F.H := hAR.trans ((pCoreIn_le 2 _).trans
    (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hzero := s.commutator_le_kernel_of_card_two_of_no_transvections hno A C hA hC hc
  have hAQ : A ≤ F.H.pCoreIn 2 := by
    intro a ha
    have hk := (s.action_mem_ker_iff ⟨a,hA ha⟩).mpr
      (fun v hv => hzero (commutator_mem_commutator ha hv))
    have he : starMap F (⟨a,hA ha⟩ : F.H) = 1 := hf (hk.trans σ.map_one.symm)
    exact mem_map_of_mem F.H.subtype
      ((QuotientGroup.eq_one_iff _).mp he)
  have hQmap : c.Qα.map f = F.H.pCoreIn 2 := by
    change ((conjugate F.H c.conjugator).pCoreIn 2).map f = _
    rw [map_pCoreIn_of_injective 2 _ f (MulAut.conj g).injective,hHg]
  apply critical_span_not_le_reciprocal_core c
  exact (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    (hAQ.trans_eq hQmap.symm)

private theorem binary_line_image_dim
    {ρ : Representation (ZMod 2) F.H W}
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (ρ : Representation (ZMod 2) F.H W))
    (C : Subgroup G) (hC : Nat.card C = 2) :
    Module.finrank (ZMod 2) (s.imageSpace C) ≤ 1 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hDcard : Nat.card (s.imageSpace C) ≤ 2 := by
    change Nat.card ((C.subgroupOf F.U).map s.coordinates) ≤ 2
    have hm := Nat.card_le_card_of_surjective (s.coordinates.subgroupMap
      (C.subgroupOf F.U)) (s.coordinates.subgroupMap_surjective _)
    have hs : Nat.card (C.subgroupOf F.U) ≤ Nat.card C :=
      Nat.card_le_card_of_injective (fun y => (⟨y.val,y.property⟩ : C))
        (by
          intro a b he
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : C => (z:G)) he)
    exact hm.trans (hs.trans hC.le)
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod] at hDcard
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2)
    (show 2 ≤ Module.finrank (ZMod 2) (s.imageSpace C) by omega)
  omega

private theorem critical_common_center_space
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (ρ : Representation (ZMod 2) F.H W)
    (hkernel : ρ.ker = pCore 2 F.H)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (hσ : σ.comp (starMap F) = ρ)
    (c : CriticalPath (L := L) F) :
    let B := star F c.Uα
    ∃ P : Subrepresentation (σ.comp B.subtype),
      ∃ Z : Submodule (ZMod 2) W,
        Module.finrank (ZMod 2) Z ≤ 1 ∧
        Module.finrank (ZMod 2) (W ⧸ P.toSubmodule) =
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ∧
        ∀ b v, v ∈ P.toSubmodule → (σ.comp B.subtype) b v - v ∈ Z := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let := IsElementaryAbelian.subgroupOf (p:=2) hAH
  let B := star F c.Uα
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (starMap F)
  let τ := σ.comp B.subtype
  let D := F.U ⊓ c.Qα
  have hDH : c.Uα ≤ conjugate F.H c.conjugator := map_mono F.U_le_H
  have hDn : c.Uα ≤ normalizer (D:Set G) := by
    apply (le_inf (hAH.trans s.normalized) _).trans inf_normalizer_le_normalizer_inf
    exact hDH.trans ((conjugate F.H c.conjugator).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (conjugate F.H c.conjugator))))
  let P : Subrepresentation τ := {
    toSubmodule := s.imageSpace D
    apply_mem_toSubmodule := by
      rintro ⟨b,hb⟩ v hv
      obtain ⟨a,ha,rfl⟩ := hb
      obtain ⟨u,hu,rfl⟩ := (s.mem_imageSpace_iff D v).mp hv
      have he : τ ⟨starMap F a,mem_map_of_mem _ ha⟩ = ρ a :=
        congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
      rw [he]
      refine (s.mem_imageSpace_iff D _).mpr ⟨⟨a*u*(a:G)⁻¹,
        (mem_normalizer_iff.mp (s.normalized a.property) u).mp u.property⟩,
        (mem_normalizer_iff.mp (hDn ha) u).mp hu,s.equivariant a u⟩ }
  have hline : Module.finrank (ZMod 2) (s.imageSpace c.Zα) ≤ 1 := by
    apply binary_line_image_dim s c.Zα
    rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hc : ⁅c.Uα,D⁆ ≤ c.Zα := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_right le_rfl).trans
      (reciprocal_core_commutator_le_point h s c)
  have hdisp : ∀ b v, v ∈ P.toSubmodule → τ b v-v ∈ s.imageSpace c.Zα := by
    rintro ⟨b,hb⟩ v hv
    obtain ⟨a,ha,rfl⟩ := hb
    obtain ⟨u,hu,rfl⟩ := (s.mem_imageSpace_iff D v).mp hv
    have he : τ ⟨starMap F a,mem_map_of_mem _ ha⟩ = ρ a :=
      congrArg (fun k : Representation (ZMod 2) F.H W => k a) hσ
    rw [he]
    let z : F.U := (⟨a*u*(a:G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized a.property) u).mp u.property⟩ : F.U)*u⁻¹
    refine (s.mem_imageSpace_iff c.Zα _).mpr ⟨z,
      hc (commutator_mem_commutator ha hu),?_⟩
    rw [map_mul,map_inv]
    change (s.coordinates ⟨a*u*(a:G)⁻¹,_⟩).toAdd + -(s.coordinates u).toAdd = _
    rw [s.equivariant,sub_eq_add_neg]
  have hPD : F.Vi 1 ≤ D := le_inf
    ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
    (point_le_reciprocal_core_of_kernel_at h structural hkernel s c)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient (D.subgroupOf F.U) |>.exists_card_eq
  have hindex : D.relIndex F.U = 2^n := hn
  have hdim := s.imageSpace_codimension_of_index D inf_le_left hPD n hindex
  have hquot := (s.imageSpace D).finrank_quotient_add_finrank
  have hcodim : Module.finrank (ZMod 2) (W ⧸ P.toSubmodule) = Nat.log 2 (D.relIndex F.U) := by
    rw [hindex,Nat.log_pow Nat.one_lt_two]
    change Module.finrank (ZMod 2) (W ⧸ s.imageSpace D) = n
    omega
  exact ⟨P,s.imageSpace c.Zα,hline,hcodim,hdisp⟩


/-- In the original exchanged branch the selected critical actor and the
literal reciprocal quotient both have order two. Their action is on the
whole orthogonal section, with fixed codimension exactly two. -/
theorem local_nonnormal_component_selected_critical_rank_one_at
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
        ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
          c.Uα ≤ F.Ri L 1 ∧ F.Vi 1 ≤ c.Qα ∧
          IsElementaryTwo (star F c.Uα) ∧
          IsQuadratic a.representation (star F c.Uα) ∧
          rank (star F c.Uα) = 1 ∧
          Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) = 1 ∧
          fixedCodim a.representation (star F c.Uα) = 2 ∧
          Nat.card (star F c.Uα) = 2 ∧
          (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
          rank (star F c.Uα) < fixedCodim a.representation (star F c.Uα) ∧
          fixedCodim a.representation (star F c.Uα) ≤
            rank (star F c.Uα) + Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ∧
          (∀ x : HStar F.H, fixedCodim a.representation (zpowers x) ≠ 1) ∧
          ∀ x ∈ star F c.Uα,
            Module.finrank (ZMod 2) (a.representation x - LinearMap.id).range ≤
              Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
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
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,e,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := e.orbit_normal
  have hm' : HasOrthogonalFourOrbit a.representation e.orbit := horbit.symm ▸ hm
  obtain ⟨E,j,hj,hE⟩ := orthogonal_coordinates a.representation a.faithful e.orbit hm'
  have hno (x : HStar F.H) : fixedCodim a.representation (zpowers x) ≠ 1 := by
    rw [fixedCodim_map_equivariant a.representation _ j E hE,
      MonoidHom.map_zpowers,fixedCodim_zpowers_eq_displacement_rank]
    exact ClassicalOrthogonal.FourPlusMatrix.Binary.normalizer_no_transvection
      (LinearMap.GeneralLinearGroup.toLinearEquiv (j x).val)
      (ClassicalOrthogonal.FourPlusMatrix.Binary.normalizer_linearEquiv_mem (j x))
  have hno' (x : F.H) : fixedCodim (a.representation.comp (starMap F)) (zpowers x) ≠ 1 := by
    change Module.finrank (ZMod 2) (_ ⧸ fixedSpace (a.representation.comp (starMap F)) _) ≠ 1
    rw [fixedSpace_comp_map,MonoidHom.map_zpowers]
    exact hno (starMap F x)
  have hkernel : (a.representation.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change a.representation (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (a.faithful (hx.trans a.representation.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  obtain ⟨c₀⟩ := exists_criticalPath_at h hab (h.flag_escape_at F previous) structural
  obtain ⟨c,hs⟩ := select_critical_orientation_of_nontrivial_star_at h structural c₀
    (critical_star_nontrivial_of_no_transvections h structural a.representation a.faithful s hno' c₀)
  have hne := critical_star_nontrivial_of_no_transvections h structural
    a.representation a.faithful s hno' c
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  let : IsElementaryAbelian 2 c.Uα :=
    IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (c.Uα.subgroupOf F.H) := IsElementaryAbelian.subgroupOf hAH
  have hA : IsElementaryTwo (star F c.Uα) := ⟨hne,IsElementaryAbelian.map (starMap F)⟩
  have hquad : IsQuadratic a.representation (star F c.Uα) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    exact critical_quadratic h hab s c x hx y hy v
  let B := (star F c.Uα).map j
  have hB : IsElementaryTwo B := by
    let := hA.2
    refine ⟨?_,IsElementaryAbelian.map j⟩
    intro hb
    exact hA.1 (map_injective hj (hb.trans (map_bot j).symm))
  have hqB : IsQuadratic (normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action) B := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
    obtain ⟨w,rfl⟩ := E.surjective v
    have hh := congrArg E (hquad x hx y hy w)
    simpa only [map_sub,hE] using hh
  have hrB : rank B = rank (star F c.Uα) := rank_map_injective j hj _
  have hcB : fixedCodim a.representation (star F c.Uα) =
      fixedCodim (normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action) B :=
    fixedCodim_map_equivariant _ _ j E hE _
  have hsmall := ClassicalOrthogonal.FourPlusMatrix.Binary.quadratic_normalizer_rank_le_three B hB hqB
  have hlower := ClassicalOrthogonal.FourPlusMatrix.Binary.normalizer_rank_lt_fixedCodim B hB
  rw [hrB] at hsmall hlower
  rw [←hcB] at hlower
  obtain ⟨hbound,hdisp⟩ := critical_fixedCodim_bounds_of_kernel_at h hab structural hkernel s c
  have hcod : fixedCodim (a.representation.comp (starMap F)) (c.Uα.subgroupOf F.H) =
      fixedCodim a.representation (star F c.Uα) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
    rfl
  rw [hcod] at hbound
  obtain ⟨P,Z,hZ,hPD,hdispP⟩ := critical_common_center_space h hab structural
    (a.representation.comp (starMap F)) hkernel s a.representation rfl c
  let Dm := P.toSubmodule.map E.toLinearMap
  let Zm := Z.map E.toLinearMap
  have hDm : B ≤ subspaceStabilizer
      (normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action) Dm := by
    apply le_subspaceStabilizer
    rintro _ ⟨b,hb,rfl⟩ _ ⟨v,hv,rfl⟩
    exact ⟨a.representation b v,P.apply_mem_toSubmodule ⟨b,hb⟩ hv,hE b v⟩
  have hdimD : Module.finrank (ZMod 2) (ClassicalOrthogonal.FourPlusMatrix.Binary.V ⧸ Dm) =
      Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) := by
    have hm := E.finrank_map_eq P.toSubmodule
    have hq := Dm.finrank_quotient_add_finrank
    have hp := P.toSubmodule.finrank_quotient_add_finrank
    have he := E.finrank_eq
    change Module.finrank (ZMod 2) Dm = _ at hm
    omega
  have hdimZ : Module.finrank (ZMod 2) Zm ≤ 1 := by
    exact (E.finrank_map_eq Z).le.trans hZ
  have hmove : ∀ b ∈ B, ∀ v ∈ Dm,
      normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action b v - v ∈ Zm := by
    rintro _ ⟨b,hb,rfl⟩ _ ⟨v,hv,rfl⟩
    refine ⟨a.representation b v - v,hdispP ⟨b,hb⟩ v hv,?_⟩
    change E (a.representation b v - v) = _
    rw [map_sub,hE]
    rfl
  have hsmallD : Module.finrank (ZMod 2) (ClassicalOrthogonal.FourPlusMatrix.Binary.V ⧸ Dm) ≤ 3 := by
    rw [hdimD]
    exact hs.comparison.trans hsmall
  have hnot := ClassicalOrthogonal.FourPlusMatrix.Binary.rank_ne_three_of_common_line
    B hB hqB Dm Zm hDm hsmallD hdimZ hmove
  rw [hrB] at hnot
  have hrankTwo : rank (star F c.Uα) ≤ 2 := by omega
  have hall : ∀ t ∈ B, operatorFixedCodim t.val.val ≤ 3 := by
    rintro _ ⟨b,hb,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hb
    have hd := hdisp x hx
    have hidx : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ≤ 2 :=
      hs.comparison.trans hrankTwo
    have he := fixedCodim_map_equivariant a.representation
      (normalizerRepresentation ClassicalOrthogonal.FourPlusMatrix.Binary.action)
      j E hE (zpowers (starMap F x))
    rw [MonoidHom.map_zpowers,fixedCodim_zpowers_eq_displacement_rank,
      fixedCodim_zpowers_eq_displacement_rank] at he
    change Module.finrank (ZMod 2) (a.representation (starMap F x) - LinearMap.id).range = _ at he
    change operatorFixedCodim (j (starMap F x)).val.val ≤ 3
    change Module.finrank (ZMod 2) (a.representation (starMap F x) - LinearMap.id).range ≤ _ at hd
    change Module.finrank (ZMod 2) (a.representation (starMap F x) - LinearMap.id).range =
      operatorFixedCodim (j (starMap F x)).val.val at he
    omega
  have hrankOne := ClassicalOrthogonal.FourPlusMatrix.Binary.rank_le_one_of_all_displacements_le_three
    B hB hall
  rw [hrB] at hrankOne
  have hrankEq : rank (star F c.Uα) = 1 := by have hp := hA.rank_pos; omega
  have hindexEq : Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) = 1 := by
    have hp := hs.positive
    have hc := hs.comparison
    change _ ≤ rank (star F c.Uα) at hc
    omega
  have hcodimEq : fixedCodim a.representation (star F c.Uα) = 2 := by
    change fixedCodim a.representation (star F c.Uα) ≤ rank (star F c.Uα) + _ at hbound
    omega
  have hactorCard : Nat.card (star F c.Uα) = 2 := by
    rw [hA.card_eq_two_pow_rank,hrankEq,pow_one]
  have hindexCard : (F.U ⊓ c.Qα).relIndex F.U = 2 := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 F.U).to_quotient
      ((F.U ⊓ c.Qα).subgroupOf F.U) |>.exists_card_eq
    have hn' : (F.U ⊓ c.Qα).relIndex F.U = 2^n := hn
    have hnOne := hindexEq
    rw [hn',Nat.log_pow Nat.one_lt_two] at hnOne
    rw [hn',hnOne,pow_one]
  refine ⟨hU,a,hm,c,hs,critical_le_Ri_at h structural c,
    point_le_reciprocal_core_of_kernel_at h structural hkernel s c,hA,hquad,
    hrankEq,hindexEq,hcodimEq,hactorCard,hindexCard,hlower,hbound,hno,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact hdisp x hx

/-- The original exchanged branch has a selected critical path on the whole
literal orthogonal section. Its actual star actor has rank at most three;
the common-center estimate retains the exact reciprocal index. -/
theorem local_nonnormal_component_selected_critical_at
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
        ∃ c : CriticalPath (L := L) F, c.RankSelection ∧
          c.Uα ≤ F.Ri L 1 ∧ F.Vi 1 ≤ c.Qα ∧
          IsElementaryTwo (star F c.Uα) ∧
          IsQuadratic a.representation (star F c.Uα) ∧
          rank (star F c.Uα) ≤ 3 ∧
          rank (star F c.Uα) < fixedCodim a.representation (star F c.Uα) ∧
          fixedCodim a.representation (star F c.Uα) ≤
            rank (star F c.Uα) + Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) ∧
          (∀ x : HStar F.H, fixedCodim a.representation (zpowers x) ≠ 1) ∧
          ∀ x ∈ star F c.Uα,
            Module.finrank (ZMod 2) (a.representation x - LinearMap.id).range ≤
              Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) + 1 := by
  obtain ⟨hU,a,hm,c,hs,hR,hV,hA,hq,hr,hi,hc,hcard,hindex,hl,hb,hn,hd⟩ :=
    local_nonnormal_component_selected_critical_rank_one_at d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  exact ⟨hU,a,hm,c,hs,hR,hV,hA,hq,by omega,hl,hb,hn,hd⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
