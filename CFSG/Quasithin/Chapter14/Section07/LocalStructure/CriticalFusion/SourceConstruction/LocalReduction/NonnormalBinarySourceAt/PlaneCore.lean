module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.PlaneCentralizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCentralizer
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularSectionCore
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original reciprocal-plane core identity

The actual orthogonal coordinates on U/V₁ retain the full inner component
image. The selected order-two actor has binary displacement rank two, so
its reciprocal point has a nonsingular nonzero image. Applying the literal
section normalizer bound gives a star image of order at most two for
O₂(H ∩ N_G(P)), where P = V₁ ∨ Zα.

The returning-point theorem places Uα inside O₂(Y₀). Relative normality
places O₂(Y₀) inside O₂(C_G(P)) and then O₂(H ∩ N_G(P)). Their star images
must therefore equal the actual order-two Uα image. Lifting through the
same H/O₂(H) map gives O₂(H ∩ N_G(P)) = O₂(H) ∨ Uα and
O₂(C_G(P)) = O₂(Y₀). In particular O₂(Y₀) ≤ O₂(H) ∨ Uα, the bound used in
the construction of T_Y. No splitting of the central section is used.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1057–1058,
refs/quasithin.pdf. The normalizer comparison avoids assuming that the
whole quotient point stabilizer lifts into the plane centralizer.
Construction of T_Y,Y, the weak-closure contradiction, and the later
classification remain subsequent obligations. The structural premises are
used only at the original G,T.
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
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem critical_plane_core_card_of_orthogonal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (σ : Representation (ZMod 2) (HStar F.H) W) (hf : Function.Injective σ)
    (N : Subgroup (HStar F.H)) [N.Normal] (hm : HasOrthogonalFourOrbit σ N)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2)
    (hPU : F.Vi 1 ⊔ c.Zα ≤ F.U) (hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4) :
    Nat.card (star F ((F.H ⊓ normalizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G)).pCoreIn 2)) ≤ 2 := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨E,j,hj,hE,hjn,hji⟩ := orthogonal_coordinates_with_inner σ hf N hm
  let π := j.comp (starMap F)
  have hπ (x : F.H) (w : W) : E ((σ.comp (starMap F)) x w) = π x (E w) :=
    hE _ _
  have hkernel : (σ.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change σ (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (hf (hx.trans σ.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  have hπker : π.ker = pCore 2 F.H := by
    ext x
    change j (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    rw [←j.map_one,hj.eq_iff]
    exact QuotientGroup.eq_one_iff _
  obtain ⟨f,e,he⟩ := hm
  have hno (x : F.H) : fixedCodim (σ.comp (starMap F)) (zpowers x) ≠ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact OrthogonalEight.equivariant_extension_no_transvection
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp σ.asGroupHom)
      N f e he (starMap F x)
  have hdisj := critical_points_disjoint_of_no_transvections_at h hab structural hkernel hno s c hs ha
  have hCZ : c.Zα ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_intersection_commutator_of_no_transvections_at h hab structural hkernel hno s c hs ha]
    exact commutator_mono inf_le_left le_rfl
  have hZne : s.imageSpace c.Zα ≠ ⊥ := by
    intro hz
    have hZP : c.Zα ≤ F.Vi 1 := by
      intro z hzz
      let zU : F.U := ⟨z,hPU (mem_sup_right hzz)⟩
      have hh : (s.coordinates zU).toAdd ∈ s.imageSpace c.Zα :=
        (s.mem_imageSpace_iff _ _).mpr ⟨zU,hzz,rfl⟩
      rw [hz,Submodule.mem_bot] at hh
      exact (s.coordinates_eq_one_iff zU).mp hh
    have hbot := hdisj.symm.eq_bot_of_le hZP
    have hc : Nat.card c.Zα = 2 := by
      rw [CriticalPath.Zα,conjugate,card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
      simpa using F.card 1 (by decide)
    rw [hbot,Nat.card_unique] at hc
    omega
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
  let A := star F c.Uα
  let : Nontrivial A := (nontrivial_iff_ne_bot _).mpr (c.star_ne_bot hs)
  obtain ⟨t,ht⟩ := exists_ne (1 : A)
  have ht2 : (t : HStar F.H)^2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    change t^Nat.card A = 1 at hh
    rw [show Nat.card A = 2 from ha] at hh
    exact congrArg Subtype.val hh
  have htgen : zpowers (t : HStar F.H) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card ha ht)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hAH : c.Uα ≤ F.H := (critical_le_Q_at h structural c).trans (Q_le_H F)
  have hsr : s.imageSpace ⁅F.U,c.Uα⁆ = (σ t - LinearMap.id).range := by
    rw [commutator_comm,s.imageSpace_commutator c.Uα F.U hAH le_rfl,s.imageSpace_self,
      subspaceCommutator_comp_map]
    change subspaceCommutator σ ⊤ A = _
    calc
      subspaceCommutator σ ⊤ A = subspaceCommutator σ ⊤ (zpowers (t : HStar F.H)) :=
        congrArg (subspaceCommutator σ ⊤) htgen.symm
      _ = _ := CyclicFixedRank.commutator_eq_range σ t
  have hmap : (s.imageSpace ⁅F.U,c.Uα⁆).map E.toLinearMap =
      LinearMap.range ((j t).toLinearMap - LinearMap.id) := by
    rw [hsr]
    ext w
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      refine ⟨E x,?_⟩
      change j t (E x)-E x = E (σ t x-x)
      rw [map_sub,hE]
    · rintro ⟨x,rfl⟩
      obtain ⟨y,rfl⟩ := E.surjective x
      refine ⟨σ t y-y,⟨y,rfl⟩,?_⟩
      change E (σ t y-y) = j t (E y)-E y
      rw [map_sub,hE]
  have hr : Module.finrank (ZMod 2) ((j t).toLinearMap - LinearMap.id).range = 2 := by
    rw [←hmap,E.finrank_map_eq]
    exact critical_commutator_image_rank_of_no_transvections_at h hab structural hkernel hno s c hs ha
  have hzn : (E z).det ≠ 0 := by
    intro hzdet
    apply ClassicalOrthogonal.FourPlusMatrix.Binary.low_rank_involution_singular_not_mem_displacement
      (j t) (hjn ⟨t,rfl⟩) hr.le (by rw [←map_pow,ht2,map_one])
      (E z) (fun hh => hz0 (E.injective (hh.trans E.map_zero.symm))) hzdet
    rw [←hmap]
    exact ⟨z,s.imageSpace_mono hCZ hz,rfl⟩
  let P := F.Vi 1 ⊔ c.Zα
  have hpc : Nat.card (s.imageSpace P) = 2 := by
    rw [s.imageSpace_card_eq_relIndex P hPU]
    have hh := relIndex_mul_card_of_le (show F.Vi 1 ≤ P from le_sup_left)
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hp,hfour] at hh
    omega
  have hrange : π.range = j.range := by
    change (j.comp (starMap F)).range = _
    have hs : Function.Surjective (starMap F) := QuotientGroup.mk'_surjective _
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr hs,←MonoidHom.range_eq_map]
  have hb := ClassicalOrthogonal.FourPlusMatrix.Binary.PointCore.section_normalizer_core_card
    s π E hπ (by rw [hrange]; exact hjn) (by rw [hrange]; exact hji)
    (by rw [hπker]; exact pCore_isPGroup)
    P hPU le_sup_left hpc z (s.imageSpace_mono le_sup_right hz) hz0 hzn
  have he : (normalizer (P : Set G)).subgroupOf F.H =
      (F.H ⊓ normalizer (P : Set G)).subgroupOf F.H := by
    ext x; exact ⟨fun hx => ⟨x.property,hx⟩,fun hx => hx.2⟩
  rw [he,pCoreIn_subgroupOf 2 _ F.H inf_le_left] at hb
  change Nat.card ((((F.H ⊓ normalizer (P : Set G)).pCoreIn 2).subgroupOf F.H).map
    (j.comp (starMap F))) ≤ 2 at hb
  rw [←Subgroup.map_map,card_map_of_injective hj] at hb
  exact hb

/-- The original reciprocal-plane core has exactly the selected order-two
star image. In particular it lies in Q_H Uα, as required for the source
construction of T_Y. -/
theorem local_nonnormal_component_reciprocal_plane_core_with_action_at
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
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      Y₀ ≤ normalizer (P : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (Y₀ : Set G) ∧
      Y₀.pCoreIn 2 = Y₀ ⊓ centralizer (P : Set G) ∧
      c.Uα ≤ Y₀.pCoreIn 2 ∧
      Y₀.pCoreIn 2 = (centralizer (P : Set G)).pCoreIn 2 ∧
      (F.H ⊓ normalizer (P : Set G)).pCoreIn 2 = F.H.pCoreIn 2 ⊔ c.Uα ∧
      star F (Y₀.pCoreIn 2) = star F c.Uα ∧
      (star F (F.H ⊓ normalizer (P : Set G))).pCoreIn 2 = star F c.Uα ∧
      Y₀.pCoreIn 2 ≤ F.H.pCoreIn 2 ⊔ c.Uα ∧
      (∀ g : G, conjugate (F.Vi 1) g ≤ P →
        ∃ y ∈ Y₀, conjugate F.U g = conjugate F.U y ∧
          P ≤ conjugate F.U g ∧ conjugate F.U g ≤ Y₀.pCoreIn 2) ∧
      ∃ σ : Y₀ →* MulAut P, Function.Surjective σ ∧
        (∀ (y : Y₀) (v : P), (σ y v : G) = (y : G) * v * (y : G)⁻¹) := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hreturn,hact⟩ :=
    local_nonnormal_component_returning_point_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  obtain ⟨hU,a,hm,hrest⟩ := local_nonnormal_component_whole_orthogonal_at d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let := hU
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor_at d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let := b.orbit_normal
  have hm' : HasOrthogonalFourOrbit a.representation b.orbit := horbit.symm ▸ hm
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
  let P := F.Vi 1 ⊔ c.Zα
  let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
  let M := F.H ⊓ normalizer (P : Set G)
  have hb : Nat.card (star F (M.pCoreIn 2)) ≤ 2 :=
    critical_plane_core_card_of_orthogonal h hab structural a.representation a.faithful
      b.orbit hm' s c hs hcard (hplane.trans inf_le_left) hfour
  have hCH : centralizer (P : Set G) ≤ F.H :=
    (centralizer_le (show F.Vi 1 ≤ P from le_sup_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcoreC : Y₀.pCoreIn 2 ≤ (centralizer (P : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 Y₀) (hkernel ▸ inf_le_right)
      (((Subgroup.centralizer_le_normalizer _).trans hNY).trans
        (normalizer_le_normalizer_characteristic_image Y₀ (pCore 2 Y₀)))
  have hcoreM : Y₀.pCoreIn 2 ≤ M.pCoreIn 2 :=
    hcoreC.trans (pCoreIn_mono_of_normalizes
      (le_inf hCH (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans (normalizer_le_normalizer_centralizer P)))
  have hAcore : c.Uα ≤ Y₀.pCoreIn 2 := by
    obtain ⟨y,hy,he,hP,hU⟩ := hreturn c.conjugator
      (show conjugate (F.Vi 1) c.conjugator ≤ P from le_sup_right)
    exact hU
  have hstar : star F (Y₀.pCoreIn 2) = star F c.Uα := by
    apply (eq_of_le_of_card_ge
      (map_mono (subgroupOf_mono F.H hAcore)) _).symm
    exact (card_le_of_le (map_mono (subgroupOf_mono F.H hcoreM))).trans
      (hb.trans_eq hcard.symm)
  have hstarM : star F (M.pCoreIn 2) = star F c.Uα := by
    apply (eq_of_le_of_card_ge
      (map_mono (subgroupOf_mono F.H (hAcore.trans hcoreM))) _).symm
    exact hb.trans_eq hcard.symm
  have hquotient : (star F M).pCoreIn 2 = star F c.Uα := by
    have hk : IsPGroup 2 (starMap F).ker := by
      change IsPGroup 2 (QuotientGroup.mk' (pCore 2 F.H)).ker
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have he := map_pCoreIn_of_ker_isPGroup (starMap F) hk (M.subgroupOf F.H)
    rw [pCoreIn_subgroupOf 2 M F.H inf_le_left] at he
    exact he.symm.trans hstarM
  have hboundM : M.pCoreIn 2 ≤ F.H.pCoreIn 2 ⊔ c.Uα := by
    intro x hx
    let xH : F.H := ⟨x,(pCoreIn_le 2 M hx).1⟩
    have hxm : starMap F xH ∈ star F c.Uα := by
      rw [←hstarM]
      exact mem_map_of_mem _ hx
    obtain ⟨y,hy,he⟩ := hxm
    have hq : xH*y⁻¹ ∈ pCore 2 F.H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change starMap F (xH*y⁻¹) = 1
      rw [map_mul,map_inv,←he,mul_inv_cancel]
    have hxq : x*(y:G)⁻¹ ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype hq
    have hh := (F.H.pCoreIn 2 ⊔ c.Uα).mul_mem (mem_sup_left hxq) (mem_sup_right hy)
    change x*(y:G)⁻¹*(y:G) ∈ F.H.pCoreIn 2 ⊔ c.Uα at hh
    simpa only [inv_mul_cancel_right] using hh
  have hQM : F.H.pCoreIn 2 ≤ M :=
    le_inf (pCoreIn_le 2 F.H) (le_sup_left.trans hYn)
  have hcoreEq : M.pCoreIn 2 = F.H.pCoreIn 2 ⊔ c.Uα := by
    apply le_antisymm hboundM
    refine sup_le ?_ (hAcore.trans hcoreM)
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 F.H) hQM
      (inf_le_left.trans (F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))))
  have hcentralCore : Y₀.pCoreIn 2 = (centralizer (P : Set G)).pCoreIn 2 := by
    apply le_antisymm hcoreC
    have hcM : (centralizer (P : Set G)).pCoreIn 2 ≤ M.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes
        (le_inf hCH (Subgroup.centralizer_le_normalizer _))
        (inf_le_right.trans (normalizer_le_normalizer_centralizer P))
    have hcY : (centralizer (P : Set G)).pCoreIn 2 ≤ Y₀ :=
      (hcM.trans hboundM).trans (sup_le le_sup_left (hAcore.trans (pCoreIn_le 2 Y₀)))
    rw [hkernel]
    exact le_inf hcY (pCoreIn_le 2 _)
  obtain ⟨_,σ,hσ,hconj⟩ := hact Y₀ le_rfl hYn
  exact ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hAcore,
    hcentralCore,hcoreEq,hstar,hquotient,hcoreM.trans hboundM,hreturn,σ,hσ,hconj⟩

/-- The retained reciprocal-plane core interface. The strengthened successor
also keeps the full action on the very same selected plane. -/
theorem local_nonnormal_component_reciprocal_plane_core_at
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
      Nat.card (star F c.Uα) = 2 ∧ (F.U ⊓ c.Qα).relIndex F.U = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let Y₀ := F.H.pCoreIn 2 ⊔ c.Qα
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      Y₀ ≤ normalizer (P : Set G) ∧
      normalizer (P : Set G) ≤ normalizer (Y₀ : Set G) ∧
      Y₀.pCoreIn 2 = Y₀ ⊓ centralizer (P : Set G) ∧
      c.Uα ≤ Y₀.pCoreIn 2 ∧
      Y₀.pCoreIn 2 = (centralizer (P : Set G)).pCoreIn 2 ∧
      (F.H ⊓ normalizer (P : Set G)).pCoreIn 2 = F.H.pCoreIn 2 ⊔ c.Uα ∧
      star F (Y₀.pCoreIn 2) = star F c.Uα ∧
      (star F (F.H ⊓ normalizer (P : Set G))).pCoreIn 2 = star F c.Uα ∧
      Y₀.pCoreIn 2 ≤ F.H.pCoreIn 2 ⊔ c.Uα ∧
      (∀ g : G, conjugate (F.Vi 1) g ≤ P →
        ∃ y ∈ Y₀, conjugate F.U g = conjugate F.U y ∧
          P ≤ conjugate F.U g ∧ conjugate F.U g ≤ Y₀.pCoreIn 2) := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hAcore,
    hcentralCore,hcoreEq,hstar,hquotient,hbound,hreturn,_⟩ :=
    local_nonnormal_component_reciprocal_plane_core_with_action_at d h hab structural
      previous faithful earlier I K hI hKI hK hnormal
  exact ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hkernel,hAcore,
    hcentralCore,hcoreEq,hstar,hquotient,hbound,hreturn⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
