module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPointCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneLocal
public import Theory.GroupTheory.ReducedNormal.SubnormalImage
/-!
# Non-subnormality on the original weak-closure point span

The point residual's two-core maps onto an inner Sylow of the original
orthogonal component orbit. That Sylow fixes only a singular field line,
whereas the reciprocal point lies in the nonsingular displacement line
of the selected critical involution. Thus O₂(L₁) cannot centralize the
reciprocal plane. Subnormality of L₁'s image on the reduced point span
would force precisely that centralization.

The final application uses the already constructed Y and I₀, their actual
point span and its literal centralizer quotient. It proves that L₁⁺ is
nontrivial and not subnormal, and that Y₀ does not normalize L₁. The later
exclusion of Y₀ ≤ M, Thompson movement and cubic contradiction remain.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. The earlier structural inputs retain their published
interfaces; the guarded same-G,T specialization and all later source
obligations through 14.7.52 remain with the final local assembly.
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

private theorem critical_point_core_not_centralizes_plane_of_orthogonal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (σ : Representation (ZMod 2) (HStar F.H) W) (hf : Function.Injective σ)
    (N : Subgroup (HStar F.H)) [N.Normal] (hm : HasOrthogonalFourOrbit σ N)
    (S : Sylow 2 N) (hS : (S : Subgroup N).map N.subtype = star F ((F.Li L 1).pCoreIn 2))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) (hPU : F.Vi 1 ⊔ c.Zα ≤ F.U) :
    ¬ (F.Li L 1).pCoreIn 2 ≤ centralizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨f,e,he⟩ := hm
  let a := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  have hE (g : N) (v : W) : E (σ g v) =
      ClassicalOrthogonal.FourPlusMatrix.Binary.action (a g) (E v) := by
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates (e (σ g v)) = _
    rw [he,OrthogonalEight.binaryCoordinates_equivariant]
    rfl
  let γ : Representation (ZMod 2) (HStar F.H) ClassicalOrthogonal.FourPlusMatrix.Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp σ
  let j := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    ClassicalOrthogonal.FourPlusMatrix.Binary.V).toMonoidHom.comp γ.asGroupHom
  have hE' (g : HStar F.H) (v : W) : E (σ g v) = j g (E v) := by
    change E (σ g v) = E (σ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hres (g : N) : j g = ClassicalOrthogonal.FourPlusMatrix.Binary.linearAction (a g) := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [←hE']
    exact hE g w
  have him : N.map j = ClassicalOrthogonal.FourPlusMatrix.Binary.linearAction.range := by
    ext z
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨a ⟨g,hg⟩,(hres ⟨g,hg⟩).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := a.surjective g
      exact ⟨g,g.property,hres g⟩
  have hjn : j.range ≤ normalizer
      (ClassicalOrthogonal.FourPlusMatrix.Binary.linearAction.range : Set _) := by
    rintro _ ⟨g,rfl⟩
    rw [←him]
    exact N.le_normalizer_map j (mem_map_of_mem _
      (show g ∈ normalizer (N : Set _) from le_normalizer_of_normal (mem_top g)))
  have hkernel : (σ.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change σ (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (hf (hx.trans σ.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  have hno (x : F.H) : fixedCodim (σ.comp (starMap F)) (zpowers x) ≠ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact OrthogonalEight.equivariant_extension_no_transvection
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp σ.asGroupHom)
      N f e he (starMap F x)
  have hdisj := critical_points_disjoint_of_no_transvections h hab structural hkernel hno s c hs ha
  have hCZ : c.Zα ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_intersection_commutator_of_no_transvections h hab structural hkernel hno s c hs ha]
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
  have hAH : c.Uα ≤ F.H := (critical_le_Q h structural c).trans (Q_le_H F)
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
      rw [map_sub,hE']
    · rintro ⟨x,rfl⟩
      obtain ⟨y,rfl⟩ := E.surjective x
      refine ⟨σ t y-y,⟨y,rfl⟩,?_⟩
      change E (σ t y-y) = j t (E y)-E y
      rw [map_sub,hE']
  have hr : Module.finrank (ZMod 2) ((j t).toLinearMap - LinearMap.id).range = 2 := by
    rw [←hmap,E.finrank_map_eq]
    exact critical_commutator_image_rank_of_no_transvections h hab structural hkernel hno s c hs ha
  have hzn : (E z).det ≠ 0 := by
    intro hzdet
    apply ClassicalOrthogonal.FourPlusMatrix.Binary.low_rank_involution_singular_not_mem_displacement
      (j t) (hjn ⟨t,rfl⟩) hr.le (by rw [←map_pow,ht2,map_one])
      (E z) (fun hh => hz0 (E.injective (hh.trans E.map_zero.symm))) hzdet
    rw [←hmap]
    exact ⟨z,s.imageSpace_mono hCZ hz,rfl⟩
  intro hc
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hfixed : E z ∈ fixedSpace
      ClassicalOrthogonal.FourPlusMatrix.Binary.action (S' : Subgroup _) := by
    rintro ⟨g,hg⟩
    change ClassicalOrthogonal.FourPlusMatrix.Binary.action g (E z) = E z
    obtain ⟨n,hn,rfl⟩ := hg
    have hnfix : σ (n : HStar F.H) z = z := by
      have hncore : (n : HStar F.H) ∈ star F ((F.Li L 1).pCoreIn 2) :=
        hS ▸ mem_map_of_mem N.subtype hn
      obtain ⟨x,hx,hex⟩ := hncore
      rw [←hex]
      obtain ⟨v,hv,hvz⟩ := (s.mem_imageSpace_iff _ _).mp hz
      have hvfix : (⟨(x:G)*(v:G)*(x:G)⁻¹,
          (mem_normalizer_iff.mp (s.normalized x.property) v).mp v.property⟩ : F.U) = v := by
        apply Subtype.ext
        change (x:G)*(v:G)*(x:G)⁻¹ = (v:G)
        exact mul_inv_eq_iff_eq_mul.mpr (hc hx (v:G) (mem_sup_right hv)).symm
      have hh := s.equivariant x v
      rw [hvfix] at hh
      rw [←hvz]
      exact hh.symm
    exact (hE n z).symm.trans (congrArg E hnfix)
  obtain ⟨v,hv,hvdet,hline⟩ :=
    ClassicalOrthogonal.FourPlusMatrix.Binary.sylow_fixed_field_line S'
  rw [hline] at hfixed
  obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hfixed
  apply hzn
  rw [←hb,Matrix.det_smul,hvdet,mul_zero]

/-- In the original exchanged branch the point core fails to centralize
 the actual reciprocal plane. -/
theorem local_nonnormal_component_point_core_not_centralizes_plane
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) (hPU : F.Vi 1 ⊔ c.Zα ≤ F.U) :
    ¬ (F.Li L 1).pCoreIn 2 ≤ centralizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) := by
  obtain ⟨hU,a,hm,_⟩ := local_nonnormal_component_whole_orthogonal d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let := hU
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let N := Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))
  let : N.Normal := by
    dsimp only [N]
    rw [←horbit]
    exact b.orbit_normal
  obtain ⟨S,hcore⟩ := local_nonnormal_component_point_core_sylow d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
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
  exact critical_point_core_not_centralizes_plane_of_orthogonal h hab structural
    a.representation a.faithful N hm S hcore s c hs ha hPU

/-- The point image cannot be subnormal on a reduced point span containing
 the actual reciprocal plane. All action and module premises are discharged
 from the original exchanged branch. -/
theorem local_nonnormal_component_point_image_not_subnormal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (ha : Nat.card (star F c.Uα) = 2) (hPU : F.Vi 1 ⊔ c.Zα ≤ F.U)
    (A : Subgroup G) (hLA : F.Li L 1 ≤ A) (hTA : (T : Subgroup G) ≤ A)
    (hred : IsPReduced 2 ((conjugateSpanBy (F.Vi 1) A).subgroupOf A))
    (hP : F.Vi 1 ⊔ c.Zα ≤ conjugateSpanBy (F.Vi 1) A) :
    letI := hred.normal
    ¬ (((F.Li L 1).subgroupOf A).map (QuotientGroup.mk'
      (centralizer ((conjugateSpanBy (F.Vi 1) A).subgroupOf A : Set A)))).IsSubnormal := by
  let := hred.normal
  intro hn
  have hc := hred.core_centralizes_of_subnormal_image ((F.Li L 1).subgroupOf A) hn
  rw [pCoreIn_subgroupOf 2 _ A hLA] at hc
  apply local_nonnormal_component_point_core_not_centralizes_plane d h hab structural
    previous faithful earlier I K hI hKI hK hnormal c hs ha hPU
  have hspan : conjugateSpanBy (F.Vi 1) A ≤ A :=
    conjugateSpanBy_le ((F.le_seed 1).trans (h.chosen.le_sylow.trans hTA)) A.le_normalizer
  intro x hx y hy
  let xA : A := ⟨x,hLA (pCoreIn_le 2 _ hx)⟩
  let yA : A := ⟨y,hspan (hP hy)⟩
  exact congrArg Subtype.val (hc (show xA ∈ ((F.Li L 1).pCoreIn 2).subgroupOf A from hx)
    yA (hP hy))

/-- The constructed original weak-closure local has a nontrivial, non-subnormal
point image. In particular its plane-action group does not normalize L₁. -/
theorem local_nonnormal_component_weakClosure_non_subnormal
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW⟩ :=
    local_nonnormal_component_weakClosure_local_with_actor d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  let P := F.Vi 1 ⊔ c.Zα
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := J ⊔ Y
  let W₀ := conjugateSpanBy (F.Vi 1) I₀
  let : (W₀.subgroupOf I₀).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let q := QuotientGroup.mk' (centralizer (W₀.subgroupOf I₀ : Set I₀))
  have hLA : F.Li L 1 ≤ I₀ := le_sup_left.trans le_sup_left
  have hTA : (T : Subgroup G) ≤ I₀ := le_sup_right.trans le_sup_left
  have hsub : ¬ (((F.Li L 1).subgroupOf I₀).map q).IsSubnormal :=
    local_nonnormal_component_point_image_not_subnormal d h hab structural previous
      faithful earlier I K hI hKI hK hnormal c hs ha (hplane.trans inf_le_left)
      I₀ hLA hTA hred hPVI
  have hne : ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ := by
    intro hz
    apply hsub
    rw [hz]
    exact Normal.isSubnormal inferInstance
  have hYn : ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) := by
    intro hn
    have hJ : J ≤ normalizer (F.Li L 1 : Set G) :=
      sup_le (F.Li L 1).le_normalizer
        (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes structural))
    have hI₀ : I₀ ≤ normalizer (F.Li L 1 : Set G) := by
      change I₀ = J ⊔ c.Qα at hIeq
      rw [hIeq]
      exact sup_le hJ (le_sup_right.trans hn)
    have hnL : ((F.Li L 1).subgroupOf I₀).Normal :=
      normal_subgroupOf_of_le_normalizer hI₀
    exact hsub ((hnL.map q (QuotientGroup.mk'_surjective _)).isSubnormal)
  exact ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hsub,hne,hYn⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
