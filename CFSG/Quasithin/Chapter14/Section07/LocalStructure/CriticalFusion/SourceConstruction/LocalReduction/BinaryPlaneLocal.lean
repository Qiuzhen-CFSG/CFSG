module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneSylow
public import Theory.Representation.OrthogonalFourPlusMatrix.TwoGroupDisplacements
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup
public import Theory.GroupTheory.PCoreOvergroup

/-!
# The reciprocal-plane weak-closure local in the exchanged branch

The normal span R = Q_H ∨ ⟨Uα^(L₁T)⟩ normalizes the original reciprocal
plane P. On the literal orthogonal quotient U/V₁, every conjugate of the
critical involution lies in the same two-core and has field rank one.
Rank-one quadratic isometries in a common two-group fix each other's
whole displacement spaces. The exact section kernel lifts this fixation
to the original plane, including its central point.

Applying the proved plane-Sylow extension theorem constructs Y = Y₀R
with Sylow R and centralizer C_Y(P) = O₂(Y). Its weak closure is normalized
by I₀ = ⟨L₁T,Y⟩ = ⟨L₁T,Qα⟩, placing this actual group inside a proper
two-local. Even characteristic and B.2.14 make the actual point span
⟨V₁^I₀⟩ two-reduced; the reciprocal cross-core movement puts P inside it.
No plane-normalization, local-existence or reducedness callback remains.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1058,
refs/quasithin.pdf. The non-subnormality application is in
BinaryNonSubnormal; the Thompson and cubic arguments on pp.1058–1059
remain to be proved. Earlier structural inputs
retain the universal published interface; final assembly still requires
the guarded same-G,T successors and all later duties through 14.7.52.
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

/-- The normal span of the selected critical actor normalizes the actual
reciprocal plane in the literal orthogonal section. -/
theorem critical_normal_span_normalizes_plane_of_orthogonal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (σ : Representation (ZMod 2) (HStar F.H) W) (hf : Function.Injective σ)
    (N : Subgroup (HStar F.H)) [N.Normal] (hm : HasOrthogonalFourOrbit σ N)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (hR : c.Uα ≤ F.Ri L 1) (ha : Nat.card (star F c.Uα) = 2)
    (hPU : F.Vi 1 ⊔ c.Zα ≤ F.U) (hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G) = 4) :
    F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα (F.Li L 1 ⊔ (T : Subgroup G)) ≤
      normalizer ((F.Vi 1 ⊔ c.Zα : Subgroup G) : Set G) := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  obtain ⟨E,j,hj,hE,hjn,_⟩ := orthogonal_coordinates_with_inner σ hf N hm
  let π := j.comp (starMap F)
  have hπ (x : F.H) (w : W) : E ((σ.comp (starMap F)) x w) = π x (E w) := hE _ _
  have hkernel : (σ.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change σ (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (hf (hx.trans σ.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  obtain ⟨f,e,he⟩ := hm
  have hno (x : F.H) : fixedCodim (σ.comp (starMap F)) (zpowers x) ≠ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact OrthogonalEight.equivariant_extension_no_transvection
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp σ.asGroupHom)
      N f e he (starMap F x)
  have hCZ : c.Zα ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_intersection_commutator_of_no_transvections h hab structural hkernel hno s c hs ha]
    exact commutator_mono inf_le_left le_rfl
  let P := F.Vi 1 ⊔ c.Zα
  have hpc : Nat.card (s.imageSpace P) = 2 := by
    rw [s.imageSpace_card_eq_relIndex P hPU]
    have hh := relIndex_mul_card_of_le (show F.Vi 1 ≤ P from le_sup_left)
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hp,hfour] at hh
    omega
  obtain ⟨z,hz0,_⟩ := (Nat.card_eq_two_iff' (0 : s.imageSpace P)).mp hpc
  have hz0' : (z : W) ≠ 0 := fun hh => hz0 (Subtype.ext hh)
  have hzmove : (z : W) ∈ s.imageSpace ⁅F.U,c.Uα⁆ := by
    have he : s.imageSpace P = s.imageSpace c.Zα := by
      dsimp only [P]
      rw [sup_comm,s.imageSpace_sup_kernel c.Zα (le_sup_right.trans hPU)]
    exact s.imageSpace_mono hCZ (he ▸ z.property)
  let A := star F c.Uα
  obtain ⟨t,ht,htuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp ha
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
  have hr : Module.finrank (ZMod 2) ((j t).toLinearMap-LinearMap.id).range = 2 := by
    have hh := Representation.BinaryOffender.NaturalTensor.operatorFixedCodim_eq_of_equiv
      (σ t) (j t).toLinearMap E (hE t)
    change Module.finrank (ZMod 2) (σ t-LinearMap.id).range =
      Module.finrank (ZMod 2) ((j t).toLinearMap-LinearMap.id).range at hh
    rw [←hh,←hsr]
    exact critical_commutator_image_rank_of_no_transvections h hab structural hkernel hno s c hs ha
  have hzj : E z ∈ ((j t).toLinearMap-1).range := by
    rw [hsr] at hzmove
    obtain ⟨v,hv⟩ := hzmove
    refine ⟨E v,?_⟩
    change j t (E v)-E v=E z
    rw [←hE,←map_sub]
    exact congrArg E hv
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H := sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hJR : J ≤ normalizer (F.Ri L 1 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  let B := (star F (F.Ri L 1)).map j
  have hB : IsPGroup 2 B := ((isPGroup_pCoreIn 2 J).comap_subtype.map (starMap F)).map j
  have htB : j t ∈ B := mem_map_of_mem j
    (map_mono (subgroupOf_mono F.H hR) t.property)
  have hjt2 : j t*j t=1 := by rw [←map_mul,←pow_two,ht2,map_one]
  have hnorm (x : F.H) (hx : π x (E z) = E z) : (x:G) ∈ normalizer (P : Set G) :=
    (ClassicalOrthogonal.FourPlusMatrix.Binary.PointCore.section_normalizer_iff
      s π E hπ P hPU le_sup_left hpc z z.property hz0' x).mpr hx
  apply sup_le
  · rintro x ⟨q,hq,rfl⟩
    apply hnorm q
    change j (starMap F q) (E z)=E z
    rw [show starMap F q=1 from (QuotientGroup.eq_one_iff _).mpr hq,map_one]
    rfl
  · apply (closure_le _).mpr
    rintro x ⟨g,hg,u,hu,rfl⟩
    let gH : F.H := ⟨g,hJH hg⟩
    let uH : F.H := ⟨u,hAH hu⟩
    let xH := gH*uH*gH⁻¹
    apply hnorm xH
    have huA : starMap F uH ∈ A := mem_map_of_mem _ hu
    by_cases hu1 : starMap F uH = 1
    · change j (starMap F (gH*uH*gH⁻¹)) (E z)=E z
      simp only [map_mul,map_inv,hu1,map_one,mul_one,mul_inv_cancel]
      rfl
    have hut : starMap F uH = t := congrArg Subtype.val
      (htuniq ⟨starMap F uH,huA⟩ (fun hh => hu1 (congrArg Subtype.val hh)))
    have hxB : π xH ∈ B := by
      apply mem_map_of_mem j
      apply mem_map_of_mem (starMap F)
      exact (mem_normalizer_iff.mp (hJR hg) u).mp (hR hu)
    have hx2 : π xH*π xH=1 := by
      change j (starMap F xH)*j (starMap F xH)=1
      rw [←map_mul,←pow_two]
      have he : starMap F xH = starMap F gH*t*(starMap F gH)⁻¹ := by
        simp only [xH,map_mul,map_inv,hut]
      rw [he,←MulAut.conj_apply,←map_pow,ht2,map_one,map_one]
    have hxr : Module.finrank (ZMod 2) ((π xH).toLinearMap-LinearMap.id).range ≤ 2 := by
      let ρ : Representation (ZMod 2) (HStar F.H) ClassicalOrthogonal.FourPlusMatrix.Binary.V :=
        LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp j
      have hconj : starMap F xH = starMap F gH*t*(starMap F gH)⁻¹ := by
        simp only [xH,map_mul,map_inv,hut]
      change Module.finrank (ZMod 2) (ρ (starMap F xH)-LinearMap.id).range ≤ 2
      rw [←fixedCodim_zpowers_eq_displacement_rank,hconj,fixedCodim_zpowers_conj,
        fixedCodim_zpowers_eq_displacement_rank]
      exact hr.le
    obtain ⟨n,hn⟩ := hB.exists_pow_pow_eq_one (⟨π xH* j t,B.mul_mem hxB htB⟩ : B)
    have hp : (π xH*j t)^(2^n)=1 := congrArg Subtype.val hn
    exact ClassicalOrthogonal.FourPlusMatrix.Binary.low_rank_two_power_fixes_displacement
      (π xH) (j t) (hjn ⟨starMap F xH,rfl⟩) (hjn ⟨t,rfl⟩)
      hx2 hjt2 hxr hr.le ⟨n,hp⟩ (E z) hzj


/-- The original exchanged branch constructs the normal-span Sylow and
its weak-closure local, with plane normalization discharged. -/
theorem local_nonnormal_component_weakClosure_local_with_actor
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
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ := by
  obtain ⟨c,hs,hR,hcard,hindex,hE,hfour,hplane,hYn,hNY,hpoint,hind,hR₀T,hUR₀,hext⟩ :=
    local_nonnormal_component_plane_sylow_extensions d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  obtain ⟨hU,a,hm,_⟩ := local_nonnormal_component_whole_orthogonal d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let := hU
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor d h hab structural previous faithful earlier
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
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
  let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
  let I₀ := J ⊔ Y
  let W₀ := ChapterE.indexedWeakClosure V R 0
  have hRN : R ≤ normalizer (P : Set G) :=
    critical_normal_span_normalizes_plane_of_orthogonal h hab structural
      a.representation a.faithful b.orbit hm' s c hs hR hcard
      (hplane.trans inf_le_left) hfour
  obtain ⟨hR₀R,hRT,hJR⟩ := critical_plane_normal_span c hR
  obtain ⟨hSylow,hcore,he,hVW,hWY,hYW⟩ := hext R hR₀R hRT hRN
  have hIW : I₀ ≤ normalizer (W₀ : Set G) :=
    sup_le (hJR.trans (ChapterE.normalizer_le_weakClosure_normalizer V R 0)) hYW
  have hWR : W₀ ≤ R := ChapterE.indexedWeakClosure_le V R 0
  have hWne : W₀ ≠ ⊥ := by
    intro hz
    exact h.chosen.ne_bot (bot_unique (hz ▸ hVW))
  have hlocal : IsTwoLocal (normalizer (W₀ : Set G)) :=
    ⟨W₀,hWne,T.isPGroup'.to_le (hWR.trans hRT),rfl⟩
  let := d.qtke.simple
  have hproper := twoLocal_ne_top_of_nonabelian_simple d.qtke.nonabelian hlocal
  have hIeq : I₀ = J ⊔ c.Qα := by
    apply le_antisymm
    · apply sup_le le_sup_left
      apply sup_le _ (hRT.trans (le_sup_right.trans le_sup_left))
      exact sup_le
        ((show F.H.pCoreIn 2 ≤ R from le_sup_left).trans
          (hRT.trans (le_sup_right.trans le_sup_left))) le_sup_right
    · exact sup_le le_sup_left (le_sup_right.trans (le_sup_left.trans le_sup_right))
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple I₀ :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIW)).mp
      ((d.qtke.twoLocal_sqtk hlocal).subgroup (I₀.subgroupOf (normalizer (W₀ : Set G))))
  have hTI : (T : Subgroup G) ≤ I₀ := le_sup_right.trans le_sup_left
  have hcharI : HasCharacteristicTwo I₀ := by
    obtain ⟨M,hNM,hM⟩ := Finite.exists_le_maximal hlocal
    have hIM := hIW.trans hNM
    have hTM := hTI.trans hIM
    have hc : HasCharacteristicTwo (I₀.subgroupOf M) :=
      centralizer_pCore_le_of_sylow_le (T.subtype hTM) (I₀.subgroupOf M)
        (comap_mono hTI) (d.qtke.evenCharacteristic T M hM hTM)
    exact hc.of_equiv (subgroupOfEquivOfLe hIM)
  have hred : IsPReduced 2 ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀) := by
    let := h.chosen.elementary
    let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
    apply reduced_conjugateSpan_of_sylow_central T I₀ (F.Vi 1) hTI
      ((F.le_seed 1).trans h.chosen.le_sylow) _ hcharI
    exact le_centralizer_iff.mp ((F.invariant 1).trans
      (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))))
  have hkernel : (a.representation.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change a.representation (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp
        (a.faithful (hx.trans a.representation.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  obtain ⟨f,e,heq⟩ := hm'
  have hno (x : F.H) : fixedCodim (a.representation.comp (starMap F)) (zpowers x) ≠ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact OrthogonalEight.equivariant_extension_no_transvection
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).toMonoidHom.comp
        a.representation.asGroupHom) b.orbit f e heq (starMap F x)
  let := local_nonnormal_component_section_irreducible d h hab structural previous
    faithful earlier I K hI hKI hK hnormal s
  have hPVI : P ≤ conjugateSpanBy (F.Vi 1) I₀ := by
    apply sup_le (le_conjugateSpanBy _ _)
    rw [←critical_reverse_cross_core_commutator_of_irreducible h hab structural
      hkernel hno s c hs hcard]
    apply (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
    apply le_normalizer_iff_commutator_le_left.mp
    exact (show c.Qα ≤ I₀ from le_sup_right.trans (le_sup_left.trans le_sup_right)).trans
      (le_normalizer_conjugateSpanBy _ _)
  have hVIW : conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ :=
    conjugateSpanBy_le ((F.le_seed 1).trans hVW) hIW
  exact ⟨c,hs,hR,hcard,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW⟩

/-- The original weak-closure-local interface. Its successor also retains
 the selected actor's order for the non-subnormality argument. -/
theorem local_nonnormal_component_weakClosure_local
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
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ := by
  obtain ⟨c,hs,hR,_,hrest⟩ :=
    local_nonnormal_component_weakClosure_local_with_actor d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  exact ⟨c,hs,hR,hrest⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
