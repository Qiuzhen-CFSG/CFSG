module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionQuotient
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.NoncentralChiefRefinement.TwoIntervals
public import Theory.GroupAction.NormalPChiefSeries
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two noncentral core layers in the selected diagram factor

For either canonical diagram factor R, the literal intersection
N = R ∩ O₂(O²(H)) is normal in R. Both N and O₂(R)/N have nontrivial
R-action. The first assertion uses characteristic two and perfectness:
centralizing N would make R centralize the original component core.
The second uses the actual surjection onto the marked parabolic residual,
whose kernel is a two-group and whose image has characteristic two.
The scalar cover is retained, including in the field-four linear row.

The original left Cartan normalizes N. Refining the two noncentral
sections and applying equivariant Jordan–Hölder proves that every actual
chief series on O₂(R) has at least two noncentral factors. Since the
same intervening layer is Cartan-invariant, the bound also holds for
the two-core of R A, with the original Cartan A. The Chapter 12
extension applies these results to the same prepared source pair.

This is the chief-layer step of 5.2.6, not a model or completion
recognition theorem. The remaining G₂/triality/unitary-four model
comparisons, F.1.12 core bound and global recognition remain with
qt-d-1222-rankone-generic-global. Original uniqueness retains its
independent producer qt-d-1222-rankone-global-uniqueness.

Source: Aschbacher–Smith, 5.2.6, printed pp.650–651, and F.1.12,
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

/-- An actual normal two-core layer with noncentral action below and above it. -/
@[expose] def NoncentralCoreLayer {X : Type*} [Group X] (N : Subgroup X) : Prop :=
  N.Normal ∧ N ≤ pCore 2 X ∧
    ¬ N ≤ center X ∧ ¬ ⁅pCore 2 X, (⊤ : Subgroup X)⁆ ≤ N

private theorem core_intersection_not_central
    {X : Type*} [Group X] [Finite X]
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (R : Subgroup X) [Group.IsPerfect R] (hne : R ≠ ⊥)
    (hn : pCore 2 X ≤ normalizer (R : Set X)) :
    ¬ (pCore 2 X).subgroupOf R ≤ center R := by
  intro hc
  have hi : ⁅pCore 2 X ⊓ R, R⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp (hc (show (⟨x,hx.2⟩ : R) ∈
      (pCore 2 X).subgroupOf R from hx.1)) ⟨y,hy⟩)
  have hh : ⁅pCore 2 X, R⁆ = ⊥ := by
    apply commutator_eq_bot_of_iterated_eq_bot
    apply le_bot_iff.mp
    exact (commutator_mono (le_inf (commutator_le_left _ _)
      (le_normalizer_iff_commutator_le_right.mp hn)) le_rfl).trans hi.le
  have hRQ : R ≤ pCore 2 X :=
    (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hh)).trans hX
  have hp : IsPGroup 2 R := pCore_isPGroup.to_le hRQ
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hne
  exact Group.IsPerfect.not_isNilpotent R hp.isNilpotent

private theorem two_layers_of_core_killed
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    (R : Subgroup X) [Group.IsPerfect R]
    (hn : pCore 2 X ≤ normalizer (R : Set X))
    [Nontrivial Y] [Group.IsPerfect Y]
    (f : R →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hkill : (pCore 2 X).subgroupOf R ≤ f.ker)
    (hY : centralizer (pCore 2 Y : Set Y) ≤ pCore 2 Y) :
    NoncentralCoreLayer ((pCore 2 X).subgroupOf R) := by
  let : Nontrivial R := Function.Surjective.nontrivial hf
  have hne : R ≠ ⊥ := (nontrivial_iff_ne_bot R).mp inferInstance
  refine ⟨inferInstance,le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩,
    core_intersection_not_central hX R hne hn,?_⟩
  intro hc
  have hmap : (pCore 2 R).map f = pCore 2 Y := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk, map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  have hh : ⁅pCore 2 Y, (⊤ : Subgroup Y)⁆ = ⊥ := by
    rw [←hmap, ←f.range_eq_top_of_surjective hf,MonoidHom.range_eq_map,
      ←map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr (hc.trans hkill)
  have ht : (⊤ : Subgroup Y) ≤ pCore 2 Y :=
    (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hh)).trans hY
  have hp : IsPGroup 2 Y :=
    (show IsPGroup 2 (⊤ : Subgroup Y) from top_le_iff.mp ht ▸ pCore_isPGroup).of_equiv topEquiv
  exact Group.IsPerfect.not_isNilpotent Y hp.isNilpotent

private theorem NoncentralCoreLayer.of_equiv
    {X Y : Type*} [Group X] [Group Y] {N : Subgroup X} (e : X ≃* Y)
    (h : NoncentralCoreLayer N) : NoncentralCoreLayer (N.map e.toMonoidHom) := by
  obtain ⟨hn,hN,hc,hu⟩ := h
  let := hn
  refine ⟨Normal.map inferInstance _ e.surjective,?_,?_,?_⟩
  · exact (map_mono hN).trans_eq (pCore_map_iso 2 e)
  · intro hh
    apply hc
    intro x hx
    rw [mem_center_iff]
    intro y
    apply e.injective
    simpa only [map_mul] using (show e y * e x = e x * e y from
      mem_center_iff.mp (hh (mem_map_of_mem _ hx)) (e y))
  · intro hh
    apply hu
    have he : ⁅pCore 2 X,(⊤ : Subgroup X)⁆.map e.toMonoidHom =
        ⁅pCore 2 Y,(⊤ : Subgroup Y)⁆ := by
      rw [map_commutator,pCore_map_iso,←MonoidHom.range_eq_map,
        e.toMonoidHom.range_eq_top_of_surjective e.surjective]
    exact (map_le_map_iff_of_injective e.injective).mp (he.symm ▸ hh)

private theorem NoncentralCoreLayer.map_subtype
    {X Y : Type*} [Group X] [Group Y] {R K : Subgroup X}
    (h : NoncentralCoreLayer (K.subgroupOf R)) (j : X →* Y) (hj : Function.Injective j) :
    NoncentralCoreLayer ((K.map j).subgroupOf (R.map j)) := by
  let e := R.equivMapOfInjective j hj
  have he : (K.subgroupOf R).map e.toMonoidHom = (K.map j).subgroupOf (R.map j) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem j hy
    · intro hx
      obtain ⟨y,rfl⟩ := e.surjective x
      obtain ⟨z,hz,hz'⟩ := hx
      refine ⟨y,?_,rfl⟩
      change (y : X) ∈ K
      exact (hj hz') ▸ hz
  exact he ▸ h.of_equiv e

open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Matrix.PSL3.LinearThree

/-- Both canonical linear factors have two distinct noncentral two-core layers. -/
theorem linear_source_factor_two_layers
    {X : Type*} [Group X] [Finite X]
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    {M C : Subgroup X} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : 4 ≤ Nat.card F) (e : sourceImage M C ≃* PSL(3,F)) (i : Bool) :
    NoncentralCoreLayer ((C.pCoreIn 2).subgroupOf (Prime.linearSourceFactor M C e i)) := by
  let r := Prime.linearComponentProjection M C e
  have hr : Function.Surjective r :=
    e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective C)
  have hk : pCore 2 C ≤ r.ker := by
    intro x hx
    apply e.map_eq_one_iff.mpr
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff x.val).mpr
    exact hO (pCoreIn_le_of_subnormal 2 hC.subnormal (mem_map_of_mem C.subtype hx))
  let r0 := QuotientGroup.lift (pCore 2 C) r hk
  let q0 := QuotientGroup.mk' (pCore 2 C)
  have hr0 : Function.Surjective r0 := QuotientGroup.lift_surjective_of_surjective _ _ hr _
  let R := CoveredLocals.factor r i
  let P := (CoveredLocals.parabolic F i).comap r
  let B := CoveredLocals.localProjective F i
  have him : R.map r = B := CoveredLocals.factor_image hF r hr i
  let f := (MulEquiv.subgroupCongr him).toMonoidHom.comp (r.subgroupMap R)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr him).surjective.comp (r.subgroupMap_surjective R)
  let := hqs
  have him0 : R.map q0 = CoveredLocals.factor r0 i :=
    map_solvableResidual_comap q0 (QuotientGroup.mk'_surjective _) ((CoveredLocals.parabolic F i).comap r0)
  have hkf : IsPGroup 2 f.ker := by
    apply (pCore_isPGroup.comap_subtype (H := pCore 2 C) (K := R)).to_le
    intro x hx
    have hp : q0 x.val ∈ CoveredLocals.factor r0 i := him0 ▸ mem_map_of_mem q0 x.property
    have heq : (⟨q0 x.val,hp⟩ : CoveredLocals.factor r0 i) = 1 := by
      apply CoveredLocals.factor_projection_injective hF r0 hr0 (pCore_quotient_pCore_eq_bot 2) i
      change r0 (q0 x.val) = r0 1
      rw [map_one]
      exact congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff x.val).mp (congrArg Subtype.val heq)
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  let : Group.IsPerfect B := by
    cases i
    · exact lineLocal_isPerfect F hF
    · exact pointLocal_isPerfect F hF
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr
    (fun hb => CoveredLocals.local_not_le_borel i (hb ▸ bot_le))
  have hn : pCore 2 C ≤ normalizer (R : Set C) :=
    ((hk.trans ((CoveredLocals.parabolic F i).ker_le_comap r)).trans P.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  have hB : centralizer (pCore 2 B : Set B) ≤ pCore 2 B := by
    apply (ChapterA.generalizedFitting_eq_pCore_iff 2).mp
    cases i
    · exact lineLocal_generalizedFitting_eq_twoCore F
    · exact pointLocal_generalizedFitting_eq_twoCore F
  have hl := two_layers_of_core_killed (subnormal_core_selfCentralizing hX C hC.subnormal)
    R hn f hf hkf (by intro x hx; apply Subtype.ext; exact hk hx) hB
  exact hl.map_subtype C.subtype C.subtype_injective

open Theory.SpecificGroups.SymplecticFour in
/-- The same two layers occur on both literal symplectic factors. -/
theorem symplectic_source_factor_two_layers
    {X : Type*} [Group X] [Finite X]
    (hX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X)
    {M C : Subgroup X} (hk : sourceKernel M = pCore 2 X)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp F) (i : Bool) :
    NoncentralCoreLayer ((pCore 2 X).subgroupOf (Prime.symplecticSourceFactor M C e i)) := by
  let A := Prime.symplecticModelLocal F i
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := (sourceImage M C).subtype_injective.comp e.symm.injective
  let d := A.equivMapOfInjective j hj
  let : Group.IsPerfect A := by
    cases i
    · exact planeLocal_perfect hF hf
    · exact pointLocal_perfect hF hf
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^f from Nat.pow_lt_pow_right (by decide) hf)
  let := NaturalExtension.model_simple hlarge
  let : Nontrivial A := by
    cases i
    · exact Function.Surjective.nontrivial Plane.quotientMap_surjective
    · exact Function.Surjective.nontrivial pointQuotient_surjective
  let : Group.IsPerfect (A.map j) := Group.IsPerfect.map j
  let : Nontrivial (A.map j) := d.symm.toEquiv.nontrivial
  have hfit : generalizedFitting A = pCore 2 A := by
    cases i
    · exact (planeNaturalExtension hF hf).generalizedFitting_eq hlarge
    · exact (pointNaturalExtension hF hf).generalizedFitting_eq hlarge
  have hfit' : centralizer (pCore 2 (A.map j) : Set (A.map j)) ≤ pCore 2 (A.map j) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 d).mp
      ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  let q := QuotientGroup.mk' (sourceKernel M)
  let P := (A.map j).comap q
  let R := Prime.symplecticSourceFactor M C e i
  let : Group.IsPerfect R := Group.IsPerfect.map P.subtype
  have him : R.map q = A.map j := by
    change ((solvableResidual P).map P.subtype).map q = _
    rw [map_solvableResidual_comap q (QuotientGroup.mk'_surjective _),
      solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype]
  let r := (MulEquiv.subgroupCongr him).toMonoidHom.comp (q.subgroupMap R)
  have hr : Function.Surjective r :=
    (MulEquiv.subgroupCongr him).surjective.comp (q.subgroupMap_surjective R)
  have hkr : IsPGroup 2 r.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr him).injective,
      ker_subgroupMap,QuotientGroup.ker_mk',hk]
    exact pCore_isPGroup.comap_subtype
  have hO : pCore 2 X ≤ q.ker := by rw [QuotientGroup.ker_mk',hk]
  have hn : pCore 2 X ≤ normalizer (R : Set X) :=
    ((hO.trans ((A.map j).ker_le_comap q)).trans P.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  exact two_layers_of_core_killed hX R hn r hr hkr
    (by intro x hx; apply Subtype.ext; exact hO hx) hfit'

variable {G : Type*} [Group G] [Finite G]

/-- Retain the original residual-core layer on the same canonical factor
used by the full Cartan and Borel preparation. -/
theorem diagram_source_rightFactor_two_layers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hs : RightDiagramSource T L H) :
    ∃ (R : Subgroup G) (f : ℕ), RightFactor T L H A B R ∧ Group.IsPerfect R ∧
      ¬ ChapterC.IsShort R ∧ 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
      NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R) := by
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1)
  let M := (normalizer (L : Set G)).subgroupOf H
  have hO : pCore 2 H ≤ sourceKernel M := normal_le_normalCore.mpr
    ((pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2)).trans
      (comap_mono h.sylow_normalizes))
  obtain ⟨C,f,hC,hqs,_,hf,hc,hm⟩ := hs
  let : C.Normal := DiagramHall.single_component_normal (T.subtype hH.1.1.2) hC hc
  have hCeq : C = pResidual 2 H :=
    (DiagramHall.single_component_eq_twoResidual (T.subtype hH.1.1.2) hC hc).symm
  have hKm : (C.pCoreIn 2).map H.subtype = (residual H).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 C H.subtype H.subtype_injective]
    congr 1
    exact congrArg (map H.subtype) hCeq
  rcases hm with ⟨F,_,_,_,_,hF,e,he,hmove⟩ | ⟨F,_,_,_,_,hF,e,he,hmove⟩
  · let R0 := Prime.linearSourceFactor M C e true
    let R := R0.map H.subtype
    have hlarge : 4 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hf
    have hnot := linear_source_factor_not_short hchar hC hO hlarge e true
    let : Group.IsPerfect (CoveredLocals.factor (Prime.linearComponentProjection M C e) true) :=
      Group.IsPerfect.map _
    let : Group.IsPerfect R0 := Group.IsPerfect.map _
    refine ⟨R,f,linear_source_rightFactor_of_nonprojective_four h.sylow_normalizes hH hpar
      hthree c hN hC hqs hc hf hF e he hmove true,Group.IsPerfect.map H.subtype,?_,hf,?_,?_⟩
    · intro hshort
      exact hnot (ChapterC.RankOne.Solvable.isShort_of_equiv
        (R0.equivMapOfInjective H.subtype H.subtype_injective).symm hshort)
    · exact (linear_source_factor_geometry h.sylow_normalizes hH hpar c hN
        hC hqs hc hf hF e he hmove true).2.2.2.1
    · rw [←hKm]
      exact (linear_source_factor_two_layers hchar hC hqs hO hlarge e true).map_subtype
        H.subtype H.subtype_injective
  · obtain ⟨eF,_,hr⟩ := symplectic_source_rightFactors h.sylow_normalizes hH hpar c hN
      hC hqs hc hf hF e he hmove
    let R0 := Prime.symplecticSourceFactor M C eF true
    let : Group.IsPerfect R0 := by
      unfold R0 Prime.symplecticSourceFactor
      exact Group.IsPerfect.map _
    refine ⟨R0.map H.subtype,f,(hr true).1,Group.IsPerfect.map H.subtype,?_,hf,(hr true).2.1,?_⟩
    · intro hshort
      exact symplectic_source_factor_not_short hchar hO hf hF eF true
        (ChapterC.RankOne.Solvable.isShort_of_equiv
          (R0.equivMapOfInjective H.subtype H.subtype_injective).symm hshort)
    · have hk := Prime.symplectic_sourceKernel_eq_twoCore (T.subtype hH.1.1.2)
        (comap_mono h.sylow_normalizes) hC hqs hc hf hF e
      have hRC : R0 ≤ C := by
        apply (map_le_map_iff_of_injective H.subtype_injective).mp
        rw [hCeq]
        exact (hr true).1.le_residual
      have hcore : (C.pCoreIn 2).subgroupOf R0 = (pCore 2 H).subgroupOf R0 := by
        rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype]
        ext x
        exact ⟨And.right,fun hx => ⟨hRC x.property,hx⟩⟩
      rw [←hKm]
      apply NoncentralCoreLayer.map_subtype (j := H.subtype) _ H.subtype_injective
      rw [hcore]
      exact symplectic_source_factor_two_layers hchar hk hf hF eF true


omit [Finite G] in
/-- The layer in O₂(O²(H)) is invariant under the original left Cartan.
This is the invariant section required in the remaining U₄ argument. -/
theorem Preparation.cartan_normalizes_residual_core_intersection
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    A ≤ normalizer ((residual H).pCoreIn 2 ⊓ R : Set G) := by
  have hA : A ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
    (d.cartans.left_le.trans hN).trans
      (normalizer_le_normalizer_characteristic_image (residual H) (pCore 2 (residual H)))
  exact (le_inf hA d.cartan_normalizes_right).trans inf_normalizer_le_normalizer_inf

open NoncentralChiefRefinement in
/-- Every actual chief series of the two-core contains at least two
noncentral factors. The two normal sections, rather than an assumed
chief-count parameter, give the bound. -/
theorem NoncentralCoreLayer.two_le_noncentralCount
    {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    {N : Subgroup X} (h : NoncentralCoreLayer N)
    (s : SeriesOn (pCore 2 X)) : 2 ≤ s.noncentralCount := by
  let := h.1
  have hp : IsPPerfect 2 X := by
    intro J hJ hq
    let := hJ
    apply top_unique
    intro x _
    apply (QuotientGroup.eq_one_iff x).mp
    by_contra hh
    let : Nontrivial (X ⧸ J) := ⟨⟨QuotientGroup.mk x,1,hh⟩⟩
    exact Group.IsPerfect.not_isNilpotent (X ⧸ J) hq.isNilpotent
  let A : NormalNode X := ⟨N,h.1⟩
  let B : NormalNode X := ⟨pCore 2 X,inferInstanceAs (pCore 2 X).Normal⟩
  have hA : IsNoncentralTwo ⊥ A := by
    refine ⟨(pCore_isPGroup.to_le h.2.1).to_quotient _,?_⟩
    intro hc
    apply h.2.2.1
    rw [isCentral_iff_commutator_le] at hc
    have he : ⁅N,(⊤ : Subgroup X)⁆ = ⊥ := by
      rw [commutator_comm]
      exact le_bot_iff.mp hc
    simpa only [coe_top,centralizer_univ] using commutator_eq_bot_iff_le_centralizer.mp he
  have hB : IsNoncentralTwo A B := by
    refine ⟨pCore_isPGroup.to_quotient _,?_⟩
    intro hc
    apply h.2.2.2
    have hh : ⁅(⊤ : Subgroup X),pCore 2 X⁆ ≤ N :=
      (isCentral_iff_commutator_le A B).mp hc
    rwa [commutator_comm] at hh
  obtain ⟨a,ha0,ha1⟩ := exists_chiefSeries (⊥ : NormalNode X) A bot_le
  obtain ⟨b,hb0,hb1⟩ := exists_chiefSeries A B h.2.1
  have ha : 1 ≤ a.noncentralTwoCount := by
    obtain ⟨i,hi⟩ := a.exists_noncentralTwo_of_isPPerfect hp (by rwa [ha0,ha1])
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i,hi⟩⟩,inferInstance⟩
  have hb : 1 ≤ b.noncentralTwoCount := by
    obtain ⟨i,hi⟩ := b.exists_noncentralTwo_of_isPPerfect hp (by rwa [hb0,hb1])
    exact Nat.card_pos_iff.mpr ⟨⟨⟨i,hi⟩⟩,inferInstance⟩
  rw [s.noncentralCount_eq_twoCount pCore_isPGroup,
    s.series.noncentralTwoCount_eq (a.smash b (ha1.trans hb0.symm))
      (by simpa using s.head_eq.trans ha0.symm)
      (by simpa using s.last_eq.trans hb1.symm), ChiefSeries.noncentralTwoCount_smash]
  omega

open NoncentralChiefRefinement in
private theorem core_layer_two_chief_overgroup
    {Y X : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] [Group X] [Finite X]
    {N : Subgroup Y} (h : NoncentralCoreLayer N)
    (f : Y →* X) (hf : Function.Injective f) (hn : (N.map f).Normal)
    (hQ : (pCore 2 Y).map f ≤ pCore 2 X)
    (s : SeriesOn (pCore 2 X)) : 2 ≤ s.noncentralCount := by
  let := hn
  have hp : IsPPerfect 2 Y := by
    intro J hJ hq
    let := hJ
    apply top_unique
    intro x _
    apply (QuotientGroup.eq_one_iff x).mp
    by_contra hh
    let : Nontrivial (Y ⧸ J) := ⟨⟨QuotientGroup.mk x,1,hh⟩⟩
    exact Group.IsPerfect.not_isNilpotent (Y ⧸ J) hq.isNilpotent
  have hR : f.range ≤ pResidual 2 X := le_pResidual_of_isPPerfect f.range
    (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hNc : N.map f ≤ pCore 2 X := (map_mono h.2.1).trans hQ
  have hlo : ⁅N.map f,f.range⁆ ≠ ⊥ := by
    intro hz
    have he : ⁅N,(⊤ : Subgroup Y)⁆ = ⊥ := by
      apply map_injective hf
      rw [map_commutator,←MonoidHom.range_eq_map,hz,Subgroup.map_bot]
    exact h.2.2.1 (by
      simpa only [coe_top,centralizer_univ] using commutator_eq_bot_iff_le_centralizer.mp he)
  have hhi : ¬ ⁅(pCore 2 Y).map f,f.range⁆ ≤ N.map f := by
    intro hh
    rw [MonoidHom.range_eq_map,←map_commutator] at hh
    exact h.2.2.2 ((map_le_map_iff_of_injective hf).mp hh)
  by_cases hz : s.noncentralCount = 0
  · have hh := s.series.residual_commutator_le_head_of_count_zero
      (by rw [s.last_eq]; exact pCore_isPGroup)
      (by rwa [←s.noncentralCount_eq_twoCount pCore_isPGroup])
    rw [s.last_eq,s.head_eq] at hh
    exact (hlo (le_bot_iff.mp ((commutator_mono hNc hR).trans hh))).elim
  by_cases ho : s.noncentralCount = 1
  · rcases s.residual_dichotomy_of_count_one pCore_isPGroup ho (N.map f) hNc with hc | hc
    · exact (hlo (le_bot_iff.mp ((commutator_mono le_rfl hR).trans hc.le))).elim
    · exact (hhi ((commutator_mono hQ hR).trans hc)).elim
  omega

/-- The same two layers survive adjoining the original left Cartan. This
uses its actual normalization of the intervening residual-core layer,
so possible fusion of chief factors by the Cartan is not ignored. -/
theorem Preparation.cartan_core_two_chief
    {T : Sylow 2 G} {L H A B R : Subgroup G} (d : Preparation T L H A B R)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    (hp : Group.IsPerfect R)
    (hl : NoncentralCoreLayer (((residual H).pCoreIn 2).subgroupOf R))
    (s : NoncentralChiefRefinement.SeriesOn (pCore 2 (R ⊔ A : Subgroup G))) :
    2 ≤ s.noncentralCount := by
  let := hp
  let J := R ⊔ A
  let R' := R.subgroupOf J
  let N := ((residual H).pCoreIn 2).subgroupOf R
  let f : R →* J := inclusion (show R ≤ J from le_sup_left)
  have hnR : J ≤ normalizer (R : Set G) := sup_le R.le_normalizer d.cartan_normalizes_right
  let : R'.Normal := normal_subgroupOf_of_le_normalizer hnR
  let e : R ≃* R' := (subgroupOfEquivOfLe (show R ≤ J from le_sup_left)).symm
  have hfe : f = R'.subtype.comp e.toMonoidHom := rfl
  have hQ : (pCore 2 R).map f ≤ pCore 2 J := by
    rw [hfe,←map_map,pCore_map_iso]
    exact le_sSup ⟨inferInstance,pCore_isPGroup.map R'.subtype⟩
  have hnN : J ≤ normalizer ((residual H).pCoreIn 2 ⊓ R : Set G) := by
    refine sup_le ?_ (d.cartan_normalizes_residual_core_intersection hN)
    have hk : R ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
      (d.right_le_residual.trans (residual H).le_normalizer).trans
        (normalizer_le_normalizer_characteristic_image (residual H) (pCore 2 (residual H)))
    exact (le_inf hk R.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have heN : N.map f = ((residual H).pCoreIn 2 ⊓ R).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans le_sup_left)]
    change N.map R.subtype = _
    exact subgroupOf_map_subtype _ _
  have hn : (N.map f).Normal := by
    rw [heN]
    exact normal_subgroupOf_of_le_normalizer hnN
  exact core_layer_two_chief_overgroup hl f (inclusion_injective _) hn hQ s

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
