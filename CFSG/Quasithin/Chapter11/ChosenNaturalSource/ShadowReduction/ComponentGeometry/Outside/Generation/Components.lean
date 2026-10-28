module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Witness.Equal
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Hall
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.PResidual.ConjugateGeneration
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource

/-!
# The original component and Hall reduction for outside generation

If n(H)>1, the proved E.2.2 construction supplies an actual relative
C-component I of H, with H=IT and O²(H)=<I^T>. It escapes M and belongs
to the genuine local family. Source 1.2.4, in the literal two-local Gz,
constructs its containing component. The actual component commutator
theorem then gives I ≤ K or [K,I] ≤ O₂(K).

When K=L₁, containment contradicts escape. Passing to the T-orbit puts
the entire residual in C_Gz(K/O₂(K)). The constructed full odd Hall actor
lies in the residual and is faithful on V under precisely
LocalGeometry.WeakClosure.Generation.OddKernelNormalizer, whose producer
is qt-d-1222-natural-odd-kernel-normalizer. This input remains undischarged.

The non-equal containment exclusion and the natural-module Hall-order and
centralization argument remain with qt-d-1222-shadow-component-witness,
as do n(H)=1 and the remaining R₁-Sylow witness obligations. Earlier
geometry and component equality retain the producers named in
Witness.Equal and final discharge by qt-d-1222-shadow-components.
This module proves the source reductions, not the conclusion of 11.4.4.

Source: Aschbacher--Smith, E.2.2, 1.2.1--4 and 11.4.4,
printed pp.215--216,503--505 and778.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro H hH hq
  let : H.Normal := hH
  by_contra hne
  let : Nontrivial (A ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ H) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
  let : Group.IsNilpotent (A ⧸ H) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ H) inferInstance

/-- The E.2.2 component and its exact Sylow orbit on the original H carrier.
This is the opening reduction of 11.4.4; it does not assume a component witness. -/
theorem component_of_large_generation (h : Comparison.EarlierGeometry E)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E)
    (hn : 1 < ChapterE.generationParameter E.H) :
    ∃ I : Subgroup G, I ≤ E.H ∧ (I.subgroupOf E.H).IsCComponent ∧
      I ∈ Chapter1.L G (T : Subgroup G) ∧ ¬ I ≤ E.M ∧
      I ⊔ (T : Subgroup G) = E.H ∧
      conjugateSpanBy I (T : Subgroup G) = (pResidual 2 E.H).map E.H.subtype := by
  have hTH : (T : Subgroup G) ≤ E.H := hH.1.1.2
  have hPH : (T.subtype hTH : Subgroup E.H).map E.H.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf E.H).map E.H.subtype = _
    exact map_subgroupOf_eq_of_le hTH
  have hs : ¬ Group.IsSolvable E.H := by
    intro hs
    let := hs
    exact (not_lt_of_ge ChapterE.generationParameter_le_one_of_solvable) hn
  have hQ : IsSQTK KnownSimple.IsKnownSimple E.H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHz)).mp
      ((E.input.source.simpleQTKE.twoLocal_sqtk
        (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one)).subgroup
          (E.H.subgroupOf (Gz E)))
  obtain ⟨hP,f,hgen,hbound,d,hm,hperm⟩ :=
    LocalGeometry.WeakClosure.Generation.hall_data D E.input hH hn
  obtain ⟨I,hI,_,hIT,_⟩ := ChapterE.Structure.source_original_component hQ
    (T.subtype hTH) hP hs
  let J := I.map E.H.subtype
  have hJ : (J.subgroupOf E.H).IsCComponent := by
    simpa only [J,subgroupOf,comap_map_eq_self_of_injective E.H.subtype_injective] using hI
  have hJT : J ⊔ (T : Subgroup G) = E.H := by
    have hh := congrArg (map E.H.subtype) hIT
    simpa only [Subgroup.map_sup,hPH,
      ← MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨J,map_subtype_le _,hJ,
    Chapter1.mem_L_of_cComponent hH.1.1.1
      ⟨T.subtype hTH,hPH⟩
      (map_subtype_le _) hJ,?_,hJT,?_⟩
  · intro hJM
    exact hH.1.2 (hJT ▸ sup_le hJM D.sylow_normalizes_component)
  · let := hI.perfect
    have hh := pResidual_eq_iSup_conjugates I (T.subtype hTH : Subgroup E.H)
      perfect_twoPerfect (T.subtype hTH).isPGroup' hIT
    rw [← conjugateSpanBy_eq_iSup_conj] at hh
    have hm := congrArg (map E.H.subtype) hh
    rw [map_conjugateSpanBy] at hm
    simpa only [hPH] using hm.symm

/-- The actual local component either lies in K or centralizes K/O₂(K).
The containing C-component is constructed inside Gz by source 1.2.4. -/
theorem local_component_alternative (h : Comparison.EarlierGeometry E)
    (he : E.Kz = E.K) {I : Subgroup G}
    (hI : I ∈ Chapter1.L G (T : Subgroup G)) (hIz : I ≤ Gz E) :
    I ≤ E.K ∨ ⁅E.K,I⁆ ≤ E.K.pCoreIn 2 := by
  let Z := Gz E
  let P := T.subtype h.sylow_le_pointCentralizer
  have hQ := E.input.source.simpleQTKE.twoLocal_sqtk
    (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one)
  have hQbar := ChapterE.Structure.sqtk_two_quotient hQ (pCore 2 Z) pCore_isPGroup
  have hI' : I.subgroupOf Z ∈ Chapter1.L Z (P : Subgroup Z) :=
    (Chapter1.mem_LIn_iff_subgroupOf h.sylow_le_pointCentralizer hIz).mp ⟨hIz,hI⟩
  obtain ⟨J,⟨hJ,hIJ⟩,_⟩ := Chapter1.Section02.index_le_two_local_component_source
    hQbar P le_rfl (by simp) hI'
  have hKz : E.K ≤ Z := he ▸ h.point_component.1
  have hK' : (E.K.subgroupOf Z).IsCComponent := he ▸ h.point_component.2
  by_cases hJK : J = E.K.subgroupOf Z
  · left
    intro i hi
    exact (hJK ▸ hIJ) (show (⟨i,hIz hi⟩ : Z) ∈ I.subgroupOf Z from hi)
  · right
    have hc : ⁅E.K.subgroupOf Z,I.subgroupOf Z⁆ ≤ (E.K.subgroupOf Z).pCoreIn 2 :=
      (commutator_mono le_rfl hIJ).trans
        ((ChapterA.Section03.CComponentCommutation.proposition_1_2_1_two
          hQbar hK' hJ (fun he => hJK he.symm)).1.trans inf_le_left)
    have hm := map_mono (f := Z.subtype) hc
    rw [map_commutator,map_subgroupOf_eq_of_le hKz,map_subgroupOf_eq_of_le hIz,
      map_pCoreIn_of_injective 2 _ Z.subtype Z.subtype_injective,
      map_subgroupOf_eq_of_le hKz] at hm
    exact hm

/-- In the equal-component row, containment is impossible because I escapes M.
Thus the genuine E.2.2 component centralizes L₁/O₂(L₁). -/
theorem equal_component_of_large_generation (h : Comparison.EarlierGeometry E)
    (he : E.Kz = E.K) (hK : E.K = E.L₁)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E)
    (hn : 1 < ChapterE.generationParameter E.H) :
    ∃ I : Subgroup G, I ≤ E.H ∧ (I.subgroupOf E.H).IsCComponent ∧
      I ∈ Chapter1.L G (T : Subgroup G) ∧ ¬ I ≤ E.M ∧
      I ⊔ (T : Subgroup G) = E.H ∧
      conjugateSpanBy I (T : Subgroup G) = (pResidual 2 E.H).map E.H.subtype ∧
      ⁅E.L₁,I⁆ ≤ E.L₁.pCoreIn 2 := by
  obtain ⟨I,hIH,hI,hlocal,hout,hjoin,hres⟩ := component_of_large_generation E h hH hHz hn
  have hc := local_component_alternative E h he hlocal (hIH.trans hHz)
  have hcomm := hc.resolve_left (fun hIK => hout
    (hIK.trans (hK ▸ E.L₁_le.trans L.le_normalizer)))
  refine ⟨I,hIH,hI,hlocal,hout,hjoin,hres,?_⟩
  simpa only [hK] using hcomm

/-- The same reduction on the original chosen flag, retaining the literal H. -/
theorem ofFlag_equal_component_of_large_generation
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    ∃ I : Subgroup G, I ≤ H ∧ (I.subgroupOf H).IsCComponent ∧
      I ∈ Chapter1.L G (T : Subgroup G) ∧ ¬ I ≤ normalizer (L : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧
      conjugateSpanBy I (T : Subgroup G) = (pResidual 2 H).map H.subtype ∧
      ⁅f.Li 0,I⁆ ≤ (f.Li 0).pCoreIn 2 :=
  equal_component_of_large_generation (ofFlag S f X z H) h he hK hH hHz hn

/-- The full two-residual centralizes the component quotient: T normalizes
the literal kernel, so the conclusion passes to the constructed T-orbit. -/
theorem equal_residual_le_point_kernel_of_large_generation
    (h : Comparison.EarlierGeometry E) (he : E.Kz = E.K) (hK : E.K = E.L₁)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E)
    (hn : 1 < ChapterE.generationParameter E.H) :
    (pResidual 2 E.H).map E.H.subtype ≤ Yz E := by
  obtain ⟨I,hIH,_,_,_,_,hr,hc⟩ := equal_component_of_large_generation E h he hK hH hHz hn
  have hIz := hIH.trans hHz
  have hIY : I ≤ Yz E := by
    refine le_inf hIz (coreCentralizer_of_commutator
      (hIz.trans (point_normalizes_component E he)) ?_)
    simpa only [hK,commutator_comm] using hc
  rw [← hr]
  exact conjugateSpanBy_le hIY
    (h.sylow_le_pointCentralizer.trans (point_normalizes_kernel E he))

open scoped Pointwise
open ChapterE ChapterB ChapterE.Section06.FixedPointBounds.ParabolicCartan

/-- The full constructed Hall actor is both faithful on V and in the actual
point quotient kernel. Only the separately owned odd-kernel normalizer input
is used for faithfulness; quotient centralization is proved here. -/
theorem equal_faithful_hall_in_point_kernel
    (h : Comparison.EarlierGeometry E) (he : E.Kz = E.K) (hK : E.K = E.L₁)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E)
    (hn : 1 < generationParameter E.H) :
    ∃ (hP : IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤) (f : ℕ),
      IsEGenerated f E.H ∧ generationParameter E.H ≤ f ∧
      ∃ d : IntrinsicHallCartanData (T.subtype hH.1.1.2) hP f,
        minimalParabolicMax (T.subtype hH.1.1.2) hP = E.M.subgroupOf E.H ∧
        (d.witness.abelianGroup.map E.H.subtype : Set G) * (T : Set G) =
          (T : Set G) * (d.witness.abelianGroup.map E.H.subtype : Set G) ∧
        d.witness.abelianGroup.map E.H.subtype ≤ Yz E ∧
        d.witness.abelianGroup.map E.H.subtype ⊓ centralizer (V : Set G) = ⊥ := by
  obtain ⟨hP,f,hg,hb,d,hm,hperm⟩ :=
    LocalGeometry.WeakClosure.Generation.hall_data D E.input hH hn
  have hBN : d.witness.abelianGroup ≤ pResidual 2 E.H := by
    intro b hb
    exact mem_pResidual_of_orderOf_coprime
      (d.witness.odd.coprime_two_left.of_dvd_right
        (d.witness.abelianGroup.orderOf_dvd_natCard hb))
  refine ⟨hP,f,hg,hb,d,hm,hperm,
    (map_mono hBN).trans
      (equal_residual_le_point_kernel_of_large_generation E h he hK hH hHz hn),?_⟩
  exact LocalGeometry.WeakClosure.Generation.hall_faithful D E.input hcontrol hH hn hP d hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
