module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightQuotient
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.LinearCore
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Suzuki.Core
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import Theory.GroupTheory.ComponentLocalOrbitCore
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.StarCoordinates

-- Internal source-coordinate bridge: unfold the original maximal-core definition.
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original exchanged component, its Borel and its overlap core

Pass through the literal source kernel, which equals O₂(X) in the exchanged
row. The component is simple in that quotient. The orbit of its Borel
root group lies in the maximal-subgroup two-core; the two-component Sylow
product then includes the entire residual Sylow intersection. These
containments lift through the same two-group kernel.

The linear and Suzuki core calculations prevent that core from exchanging
the components. Rank-one Sylow-normalizer uniqueness gives the original
Borel intersection, and the source component orbit gives normalizer index
two. These are the geometric inputs to the prime-pair constructor in
`RankOneModuleGenericExceptionalCartanGlobalPrimeExchangedSelection`.
The component is not identified with the full residual.

Source: Aschbacher–Smith E.2.2(1a), E.2.7, 5.1.10–11 and 5.2.2,
printed pp.215–216,218–219,634–635,646–648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

private theorem component_root_le_core (T : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) {C : Subgroup X}
    (hC : IsComponent X C) [IsSimpleGroup C] (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hqt : IsStronglyQuasithin X) (hm : ChapterF.Source.IsRankOneModel C)
    (hj : (ChapterB.minimalParabolicMax T hP ⊓ C) ⊔ (T : Subgroup X) =
      ChapterB.minimalParabolicMax T hP) :
    (T : Subgroup X) ⊓ C ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2 := by
  let M := ChapterB.minimalParabolicMax T hP
  have heven : 2 ∣ Nat.card C := by
    by_contra hn
    let := hC.2
    exact Group.IsPerfect.not_isSolvable C (odd_order_theorem C
      (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)))
  have hb := ChapterE.Witnesses.PairedBender.component_borel_intersection T hP C hC heven
    (ChapterE.Structure.generating_component_orbit_eq_residual hqt T hC hgen) hm
  obtain ⟨P,hP'⟩ := T.exists_subgroupOf_eq_of_subnormal C hC.1
  have hmP : (P : Subgroup C).map C.subtype = (T : Subgroup X) ⊓ C := by
    rw [hP',subgroupOf_map_subtype]
  have hf := ChapterF.Source.rankOneBorelFacts_of_sylow C (T : Subgroup X) P hmP
    (hm.rankOneSylowFacts P)
  have hb' : M ⊓ C = ChapterF.Source.borel C (T : Subgroup X) := by
    have hh := congrArg (Subgroup.map C.subtype) hb
    rw [subgroupOf_map_subtype] at hh
    rw [← inf_subgroupOf_right (T : Subgroup X) C,
      ← subgroupOf_normalizer_eq (show (T : Subgroup X) ⊓ C ≤ C from inf_le_right),
      subgroupOf_map_subtype] at hh
    simpa only [ChapterF.Source.borel,inf_comm] using hh
  have hc : (M ⊓ C).pCoreIn 2 = (T : Subgroup X) ⊓ C := by
    rw [hb']
    exact hf.twoCore_eq
  have hi : (T : Subgroup X) ⊓ normalizer (C : Set X) ≤ normalizer (M ⊓ C : Set X) :=
    (le_inf (inf_le_left.trans ((ChapterB.minimalParabolicMax_spec T hP).2.trans M.le_normalizer))
      inf_le_right).trans inf_normalizer_le_normalizer_inf
  have hh := (le_componentOrbit ((M ⊓ C).pCoreIn 2) (T : Subgroup X)).trans
    (hC.local_core_orbit_le (p := 2) (show M ⊓ C ≤ C from inf_le_right) hi)
  rwa [hj,hc] at hh

private theorem component_residual_root_le_core (T : Sylow 2 X)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) {C : Subgroup X}
    (hC : IsComponent X C) (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hqt : IsStronglyQuasithin X)
    (hroot : (T : Subgroup X) ⊓ C ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2) :
    (T : Subgroup X) ⊓ pResidual 2 X ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2 := by
  rcases ChapterE.Structure.component_normal_or_pair hqt T hC hgen with
    ⟨_,he⟩ | ⟨t,hne,hD,hcomm,hN,hR,_,_⟩
  · rwa [he]
  · let M := ChapterB.minimalParabolicMax T hP
    let D := C.map (MulAut.conj (t : X)).toMonoidHom
    let N := C ⊔ D
    let := hN
    have hCN : (C.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le C.le_normalizer ((commutator_eq_bot_iff_le_centralizer.mp
        (by rw [commutator_comm];exact hcomm)).trans (Subgroup.centralizer_le_normalizer _)))
    have hDN : (D.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)) D.le_normalizer)
    let := hCN
    let := hDN
    have he := T.inf_sup_eq_sup_inf_relative N C D le_sup_left le_sup_right rfl
    rw [hR,he]
    refine sup_le hroot ?_
    have htT : (T : Subgroup X).map (MulAut.conj (t : X)).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup X).le_normalizer t.property)
    have htM := (ChapterB.minimalParabolicMax_spec T hP).2 t.property
    have htQ := (M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M))) htM
    have heQ : (M.pCoreIn 2).map (MulAut.conj (t : X)).toMonoidHom = M.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp htQ
    have hh := map_mono (f := (MulAut.conj (t : X)).toMonoidHom) hroot
    rwa [Subgroup.map_inf _ _ _ (MulAut.conj (t : X)).injective,htT,heQ] at hh

/-- The original maximal-subgroup two-core fixes the exchanged component. -/
theorem exchanged_core_normalizes (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hc : ExchangedClauses (ChapterB.minimalParabolicMax T hP) C T)
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) C f) :
    (ChapterB.minimalParabolicMax T hP).pCoreIn 2 ≤ normalizer (C : Set X) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hs : ¬ Group.IsSolvable X := fun hx => hC.not_isSolvable
    (by let := hx; infer_instance)
  have hi := ChapterE.Structure.source_component_simple_image T hP hs C hC hgen
  change IsSimpleGroup (C.map q) ∧ IsComponent (X ⧸ J) (C.map q) ∧
    ¬ IsMulCommutative (C.map q) ∧ C.map q ⊔ (S : Subgroup (X ⧸ J)) = ⊤ at hi
  let : IsSimpleGroup (C.map q) := hi.1
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
    (ChapterE.Structure.source_star_minimal_core_free T hP).1
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  have hrad : solvableRadical (X ⧸ J) = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical S hmin
      (fun hh => hi.2.1.isCComponent.not_isSolvable
        (by let := hh; infer_instance))).symm.trans
        (ChapterE.Structure.source_star_minimal_core_free T hP).2
  have hqt : IsStronglyQuasithin (X ⧸ J) := (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
    hX T hP hs).stronglyQuasithin
  have ho := ChapterE.Structure.generating_component_orbit_eq_residual hqt S hi.2.1 hi.2.2.2
  have hn : (ChapterB.minimalParabolicMax S hmin).pCoreIn 2 ≤
      normalizer (C.map q : Set (X ⧸ J)) := by
    rcases hm with ⟨F,_,_,_,hf,hF,e,_⟩ | ⟨m,hm,_,e,_⟩
    · exact ChapterE.Witnesses.PairedBender.core_normalizes_linear_component
        (by omega) hF S hmin _ hi.2.1 hi.2.1.isCComponent hrad ho
        (e.trans (Matrix.SpecialLinearGroup.TwoConjugateWitness.slEquivPSL F).symm)
    · exact ChapterE.Witnesses.PairedBender.Suzuki.core_normalizes_component
        S hmin _ hi.2.1 hrad ho (by omega) e
  rw [hmax, ← map_pCoreIn_of_ker_isPGroup q (by
    rw [QuotientGroup.ker_mk'];change IsPGroup 2 (sourceKernel M)
    rw [hc.kernel_eq];exact pCore_isPGroup)] at hn
  have hh := map_le_iff_le_comap.mp hn
  let : Group.IsSolvable J := by
    change Group.IsSolvable (sourceKernel M)
    rw [hc.kernel_eq]
    let := pCore_isPGroup (p := 2) (G := X) |>.isNilpotent
    infer_instance
  rwa [normalizer_cComponent_quotient hC J] at hh

/-- The full residual Sylow intersection lies in the original maximal two-core. -/
theorem exchanged_residual_sylow_le_core (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hc : ExchangedClauses (ChapterB.minimalParabolicMax T hP) C T)
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) C f) :
    (T : Subgroup X) ⊓ pResidual 2 X ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2 := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hs : ¬ Group.IsSolvable X := fun hx => hC.not_isSolvable
    (by let := hx; infer_instance)
  have hi := ChapterE.Structure.source_component_simple_image T hP hs C hC hgen
  change IsSimpleGroup (C.map q) ∧ IsComponent (X ⧸ J) (C.map q) ∧
    ¬ IsMulCommutative (C.map q) ∧ C.map q ⊔ (S : Subgroup (X ⧸ J)) = ⊤ at hi
  let : IsSimpleGroup (C.map q) := hi.1
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
    (ChapterE.Structure.source_star_minimal_core_free T hP).1
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  have hqt : IsStronglyQuasithin (X ⧸ J) := (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
    hX T hP hs).stronglyQuasithin
  have hmodel : ChapterF.Source.IsRankOneModel (C.map q) := by
    rcases hm with ⟨F,_,_,_,hf,hF,e,_⟩ | ⟨m,_,_,e,_⟩
    · exact .linear f (by omega) ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
    · exact .suzuki m ⟨e⟩
  have hj : (ChapterB.minimalParabolicMax S hmin ⊓ C.map q) ⊔ (S : Subgroup (X ⧸ J)) =
      ChapterB.minimalParabolicMax S hmin := by
    rw [hmax]
    change (M.map q ⊓ C.map q) ⊔ (T : Subgroup X).map q = M.map q
    have he : (M ⊓ C).map q = M.map q ⊓ C.map q := ExchangedHall.source_overlap_eq M C
    rw [← he, ← Subgroup.map_sup,
      ExchangedHall.exchanged_join hc (ChapterB.minimalParabolicMax_spec T hP).2]
  have hr := component_residual_root_le_core S hmin hi.2.1 hi.2.2.2 hqt
    (component_root_le_core S hmin hi.2.1 hi.2.2.2 hqt hmodel hj)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk'];change IsPGroup 2 (sourceKernel M)
    rw [hc.kernel_eq];exact pCore_isPGroup
  rw [hmax, ← map_pCoreIn_of_ker_isPGroup q hk] at hr
  obtain ⟨P,hP'⟩ := T.exists_subgroupOf_eq_of_subnormal (pResidual 2 X)
    (Subgroup.Normal.isSubnormal inferInstance)
  have hmP : (P : Subgroup (pResidual 2 X)).map (pResidual 2 X).subtype =
      (T : Subgroup X) ⊓ pResidual 2 X := by rw [hP',subgroupOf_map_subtype]
  have him := T.map_image_eq_inf _ _ P hmP inf_le_left q
  rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective J)] at him
  have hh := map_le_iff_le_comap.mp (him.le.trans hr)
  have hkM : q.ker ≤ M.pCoreIn 2 := le_pCoreIn_of_normalizes hk
    (by rw [QuotientGroup.ker_mk'];exact M.normalCore_le) le_normalizer_of_normal
  rwa [comap_map_eq,sup_eq_left.mpr hkM] at hh

/-- The actual component Borel is exactly its intersection with the original maximal subgroup. -/
theorem exchanged_component_borel (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hc : ExchangedClauses (ChapterB.minimalParabolicMax T hP) C T)
    (hm : ExchangedModel (ChapterB.minimalParabolicMax T hP) C f) :
    ChapterF.Source.borel C (T : Subgroup X) = ChapterB.minimalParabolicMax T hP ⊓ C := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := sourceKernel M
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  have hs : ¬ Group.IsSolvable X := fun hx => hC.not_isSolvable
    (by let := hx; infer_instance)
  have hi := ChapterE.Structure.source_component_simple_image T hP hs C hC hgen
  change IsSimpleGroup (C.map q) ∧ IsComponent (X ⧸ J) (C.map q) ∧
    ¬ IsMulCommutative (C.map q) ∧ C.map q ⊔ (S : Subgroup (X ⧸ J)) = ⊤ at hi
  let : IsSimpleGroup (C.map q) := hi.1
  let := hi.2.1.2
  have heven : 2 ∣ Nat.card (C.map q) := by
    by_contra hn
    exact Group.IsPerfect.not_isSolvable (C.map q) (odd_order_theorem _
      (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hn)))
  have hmin : ChapterB.IsMinimalParabolicOver S ⊤ :=
    (ChapterE.Structure.source_star_minimal_core_free T hP).1
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'];exact le_rfl)).symm
  have hqt : IsStronglyQuasithin (X ⧸ J) := (ChapterE.Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple
    hX T hP hs).stronglyQuasithin
  have hmodel : ChapterF.Source.IsRankOneModel (C.map q) := by
    rcases hm with ⟨F,_,_,_,hf,hF,e,_⟩ | ⟨m,_,_,e,_⟩
    · exact .linear f (by omega) ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩
    · exact .suzuki m ⟨e⟩
  have hb := ChapterE.Witnesses.PairedBender.component_borel_intersection S hmin _ hi.2.1 heven
    (ChapterE.Structure.generating_component_orbit_eq_residual hqt S hi.2.1 hi.2.2.2) hmodel
  rw [hmax] at hb
  obtain ⟨P,hP'⟩ := T.exists_subgroupOf_eq_of_subnormal C hC.subnormal
  have hmP : (P : Subgroup C).map C.subtype = (T : Subgroup X) ⊓ C := by
    rw [hP',subgroupOf_map_subtype]
  have hmap := T.map_image_eq_inf _ _ P hmP inf_le_left q
  have hBM : ChapterF.Source.borel C (T : Subgroup X) ≤ M := by
    intro x hx
    have hxC : q x ∈ C.map q := mem_map_of_mem q hx.1
    have hxN : q x ∈ normalizer (((T : Subgroup X) ⊓ C).map q : Set (X ⧸ J)) :=
      ((T : Subgroup X) ⊓ C).le_normalizer_map q (mem_map_of_mem q hx.2)
    rw [hmap] at hxN
    have hz : (⟨q x,hxC⟩ : C.map q) ∈ (M.map q).subgroupOf (C.map q) := by
      rw [hb, ← inf_subgroupOf_right (S : Subgroup (X ⧸ J)) (C.map q),
        ← subgroupOf_normalizer_eq inf_le_right]
      exact hxN
    have hpre : (M.map q).comap q = M := comap_map_eq_self
      (by rw [QuotientGroup.ker_mk'];exact M.normalCore_le)
    exact hpre ▸ (show x ∈ (M.map q).comap q from hz)
  have hf := ChapterF.Source.rankOneBorelFacts_of_sylow C (T : Subgroup X) P hmP
    (ChapterF.Source.rankOneSylowFacts_of_rankOneQuotient
      (Global.exchanged_component_quotient hC hc hm) P)
  apply le_antisymm (le_inf hBM inf_le_left)
  apply hf.unique_maximal
  · exact inf_le_inf (ChapterB.minimalParabolicMax_spec T hP).2 le_rfl
  · apply lt_of_le_of_ne inf_le_right
    intro he
    have hCM : C ≤ M := he ▸ inf_le_left
    exact (ChapterB.minimalParabolicMax_spec T hP).1.ne_top
      (top_unique (hgen ▸ sup_le hCM (ChapterB.minimalParabolicMax_spec T hP).2))

/-- The genuine exchanged source component has normalizer of index two. -/
theorem exchanged_normalizer_index (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (T : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    {C : Subgroup X} (hC : C.IsCComponent) (hgen : C ⊔ (T : Subgroup X) = ⊤)
    (hc : ExchangedClauses (ChapterB.minimalParabolicMax T hP) C T) :
    (normalizer (C : Set X)).index = 2 := by
  have hs : ¬ Group.IsSolvable X := fun hx => hC.not_isSolvable
    (by let := hx; infer_instance)
  rcases ChapterE.Structure.source_original_component_normal_or_index_two
    ChapterA.Section02.theoremA_knownSimple hX T hP hs C hC hgen with hn | hi
  · let := hn
    obtain ⟨t,_,hne,_⟩ := hc.exchanged_product
    exact (hne (mem_normalizer_iff_map_conj_eq.mp
      (show t⁻¹ ∈ normalizer (C : Set X) by rw [normalizer_eq_top];exact mem_top _)).symm).elim
  · exact hi

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
