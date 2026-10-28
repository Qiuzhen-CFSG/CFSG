module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.PermutationTransport
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MarkedExtension
public import Theory.SpecificGroups.SymmetricEight.MarkedFlagTransport
public import Theory.SpecificGroups.SymmetricEight.PairFlagParabolic

/-!
# Converting the outer middle node to a simultaneous eight-point marking

A basis change aligns the supplied middle parabolic with the middle parabolic
of an exceptional comparison. The faithful conjugation action on the normal,
self-centralizing A₈ component then extends this exact component marking to
S₈. The genuine quotient-kernel containment transports intersections, and the
normalizer of the even pair subgroup places the Sylow image in the full pair
stabilizer. Its odd element recovers the entire extended intersection.
Finally Sylow conjugacy inside that stabilizer marks the same literal nested
flag while preserving both the component and extended intersection.

`eightFlagComparison` uses the actual exceptional equivalence and the basis
(e₀+e₁,e₁,e₂+e₃,e₃) to mark both literal partitions simultaneously.
`middleNodeFlagMarking_of_outerMiddleNodeData` supplies this comparison to
the transport construction, completing the conversion from the intrinsic
outer middle-node data. The source classification must still construct that
input and supply the earlier relative normality, Sylow and kernel facts.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.27(4), 15.3.28(3), and 15.3.32(4), printed pp.1130–1133.
-/

@[expose] public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
variable {G : Type*} [Group G]

/-- The actual simultaneous middle/end comparison on the literal pair and
four-point partitions, retaining one exceptional equivalence and one basis. -/
noncomputable def eightFlagComparison : EightFlagComparison where
  equiv := Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.equiv
  basis := Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.basis
  middle := Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.middle
  ends := Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.ends

private theorem component_equiv_of_comparison
    (d : LocalData G) {I L : Subgroup G} (h : OuterMiddleNodeData d I L)
    (cmp : EightFlagComparison) :
    ∃ e : d.starImage I L ≃* alternatingGroup (Fin 8),
      ((d.starImage I (d.M ⊓ L)).subgroupOf (d.starImage I L)).map e.toMonoidHom =
        pairStabilizer.subgroupOf (alternatingGroup (Fin 8)) := by
  let g : LinearGroup 4 := h.basis.equiv cmp.basis (Equiv.refl _)
  have hb : h.basis.map g = cmp.basis := by ext i; simp [g]
  let e := h.linear.trans ((MulAut.conj g).trans cmp.equiv.symm)
  refine ⟨e, ?_⟩
  change (((d.starImage I (d.M ⊓ L)).subgroupOf (d.starImage I L)).map
    (cmp.equiv.symm.toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp h.linear.toMonoidHom))) = _
  rw [← map_map, ← map_map, h.intersection]
  have hg : (minimalParabolic h.basis 1).map (MulAut.conj g).toMonoidHom =
      minimalParabolic cmp.basis 1 := by
    unfold minimalParabolic
    rw [cutStabilizer_map_conj, hb]
  rw [hg]
  exact (map_symm_eq_iff_map_eq _).mpr cmp.middle

/-- The ambient S₈ marking before conjugating the common Sylow subgroup. -/
private theorem permutation_equiv_of_comparison
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (h : OuterMiddleNodeData d I c.L) (cmp : EightFlagComparison) :
    ∃ e : d.Star I ≃* S8,
      (d.starImage I c.L).map e.toMonoidHom = alternatingGroup (Fin 8) ∧
      (d.starImage I (d.MI I)).map e.toMonoidHom = pairStabilizer := by
  let K := d.starImage I c.L
  let J := d.starImage I (d.M ⊓ c.L)
  let Q := d.starImage I (d.MI I)
  let T := d.starImage I d.S
  let _ : K.Normal := hn.map (d.starMap I) (QuotientGroup.mk'_surjective _)
  have hK : K ≠ ⊤ := by
    intro ht
    apply h.outer
    change T ≤ K
    rw [ht]
    exact le_top
  obtain ⟨eK, heK⟩ := component_equiv_of_comparison d h cmp
  let e : d.Star I ≃* S8 := symmetricExtension K eK h.selfCentralizing hK
  have heL : K.map e.toMonoidHom = alternatingGroup (Fin 8) :=
    symmetricExtension_map K eK h.selfCentralizing hK
  have hJK : J ≤ K := map_mono (comap_mono inf_le_right)
  have hcomm : e.toMonoidHom.comp K.subtype =
      (alternatingGroup (Fin 8)).subtype.comp eK.toMonoidHom := by
    apply MonoidHom.ext
    intro k
    exact symmetricExtension_on_subgroup K eK h.selfCentralizing hK k
  have heJ : J.map e.toMonoidHom = pairStabilizer ⊓ alternatingGroup (Fin 8) := by
    calc
      J.map e.toMonoidHom = ((J.subgroupOf K).map K.subtype).map e.toMonoidHom := by
        rw [map_subgroupOf_eq_of_le hJK]
      _ = ((J.subgroupOf K).map eK.toMonoidHom).map (alternatingGroup (Fin 8)).subtype := by
        rw [map_map, hcomm, ← map_map]
      _ = pairStabilizer ⊓ alternatingGroup (Fin 8) := by
        rw [heK, subgroupOf_map_subtype]
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hSQ : T ≤ Q := map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) hSI))
  have hTN : T ≤ normalizer (J : Set (d.Star I)) := by
    have he : J = K ⊓ Q := component_intersection_star_eq_inf d c hc
    rw [he]
    exact (le_inf (le_normalizer_of_normal : T ≤ normalizer (K : Set (d.Star I)))
      (hSQ.trans Q.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have heT : T.map e.toMonoidHom ≤ pairStabilizer := by
    have hh := (map_mono hTN).trans (J.le_normalizer_map e.toMonoidHom)
    rwa [heJ, normalizer_evenPair] at hh
  have hodd : ¬ T.map e.toMonoidHom ≤ alternatingGroup (Fin 8) := by
    intro ht
    apply h.outer
    intro x hx
    have hxmap : e x ∈ K.map e.toMonoidHom := by
      rw [heL]
      exact ht ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hey⟩ := hxmap
    exact e.injective hey ▸ hy
  refine ⟨e, heL, ?_⟩
  rw [intersection_star_eq_component_intersection_sup d c hn hI, Subgroup.map_sup, heJ]
  exact evenPair_sup_of_odd heT hodd

/-- Given the simultaneous exceptional comparison, construct all component,
extended-intersection, and common Sylow markings under the original quotient. -/
theorem middleNodeFlagMarking_of_comparison [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (h : OuterMiddleNodeData d I c.L) (cmp : EightFlagComparison) :
    Nonempty (MiddleNodeFlagMarking d I c.L) := by
  obtain ⟨e, heL, heM⟩ := permutation_equiv_of_comparison d c hn hI hc h cmp
  let Q : Sylow 2 (d.Star I) := P.mapSurjective (QuotientGroup.mk'_surjective _)
  have hQ : (Q : Subgroup (d.Star I)) = d.starImage I d.S := by
    change (P : Subgroup I).map (d.starMap I) = (d.S.subgroupOf I).map (d.starMap I)
    congr 1
    apply map_injective I.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (hP ▸ map_subtype_le (P : Subgroup I))]
  let T : Sylow 2 S8 := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : (T : Subgroup S8) = (d.starImage I d.S).map e.toMonoidHom := by
    change (Q : Subgroup (d.Star I)).map e.toMonoidHom = _
    rw [hQ]
  have hSI : d.S ≤ I := hI ▸ le_sup_right
  have hTM : (T : Subgroup S8) ≤ pairStabilizer := by
    rw [hT, ← heM]
    exact map_mono (map_mono (comap_mono (le_inf (inf_le_left.trans d.sylow_le) hSI)))
  obtain ⟨q, hq, hqT⟩ := sylow_pair_alignment_of_borel cmp.equiv cmp.basis cmp.borel T hTM
  let f := e.trans (MulAut.conj q)
  have hfL : (d.starImage I c.L).map f.toMonoidHom = alternatingGroup (Fin 8) := by
    change (d.starImage I c.L).map ((MulAut.conj q).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, heL]
    exact Normal.map_conj_eq _ q
  have hfM : (d.starImage I (d.MI I)).map f.toMonoidHom = pairStabilizer := by
    change (d.starImage I (d.MI I)).map ((MulAut.conj q).toMonoidHom.comp e.toMonoidHom) = _
    rw [← map_map, heM]
    exact mem_normalizer_iff_map_conj_eq.mp (pairStabilizer.le_normalizer hq)
  refine ⟨{ toMiddleNodePermutationMarking := middleNodePermutationMarkingOfExtended d c hc f hfL hfM
            comparison := cmp
            sylow := ?_ }⟩
  change (d.starImage I d.S).map ((MulAut.conj q).toMonoidHom.comp e.toMonoidHom) = _
  rw [← map_map, ← hT]
  exact hqT

/-- Convert the intrinsic outer middle node into an actual S₈ marking of the
component, both intersections and the common Sylow flag. The simultaneous
exceptional comparison is constructed here, with no additional geometry premise. -/
theorem middleNodeFlagMarking_of_outerMiddleNodeData [Finite G]
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hn : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hc : I ⊓ centralizer (d.UI I : Set G) ≤ d.MI I)
    (h : OuterMiddleNodeData d I c.L) :
    Nonempty (MiddleNodeFlagMarking d I c.L) :=
  middleNodeFlagMarking_of_comparison d c hn hI P hP hc h eightFlagComparison

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics
