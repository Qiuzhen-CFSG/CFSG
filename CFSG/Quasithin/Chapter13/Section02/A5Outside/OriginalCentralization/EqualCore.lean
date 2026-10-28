module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.PointCore
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveIntermediate.Source
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores

/-!
# Unequal point cores in the original 13.2.12 argument

The actual intermediate Q₂ contains O₂(LT), has a transposition image,
and satisfies LQ₂=LT. Apply the transposition branch of C.1.24 to the
literal marked module in LT. If Q₁=Q₂, every characteristic subgroup of
Baum(Q₂) normal in LT is trivial by the escaping first point group and
maximal-local uniqueness. C.1.24 would therefore make L an A₅ block,
contradicting the already proved original nonblock conclusion.

F.6.11 then constructs the Goldschmidt triple in the original O₃′ quotient,
preserves its common Sylow image and excludes cyclic order-two overlap.
SourceAssembly/EqualCore applies these conclusions to the universal terminal
argument. The remaining F.6.18 exclusions stay with qt-d-1367-assembly.
Source: Aschbacher--Smith 13.2.12, printed p.882; C.1.24, pp.130--131;
F.6.11, pp.306--307.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction Section06.CentralizerReduction.A5Module
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- C.1.24 on the actual intermediate point core, with the original action. -/
theorem point_core_characteristic_or_block
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥) :
    let K := L ⊔ (T : Subgroup G)
    let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let R := (P.pCoreIn 2).subgroupOf K
    (∃ C : Subgroup (ChapterB.baumann R), C.Characteristic ∧ C ≠ ⊥ ∧
      (C.map (ChapterB.baumann R).subtype).Normal) ∨ ChapterC.IsAlternatingBlock L 5 := by
  let K := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf K
  let U := V.subgroupOf K
  let P := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
  let R := (P.pCoreIn 2).subgroupOf K
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer (show L ≤ K from le_sup_left)).mpr
    (sup_le L.le_normalizer d.normalizes_L)
  let := d.reduced.normal
  let := d.reduced.elementary
  let a : A ≃* L := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (L ⧸ pCore 2 L) := IsQuasisimple.of_mulEquiv d.quotient.symm
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  have hpA : IsPPerfect 2 A := d.twoPerfect.of_surjective a.symm.toMonoidHom a.symm.surjective
  have hfA : generalizedFitting A = pCore 2 A := by
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_generalizedFitting_equiv,pCore_map_iso,d.characteristic_L]
  have hQne : K.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact d.hypothesis.local_component.1.2
      (((pCore 2 K).map_eq_bot_iff_of_injective K.subtype_injective).mp he)
  have hf : generalizedFitting K = pCore 2 K :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (d.hypothesis.qtke.evenCharacteristic T) ⟨hQne,fun _ hx => (le_sup_right : (T : Subgroup G) ≤ K) hx⟩))
  have hpR : IsPGroup 2 R := (isPGroup_pCoreIn 2 P).comap_subtype
  have hQR : pCore 2 K ≤ R := by
    intro x hx
    exact (point_core_bounds d hH hB hZ hs hz).1 (mem_map_of_mem K.subtype hx)
  have hgen : A ⊔ R = ⊤ := by
    rw [←subgroupOf_sup (show L ≤ K from le_sup_left)
      ((pCoreIn_le 2 P).trans (point_local_le d)),point_core_component_join d hH hB hZ hs hz]
    exact subgroupOf_self K
  let e : U ≃* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    (MulEquiv.multiplicativeAdditive U).symm.trans d.localModuleCoordinates.symm.toAddEquiv.toMultiplicative
  have he : ∀ (g : K) (v : U), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (d.localActor g) (e v).toAdd := by
    intro g v
    apply d.localModuleCoordinates.injective
    change d.localModuleCoordinates (d.localModuleCoordinates.symm
      (Additive.ofMul (MulAut.conjNormal g v))) = _
    rw [LinearEquiv.apply_symm_apply]
    have hh := d.localModuleCoordinates_equivariant g
      (d.localModuleCoordinates.symm (Additive.ofMul v))
    rw [LinearEquiv.apply_symm_apply] at hh
    exact (congrArg Additive.ofMul (Subtype.ext
      (NormalElementaryQuotient.representation_apply U d.localActor.rangeRestrict
        d.localActor.rangeRestrict_surjective
        (d.localActor.ker_rangeRestrict.trans d.localActor_kernel) g (Additive.ofMul v)))).symm.trans hh
  obtain ⟨r,hr,hR⟩ := point_core_image_transposition d hH hB hZ hs hz
  rcases ChapterC.RankOne.FiveIntermediate.normal_characteristic_or_alternatingBlock A U R
    hpA hf hfA hpR hQR hgen d.localActor (localActor_surjective_of_omega_movement d hH hZ)
    (d.localActor_kernel_eq_core d.normalizes_L) d.localActor_kernel d.localActor_component_image
    e he r hr hR with hc | hb
  · exact Or.inl hc
  · exact Or.inr (ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv a hb)


/-- Equal point cores would force the original component to be an A₅ block. -/
theorem point_cores_ne_of_nonblock
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (hb : ¬ ChapterC.IsAlternatingBlock L 5)
    {P₁ : Subgroup G} (hout : ¬ P₁ ≤ normalizer (L : Set G)) :
    P₁.pCoreIn 2 ≠
      (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 := by
  intro heq
  rcases point_core_characteristic_or_block d hH hB hZ hs hz with ⟨C,hC,hne,hn⟩ | hblock
  · exact equal_point_cores_no_characteristic_baumann d hout heq C hC hne hn
  · exact hb hblock

/-- The source hypotheses discharge the nonblock premise, so the original
point cores are unequal without an equality or block callback. -/
theorem point_cores_ne
    (hn : ∀ K ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (K : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    {P₁ : Subgroup G} (hout : ¬ P₁ ≤ normalizer (L : Set G)) :
    P₁.pCoreIn 2 ≠
      (Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)).pCoreIn 2 :=
  point_cores_ne_of_nonblock d hH hB hZ hs hz
    (local_nonblock_of_centerfree_outside d hn hH hB hZ hs hz) hout

/-- F.6.11 applied to the same point groups and the literal O₃′ quotient.
The preserved overlap is not cyclic of order two, excluding F.6.18(1). -/
theorem point_quotient_of_nonblock
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) (hz : center H = ⊥)
    (hb : ¬ ChapterC.IsAlternatingBlock L 5)
    {P₁ : Subgroup G} (hout : ¬ P₁ ≤ normalizer (L : Set G)) :
    let P₂ := Lv L (markedV d.flag.flag.module) ⊔ ChapterB.baumann (T : Subgroup G)
    let J := P₁ ⊔ P₂
    let A := P₁.subgroupOf J
    let B := P₂.subgroupOf J
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    P₁ ⊓ P₂ = ChapterB.baumann (T : Subgroup G) →
    ChapterF.IsGoldschmidtTriple A B →
    P₁.pCoreIn 2 ≠ P₂.pCoreIn 2 ∧
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      A.map q ⊓ B.map q = ((ChapterB.baumann (T : Subgroup G)).subgroupOf J).map q ∧
      pCore 2 (J ⧸ pPrimeCore 3 J) = ⊥ ∧
      ¬ Nonempty (((A.map q ⊓ B.map q) : Subgroup _) ≃* Multiplicative (ZMod 2)) := by
  intro P₂ J A B q hinter hg
  have hne := point_cores_ne_of_nonblock d hH hB hZ hs hz hb hout
  have hne' : A.pCoreIn 2 ≠ B.pCoreIn 2 := by
    intro he
    apply hne
    have hh := congrArg (map J.subtype) he
    rwa [map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,
      map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le (show P₁ ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show P₂ ≤ J from le_sup_right)] at hh
  have hi : A.map q ⊓ B.map q = (A ⊓ B).map q := by
    rcases hg.primeToThreeCore_dichotomy with hgood | hbad
    · exact hgood.1
    · exact (hne' (hbad.1.trans hbad.2.1.symm)).elim
  refine ⟨hne,hg.quotient_primeToThreeCore_of_distinct_cores hne',?_,
    hg.primeToThreeCore_quotient_twoCore_eq_bot,
    hg.primeToThreeCore_intersection_not_cyclic_two hne'⟩
  rw [hi]
  change ((P₁ ⊓ P₂).subgroupOf J).map q = _
  rw [hinter]

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
