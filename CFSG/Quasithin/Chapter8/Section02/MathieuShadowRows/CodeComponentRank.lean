module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SourceRanks
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# The original A₆ residual isolates the detected component

An A₆ projective section has three-rank at least two, even when its central
cover is nontrivial. The proved A.3.6 classification makes a containing
C-component quasisimple modulo its full two-core, with center of order at
most three. A solvable normal subgroup centralizes its image in the ambient
two-core quotient, and consequently has three-rank at most one.

The same rank argument identifies any component whose conjugate orbit
contains a rank-two subgroup with the original normal containing component.
Two commuting rank-two subgroups with intersection of order at most three
would force ambient three-rank at least three. No covering center is deleted.
The original Chapter12 application is `M22CodeComponentSieve`.

Source: Aschbacher--Smith 8.2.2(1), printed p.715, using A.2.12,
A.3.6--7 and 1.3.4, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G]

/-- An odd-rank-one source has cyclic Sylow three-subgroups, hence so does every quotient. -/
theorem three_rank_lower_of_surjective
    {B Q : Type*} [Group B] [Finite B] [Group Q] [Finite Q]
    (f : B →* Q) (hf : Function.Surjective f) (hr : 2 ≤ primeRank 3 Q) :
    2 ≤ primeRank 3 B := by
  by_contra hn
  let P : Sylow 3 B := Classical.choice inferInstance
  have hcyc := P.isCyclic_of_odd_of_primeRank_le_one (by decide)
    (show primeRank 3 B ≤ 1 by omega)
  have hq := P.primeRank_le_one_of_surjective hcyc f hf
  omega

/-- The full original two-core quotient retains three-rank at least two above its projective A₆ marking. -/
theorem projective_six_three_rank
    (e : ((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃*
      alternatingGroup (Fin 6)) : 2 ≤ primeRank 3 G := by
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (center (G ⧸ pCore 2 G))).comp
    (QuotientGroup.mk' (pCore 2 G)))
  exact three_rank_lower_of_surjective f
    (e.surjective.comp ((QuotientGroup.mk'_surjective _).comp
      (QuotientGroup.mk'_surjective _)))
    (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide))

/-- The actual containing C-component has a quasisimple two-core quotient with center of order at most three. -/
theorem rank_two_component_center_bound
    (hG : IsSQTK KnownSimple.IsKnownSimple G) {K : Subgroup G}
    (hK : K.IsCComponent) (hrK : 2 ≤ primeRank 3 K) :
    IsQuasisimple (K ⧸ pCore 2 K) ∧
      Nat.card (center (K ⧸ pCore 2 K)) ≤ 3 := by
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let e := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hG hK hrK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hB : IsComponent Q B := ⟨(hK.map_quotient _).subnormal,inferInstance⟩
  have hf : fittingSubgroup B ≤ center B :=
    (le_solvableRadical _ inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hm := (ChapterA.SQTKStructure.ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hQ B hB.isCComponent hf).2
  have hc := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common
    (ChapterA.SQTKStructure.OrdinarySource.ordinary_conclusion_of_model
      (pCore_quotient_pCore_eq_bot 2) B hB hm).2
  refine ⟨inferInstance,?_⟩
  rw [Nat.card_congr (centerCongr e).toEquiv]
  change Nat.card (center B) ≤ 3
  rcases hc with hc | hc <;> omega

/-- A normal solvable subgroup cannot carry a three-plane alongside the original rank-two component. -/
theorem solvable_normal_three_rank_le_one
    (hG : IsSQTK KnownSimple.IsKnownSimple G) {K : Subgroup G}
    (hK : K.IsCComponent) (hrK : 2 ≤ primeRank 3 K)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] : primeRank 3 N ≤ 1 := by
  obtain ⟨hqK,hzK⟩ := rank_two_component_center_bound hG hK hrK
  let := hqK
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let B := K.map q
  let A := N.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let e := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hB : IsComponent Q B := ⟨(hK.map_quotient _).subnormal,inferInstance⟩
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable A := Group.isSolvable_of_surjective (q.subgroupMap_surjective N)
  have hcomm : A ≤ centralizer (B : Set Q) :=
    le_centralizer_iff.mp (hB.le_centralizer_of_solvable_normal A)
  have hz : Nat.card (center B) ≤ 3 := by
    rwa [←Nat.card_congr (centerCongr e).toEquiv]
  have hker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hAr : primeRank 3 A = primeRank 3 N :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hker N
  have hBr : primeRank 3 B = primeRank 3 K :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hker K
  have hi : Nat.card (A ⊓ B : Subgroup Q) ≤ 3 := by
    let f : (A ⊓ B : Subgroup Q) →* center B := {
      toFun x := ⟨⟨x,x.property.2⟩,mem_center_iff.mpr (fun b =>
        Subtype.ext (hcomm x.property.1 b b.property))⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact (Nat.card_le_card_of_injective f (fun _ _ he => Subtype.ext
      (congrArg (fun x : center B => ((x : B) : Q)) he))).trans hz
  by_contra! hn
  have hl := three_le_primeRank_of_cubic_intersection A B hcomm hi
    (by omega : 2 ≤ primeRank 3 A) (by omega : 2 ≤ primeRank 3 B)
  have hu := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 G)
    pCore_isPGroup).trans (hG.stronglyQuasithin 3 (by decide) (by decide))
  omega

/-- A conjugate component orbit carrying a three-plane must come from the same normal rank-two component. -/
theorem rank_two_component_eq_of_orbit_contains_rank_two
    (hG : IsSQTK KnownSimple.IsKnownSimple G) {K B X T : Subgroup G}
    (hK : K.IsCComponent) [K.Normal] (hrK : 2 ≤ primeRank 3 K)
    (hB : B.IsCComponent) (hX : X ≤ componentOrbit B T) (hrX : 2 ≤ primeRank 3 X) :
    B = K := by
  by_contra hne
  obtain ⟨hqK,hzK⟩ := rank_two_component_center_bound hG hK hrK
  let := hqK
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let Kq := K.map q
  let Bq := B.map q
  let Xq := X.map q
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let e := cComponentTwoCoreQuotientEquiv hK
  let : IsQuasisimple Kq := IsQuasisimple.of_mulEquiv e
  let : Kq.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have hBK : Bq ≤ centralizer (Kq : Set Q) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    exact ChapterA.Section03.CComponentCommutation.commutator_eq_bot hQ
      (pCore_quotient_pCore_eq_bot 2) (hB.map_quotient _) (hK.map_quotient _)
      (fun he => hne (hB.eq_of_map_quotient_eq hK _ he))
  have hc : Xq ≤ centralizer (Kq : Set Q) := by
    have hx := map_mono (f := q) hX
    rw [map_componentOrbit] at hx
    exact hx.trans (iSup_conjugates_le_of_le_normalizer Bq (T.map q)
      (centralizer (Kq : Set Q)) hBK (by rw [normalizer_eq_top]; exact le_top))
  have hker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hXr : primeRank 3 Xq = primeRank 3 X :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hker X
  have hKr : primeRank 3 Kq = primeRank 3 K :=
    ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q hker K
  have hz : Nat.card (center Kq) ≤ 3 := by
    rwa [←Nat.card_congr (centerCongr e).toEquiv]
  have hi : Nat.card (Xq ⊓ Kq : Subgroup Q) ≤ 3 := by
    let f : (Xq ⊓ Kq : Subgroup Q) →* center Kq := {
      toFun x := ⟨⟨x,x.property.2⟩,mem_center_iff.mpr (fun b =>
        Subtype.ext (hc x.property.1 b b.property))⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact (Nat.card_le_card_of_injective f (fun _ _ he => Subtype.ext
      (congrArg (fun x : center Kq => ((x : Kq) : Q)) he))).trans hz
  have hl := three_le_primeRank_of_cubic_intersection Xq Kq hc hi
    (by omega : 2 ≤ primeRank 3 Xq) (by omega : 2 ≤ primeRank 3 Kq)
  have hu := hQ.stronglyQuasithin 3 (by decide) (by decide)
  change primeRank 3 Q ≥ 3 at hl
  omega

end CFSG.Quasithin.Chapter8.MathieuShadowRows
