module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage.Indices
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.Classification
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DerivedCoordinates

/-!
# Arbitrary-radical small movers through the original quotient

Kernel saturation and the literal natural-cover index identify the original
maximum-small-mover family with the maximum family in Sylow coordinates.
The correspondence is bijective, preserving the actual family cardinality.
Two distinct original movers therefore force the radical image to be the
point radical, give exactly five original movers, and make their join equal
to the whole original radical, including its two-kernel.

Source: Meierfrankenfeld–Stellmacher (1993), (5.4)(b), printed p.915. The
quotient, conjugation representation and central-cover projection are literal
inputs supplied by the initial recognition. The coordinate-range premise
records the chosen containing Sylow; it does not require the radical itself
to be Sylow or elementary abelian.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
open Representation.SymplecticFourOrthogonalCover
namespace ModelSmallMovers
open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {K G : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] [Finite V]
variable (q : G →* L (K := K)) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))
variable (p : (NormalElementaryQuotient.representation V q hq hker).IntertwiningMap
  (binaryNatural (K := K))) (hp : IsCover p)
variable (hK : Nat.card K=4)

noncomputable def coordinates (E : Subgroup G) : Subgroup (unipotent (F := K)) :=
  (E.map q).comap (derivedEmbedding (by omega : 2<Nat.card K))

omit [V.Normal] [IsElementaryAbelian 2 V] [Finite V] [Algebra (ZMod 2) K] [Finite G] in
theorem coordinates_map (E : Subgroup G)
    (hE : E.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range) :
    (coordinates q hK E).map (derivedEmbedding (by omega : 2<Nat.card K))=E.map q :=
  map_comap_eq_self hE

include hp in
theorem maximal_coordinates (T E : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hE : E ∈ Subgroup.SmallMover.Maximal V q.ker T 16) :
    coordinates q hK E ∈ Maximal (coordinates q hK T) := by
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  have hi : Function.Injective i := derivedEmbedding_injective _
  have he := (maximalMover_iff_natural V q hq hker p hp T E 16 hkT).mp hE
  have hEi : E.map q ≤ i.range := (map_mono he.2.1).trans hT
  have hEm : (coordinates q hK E).map i=E.map q := coordinates_map q hK E hEi
  have hTm : (coordinates q hK T).map i=T.map q := coordinates_map q hK T hT
  have hcardE : Nat.card (E.map q)=Nat.card (coordinates q hK E) := by
    rw [←hEm,card_map_of_injective hi]
  have hindexE : 2^fixedCodim binaryNatural (E.map q)=movingIndex (coordinates q hK E) := by
    rw [←hEm]
    exact derivedEmbedding_movingIndex _ _
  refine ⟨comap_mono (map_mono he.2.1),?_,?_⟩
  · exact ⟨by simpa only [hcardE,hindexE] using he.2.2.1,
      by simpa only [hindexE] using he.2.2.2.1⟩
  · intro A hA hsmall
    have him : A.map i ≤ T.map q := (map_mono hA).trans_eq hTm
    have hm := he.2.2.2.2 (A.map i) him
    have hindex : 2^fixedCodim binaryNatural (A.map i)=movingIndex A :=
      derivedEmbedding_movingIndex _ _
    have hc : Nat.card (A.map i)=Nat.card A := card_map_of_injective hi
    rw [hindex,hc,hcardE] at hm
    exact hm hsmall.1 hsmall.2

omit [V.Normal] [IsElementaryAbelian 2 V] [Finite V] [Algebra (ZMod 2) K] [Finite G] in
theorem coordinates_injective_on_saturated {E A : Subgroup G}
    (hEk : q.ker ≤ E) (hAk : q.ker ≤ A)
    (hEi : E.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hAi : A.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (he : coordinates q hK E=coordinates q hK A) : E=A := by
  have hm := congrArg (fun B => B.map (derivedEmbedding (by omega : 2<Nat.card K))) he
  rw [coordinates_map q hK E hEi,coordinates_map q hK A hAi] at hm
  have hh := congrArg (fun B => B.comap q) hm
  simpa only [comap_map_eq_self hEk,comap_map_eq_self hAk] using hh

include hp in
theorem two_maximal_radical_image (T E A : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hE : E ∈ Subgroup.SmallMover.Maximal V q.ker T 16)
    (hA : A ∈ Subgroup.SmallMover.Maximal V q.ker T 16) (hne : E ≠ A) :
    T.map q = (CentralRootGeometry.wing (F := K) false).map
      (derivedEmbedding (by omega : 2<Nat.card K)) := by
  have hEc := maximal_coordinates V q hq hker p hp hK T E hkT hT hE
  have hAc := maximal_coordinates V q hq hker p hp hK T A hkT hT hA
  have hkerE := (maximalMover_iff_natural V q hq hker p hp T E 16 hkT).mp hE |>.1
  have hkerA := (maximalMover_iff_natural V q hq hker p hp T A 16 hkT).mp hA |>.1
  have hne' : coordinates q hK E ≠ coordinates q hK A := by
    intro he
    exact hne (coordinates_injective_on_saturated q hK hkerE hkerA
      ((map_mono hE.1.1).trans hT) ((map_mono hA.1.1).trans hT) he)
  have hmodel := two_maximal_force_point_wing hK hEc hAc hne'
  rw [←coordinates_map q hK T hT,hmodel]
include hp in
theorem maximal_of_coordinates (T E : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hEk : q.ker ≤ E) (hET : E ≤ T)
    (hE : coordinates q hK E ∈ Maximal (coordinates q hK T)) :
    E ∈ Subgroup.SmallMover.Maximal V q.ker T 16 := by
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  have hi : Function.Injective i := derivedEmbedding_injective _
  have hEi : E.map q ≤ i.range := (map_mono hET).trans hT
  have hEm : (coordinates q hK E).map i=E.map q := coordinates_map q hK E hEi
  have hcardE : Nat.card (E.map q)=Nat.card (coordinates q hK E) := by
    rw [←hEm,card_map_of_injective hi]
  have hindexE : 2^fixedCodim binaryNatural (E.map q)=movingIndex (coordinates q hK E) := by
    rw [←hEm]
    exact derivedEmbedding_movingIndex _ _
  apply (maximalMover_iff_natural V q hq hker p hp T E 16 hkT).mpr
  refine ⟨hEk,hET,?_,?_,?_⟩
  · simpa only [hindexE,hcardE] using hE.2.1.1
  · simpa only [hindexE] using hE.2.1.2
  · intro A hAT hm hb
    have hAi : A ≤ i.range := hAT.trans hT
    have hAm : (A.comap i).map i=A := map_comap_eq_self hAi
    have hindex : 2^fixedCodim binaryNatural A=movingIndex (A.comap i) := by
      have hh := derivedEmbedding_movingIndex (F := K) (by omega : 2<Nat.card K) (A.comap i)
      change 2^fixedCodim binaryNatural ((A.comap i).map i)=movingIndex (A.comap i) at hh
      rw [hAm] at hh
      exact hh
    have hcard : Nat.card A=Nat.card (A.comap i) := by
      have hh := card_map_of_injective (K := A.comap i) hi
      rwa [hAm] at hh
    rw [hindex,hcard] at hm
    rw [hindex] at hb
    rw [hcard,hcardE]
    exact hE.2.2 _ (comap_mono hAT) ⟨hm,hb⟩

include hp in
theorem maximal_coordinates_bijective (T : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range) :
    Function.Bijective (fun E : Subgroup.SmallMover.Maximal V q.ker T 16 =>
      (⟨coordinates q hK E.val,maximal_coordinates V q hq hker p hp hK T E.val hkT hT E.property⟩ :
        Maximal (coordinates q hK T))) := by
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  have hi : Function.Injective i := derivedEmbedding_injective _
  constructor
  · intro E A he
    apply Subtype.ext
    have hEk := (maximalMover_iff_natural V q hq hker p hp T E.val 16 hkT).mp E.property |>.1
    have hAk := (maximalMover_iff_natural V q hq hker p hp T A.val 16 hkT).mp A.property |>.1
    exact coordinates_injective_on_saturated q hK hEk hAk
      ((map_mono E.property.1.1).trans hT) ((map_mono A.property.1.1).trans hT)
      (congrArg Subtype.val he)
  · intro A
    let E := (A.val.map i).comap q
    have hTm : (coordinates q hK T).map i=T.map q := coordinates_map q hK T hT
    have hET : E ≤ T := by
      have hh := comap_mono (f := q) ((map_mono (f := i) A.property.1).trans_eq hTm)
      exact hh.trans_eq (comap_map_eq_self hkT)
    have hEk : q.ker ≤ E := by
      intro x hx
      change q x ∈ A.val.map i
      rw [MonoidHom.mem_ker.mp hx]
      exact one_mem _
    have heq : coordinates q hK E=A.val := by
      change ((A.val.map i).comap q |>.map q).comap i=A.val
      rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top),
        comap_map_eq_self (by
          intro x hx
          have hx1 : x=1 := hi ((MonoidHom.mem_ker.mp hx).trans (map_one i).symm)
          rw [hx1]
          exact one_mem _)]
    have hEm := maximal_of_coordinates V q hq hker p hp hK T E hkT hT hEk hET
      (heq.symm ▸ A.property)
    exact ⟨⟨E,hEm⟩,Subtype.ext heq⟩

include hp in
theorem maximal_family_card_eq_coordinates (T : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range) :
    Nat.card (Subgroup.SmallMover.Maximal V q.ker T 16)=
      Nat.card (Maximal (coordinates q hK T)) := by
  exact Nat.card_congr (Equiv.ofBijective _
    (maximal_coordinates_bijective V q hq hker p hp hK T hkT hT))

include hp in
theorem two_maximal_radical_image_and_family_card (T E A : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hE : E ∈ Subgroup.SmallMover.Maximal V q.ker T 16)
    (hA : A ∈ Subgroup.SmallMover.Maximal V q.ker T 16) (hne : E ≠ A) :
    T.map q = (CentralRootGeometry.wing (F := K) false).map
      (derivedEmbedding (by omega : 2<Nat.card K)) ∧
    Nat.card (Subgroup.SmallMover.Maximal V q.ker T 16)=5 := by
  have himage := two_maximal_radical_image V q hq hker p hp hK T E A hkT hT hE hA hne
  refine ⟨himage,?_⟩
  rw [maximal_family_card_eq_coordinates V q hq hker p hp hK T hkT hT]
  have he : coordinates q hK T=CentralRootGeometry.wing (F := K) false := by
    apply map_injective (derivedEmbedding_injective _)
    exact (coordinates_map q hK T hT).trans himage
  rw [he]
  exact maximal_point_wing_card hK

include hp in
theorem two_maximal_join_eq_radical (T E A : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hE : E ∈ Subgroup.SmallMover.Maximal V q.ker T 16)
    (hA : A ∈ Subgroup.SmallMover.Maximal V q.ker T 16) (hne : E ≠ A) :
    Subgroup.SmallMover.join V q.ker T 16 = T := by
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  have hEc := maximal_coordinates V q hq hker p hp hK T E hkT hT hE
  have hAc := maximal_coordinates V q hq hker p hp hK T A hkT hT hA
  have hkerE := (maximalMover_iff_natural V q hq hker p hp T E 16 hkT).mp hE |>.1
  have hkerA := (maximalMover_iff_natural V q hq hker p hp T A 16 hkT).mp hA |>.1
  have hne' : coordinates q hK E ≠ coordinates q hK A := by
    intro he
    exact hne (coordinates_injective_on_saturated q hK hkerE hkerA
      ((map_mono hE.1.1).trans hT) ((map_mono hA.1.1).trans hT) he)
  have hmodel := two_maximal_classification hK hEc hAc hne'
  let J := Subgroup.SmallMover.join V q.ker T 16
  have hJT : J ≤ T := Subgroup.SmallMover.join_le _ _ _ _
  have hkJ : q.ker ≤ J := hkerE.trans (le_sSup hE)
  have hmap : T.map q ≤ J.map q := by
    rw [←coordinates_map q hK T hT,←hmodel.2.2.2]
    change (join (coordinates q hK T)).map i ≤ J.map q
    rw [join,sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro B
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hB
    obtain ⟨C,hC⟩ := (maximal_coordinates_bijective V q hq hker p hp hK T hkT hT).surjective ⟨B,hB⟩
    have heq : coordinates q hK C.val=B := congrArg Subtype.val hC
    rw [←heq,coordinates_map q hK C.val ((map_mono C.property.1.1).trans hT)]
    exact map_mono (le_sSup C.property)
  apply le_antisymm hJT
  have hc := comap_mono (f := q) hmap
  simpa only [comap_map_eq_self hkT,comap_map_eq_self hkJ] using hc

end ModelSmallMovers
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
