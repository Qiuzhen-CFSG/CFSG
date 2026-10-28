module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointAlternatingModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.IntrinsicFour
public import Theory.SpecificGroups.AlternatingSevenNormalControl
public import Theory.SpecificGroups.Alternating.SevenPerfectSylow
public import Theory.GroupTheory.PResidual.NormalizerImage

/-!
# Inner action on the actual A7 containing carrier

The conjugation action on the normal A7 carrier has image A7 or S7.
The S7 image would send the actual full Sylow to a full symmetric Sylow
normalizing the perfect order168 smaller subgroup. The seven-cycle and
transposition obstruction excludes this image. Thus X=K C_X(K), and the
original smaller normalizer equals B C_X(K).

For the actual point quotient, the literal preimage of C_X(K) normalizes
the original L and hence its intrinsic four. The full Sylow places O2(C)
inside the original join normalizing L, so the perfect-subgroup normalizer
comparison applies to the unchanged quotient map. No faithful action of
the entire point quotient, or normalization of the four by K, is assumed.

Source: Aschbacher--Smith15.3.23, pp.1128--1129, and the seven-letter
Sylow-normalized subgroup analysis of12.2.7(2), p.797.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
variable {X : Type*} [Group X] [Finite X]

/-- A full Sylow normalizing the actual binary-three subgroup forces inner
action on its normal A7 overgroup. The centralizing factor is retained. -/
theorem binary_three_a7_inner_control
    (B K : Subgroup X) [K.Normal] [Group.IsPerfect B]
    (hBK : B ≤ K) (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (a : K ≃* alternatingGroup (Fin 7))
    (T : Sylow 2 X) (hTB : (T : Subgroup X) ≤ normalizer B) :
    B < K ∧ K ⊔ centralizer (K : Set X) = ⊤ ∧
      normalizer B = B ⊔ centralizer (K : Set X) ∧
      ((QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
        (MulAut.conjNormal : X →* MulAut K)).ker = ⊤ := by
  obtain ⟨_,hBcard,hNK⟩ := binary_three_alternating_seven_placement hBK eB a
  obtain ⟨f,hker,hK⟩ := AlternatingSevenNormal.exists_permutation_action K a
  have hKcard : Nat.card K = 2520 := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.card_fin,Nat.factorial]
  have hKi : Function.Injective (f.subgroupMap K) :=
    ((f.subgroupMap_surjective K).bijective_of_nat_card_le (by
      rw [hK,Nat.card_congr a.toEquiv])).1
  have hBi : Function.Injective (f.subgroupMap B) := by
    intro x y he
    apply Subtype.ext
    have hh : f.subgroupMap K (inclusion hBK x) = f.subgroupMap K (inclusion hBK y) :=
      Subtype.ext (congrArg (fun y : B.map f => (y : Equiv.Perm (Fin 7))) he)
    exact congrArg (fun y : K => (y : X)) (hKi hh)
  have hBf : Nat.card (B.map f) = 168 :=
    (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap B)
      ⟨hBi,f.subgroupMap_surjective B⟩).symm.toEquiv).trans hBcard
  have hrange : f.range = alternatingGroup (Fin 7) := by
    rcases alternatingGroup.SevenComponent.range_eq_alternating_or_top f
        (hK ▸ K.map_le_range f) with h | h
    · exact h
    have hf : Function.Surjective f := MonoidHom.range_eq_top.mp h
    let S := T.mapSurjective (f := f) hf
    let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
    have hne : B.map f ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hBf
      omega
    have hproper : B.map f ≠ alternatingGroup (Fin 7) := by
      intro he
      rw [he,nat_card_alternatingGroup] at hBf
      norm_num [Nat.card_fin,Nat.factorial] at hBf
    have hSB : (S : Subgroup (Equiv.Perm (Fin 7))) ≤ normalizer (B.map f) :=
      (map_mono hTB).trans (B.le_normalizer_map f)
    exact False.elim (Theory.SpecificGroups.Alternating.SevenPerfectSylow.seven_not_dvd
      (B.map f) hne hproper S hSB (by rw [hBf]; decide))
  have hgen : K ⊔ centralizer (K : Set X) = ⊤ := by
    have hh := congrArg (comap f) (hK.trans hrange.symm)
    rw [comap_map_eq,hker] at hh
    apply hh.trans
    apply top_unique
    intro x _
    exact ⟨x,rfl⟩
  let Z := centralizer (K : Set X)
  have hZB : Z ≤ normalizer B :=
    (centralizer_le hBK).trans (Subgroup.centralizer_le_normalizer _)
  have hKZ : K ≤ normalizer Z :=
    (le_centralizer_iff.mp (show Z ≤ centralizer (K : Set X) from le_rfl)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnorm : normalizer B = B ⊔ Z := by
    apply le_antisymm ?_ (sup_le B.le_normalizer hZB)
    intro x hx
    have hp : x ∈ (K : Set X) * (Z : Set X) := by
      rw [←coe_mul_of_left_le_normalizer_right K Z hKZ,hgen]
      exact mem_top x
    obtain ⟨k,hk,z,hz,rfl⟩ := hp
    have hkN : k ∈ normalizer B := by
      have hh : k * z * z⁻¹ ∈ normalizer (B : Set X) :=
        (normalizer (B : Set X)).mul_mem hx ((normalizer (B : Set X)).inv_mem (hZB hz))
      simpa only [mul_inv_cancel_right] using hh
    have hkB : k ∈ B := hNK ▸ (show k ∈ normalizer B ⊓ K from ⟨hkN,hk⟩)
    exact mul_mem (mem_sup_left hkB) (mem_sup_right hz)
  refine ⟨lt_of_le_of_ne hBK ?_,hgen,hnorm,?_⟩
  · intro he
    rw [he,hKcard] at hBcard
    omega
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',
      MulAut.conjNormal_comap_innerSubgroup,hgen]

open LinearThree LinearThree.OriginalSource ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- The actual point, full Sylow and quotient map supply inner A7 action
and normalization of the original component and intrinsic four by the
literal preimage of the centralizing factor. -/
theorem binary_three_point_a7_inner_control
    (d : LocalData G) (L : Subgroup G)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (a : K ≃* alternatingGroup (Fin 7)) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let Z := centralizer (K : Set (C ⧸ pCore 2 C))
    let D := (Z.comap q).map C.subtype
    B < K ∧ K ⊔ Z = ⊤ ∧ normalizer B = B ⊔ Z ∧
      (K.comap q).map C.subtype ⊔ D = C ∧
      D ≤ normalizer L ∧ D ≤ normalizer (intrinsicFour L) := by
  let C := centralizer ({z} : Set G)
  let J := L ⊔ d.S
  let q := QuotientGroup.mk' (pCore 2 C)
  let A := L.subgroupOf C
  let B := A.map q
  let Z := centralizer (K : Set (C ⧸ pCore 2 C))
  let D := (Z.comap q).map C.subtype
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hJL : J ≤ normalizer L :=
    (normal_subgroupOf_iff_le_normalizer (show L ≤ J from le_sup_left)).mp b.component_normal
  have hPB : (P : Subgroup C) ≤ normalizer A := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    apply hJL
    exact (show d.S ≤ J from le_sup_right) (hP ▸ mem_map_of_mem C.subtype hx)
  let T := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hTB : (T : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer B :=
    (map_mono hPB).trans (A.le_normalizer_map q)
  let : Group.IsPerfect (L.subgroupOf J) := b.component.perfect
  let i : (L.subgroupOf J) ≃* A :=
    (subgroupOfEquivOfLe (show L ≤ J from le_sup_left)).trans (subgroupOfEquivOfLe hLC).symm
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  let : Group.IsPerfect B := Group.IsPerfect.map q
  have hq : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hqA : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hq.comap_subtype
  let j : A ≃* L := subgroupOfEquivOfLe hLC
  let eA := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans e
  let eB := ((q.subgroupMap A).pCoreQuotientEquiv
    (q.subgroupMap_surjective A) hqA).symm.trans eA
  obtain ⟨hstrict,hgen,hnorm,_⟩ := binary_three_a7_inner_control B K hBK eB a
    T hTB
  have hcover : (K.comap q).map C.subtype ⊔ D = C := by
    change (K.comap q).map C.subtype ⊔ (Z.comap q).map C.subtype = C
    rw [←Subgroup.map_sup,comap_sup_eq q K Z (QuotientGroup.mk'_surjective _),
      hgen,comap_top,←MonoidHom.range_eq_map,range_subtype]
  have hkernel : q.ker ≤ normalizer A := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal P).trans hPB
  have hperfect : IsPPerfect 2 A := by
    intro U hU hp
    let := hU
    have ht : Subsingleton (A ⧸ U) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (A ⧸ U) hp.isNilpotent
    apply eq_top_iff.mpr
    intro x _
    exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
  have hpre : (normalizer B).comap q = (normalizer L).subgroupOf C :=
    (comap_normalizer_map_of_pPerfect q A hperfect hq hkernel).trans
      (subgroupOf_normalizer_eq hLC).symm
  have hD : D ≤ normalizer L := by
    apply map_le_iff_le_comap.mpr
    change Z.comap q ≤ (normalizer L).subgroupOf C
    rw [←hpre]
    exact comap_mono ((centralizer_le hBK).trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨hstrict,hgen,hnorm,hcover,hD,hD.trans (intrinsicFour_normalized L)⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
