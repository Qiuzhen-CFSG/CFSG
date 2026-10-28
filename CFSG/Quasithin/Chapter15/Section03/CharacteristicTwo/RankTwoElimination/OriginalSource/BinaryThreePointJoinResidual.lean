module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointJoinQuotient
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectImage
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original smaller component is the residual of its actual Sylow join

The original component is perfect and its full Sylow normalizes it. Its
point quotient image B is therefore exactly the embedded two-residual of
B joined with the original image Sylow. Restricting that same Sylow to the
actual normal containing component preserves this equality intrinsically.
These are literal residual identities for the finite flag comparisons.

Source: Aschbacher--Smith15.3.23, printed pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterC BinaryMS.MS93
variable {G : Type*} [Group G] [Finite G]

/-- Both the full original image join and its actual containing-component
Sylow restriction have B as their embedded two-residual. -/
theorem binary_three_point_join_residual
    (d : LocalData G) (L : Subgroup G)
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (L.subgroupOf (L ⊔ d.S)) (d.S.subgroupOf (L ⊔ d.S)))
    (z : G) (hLS : L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (L.subgroupOf C).map q
    let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
    let J := B ⊔ (S : Subgroup (C ⧸ pCore 2 C))
    (pResidual 2 J).map J.subtype = B ∧
      ∃ T : Sylow 2 K, (T : Subgroup K) = (S : Subgroup (C ⧸ pCore 2 C)).subgroupOf K ∧
        let D := B.subgroupOf K
        let J₀ := D ⊔ (T : Subgroup K)
        (pResidual 2 J₀).map J₀.subtype = D := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let A := L.subgroupOf C
  let B := A.map q
  let S := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  have hLC : L ≤ C := le_sup_left.trans hLS
  have hSL : d.S ≤ normalizer (L : Set G) :=
    le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (show L ≤ L ⊔ d.S from le_sup_left)).mp b.component_normal)
  have hPB : (P : Subgroup C) ≤ normalizer (A : Set C) := by
    rw [←subgroupOf_normalizer_eq hLC]
    intro x hx
    exact hSL (hP ▸ mem_map_of_mem C.subtype hx)
  have hSB : (S : Subgroup (C ⧸ pCore 2 C)) ≤ normalizer (B : Set _) :=
    (map_mono (f := q) hPB).trans (A.le_normalizer_map q)
  let : Group.IsPerfect (L.subgroupOf (L ⊔ d.S)) := b.component.perfect
  let i := subgroupOfEquivOfLe (show L ≤ L ⊔ d.S from le_sup_left)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
  let a := subgroupOfEquivOfLe hLC
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective A)
  have hBp : IsPPerfect 2 B := (pResidual_eq_top_iff 2 B).mp (pResidual_eq_top_of_isPerfect 2)
  have hfull := embedded_pResidual_join_pGroup B (S : Subgroup _) hBp S.isPGroup' hSB
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal K
  let D := B.subgroupOf K
  have hDp : IsPPerfect 2 D := hBp.of_surjective (subgroupOfEquivOfLe hBK).symm.toMonoidHom
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hTD : (T : Subgroup K) ≤ normalizer (D : Set K) := by
    rw [hT,←subgroupOf_normalizer_eq hBK]
    exact fun _ hx => hSB hx
  exact ⟨hfull,T,hT,embedded_pResidual_join_pGroup D (T : Subgroup K) hDp T.isPGroup' hTD⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
