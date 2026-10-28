module
public import CFSG.Quasithin.ChapterB.Section02.Thompson

/-!
# Normalizers of rank-indexed Thompson images

If the kernel of an action of B lies in R ≤ B, the preimage of the image
of J_j(R) is an intermediate subgroup between J_j(R) and R. B.2.3(3)
recovers J_j(R) from this preimage, so its image normalizer lifts to the
original normalizer. Surjectivity of the action is unnecessary.

Source: Aschbacher--Smith 13.1.9, printed p.871, using B.2.3(3), p.75.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- Lift a Thompson-image normalizer through a kernel contained in the
original two-subgroup. All inclusions are relative to the specified B. -/
theorem normalizer_image_thompson_le (B R : Subgroup G) (hRB : R ≤ B)
    {j : ℕ} (hj : j < twoRank R) (q : B →* Q) (hker : q.ker ≤ R.subgroupOf B) :
    ((normalizer (((thompsonJ R j).subgroupOf B).map q : Set Q)).comap q).map B.subtype ≤
      normalizer (thompsonJ R j : Set G) := by
  let J := thompsonJ R j
  let P := (((J.subgroupOf B).map q).comap q).map B.subtype
  have hJB : J ≤ B := (thompsonJ_le R j).trans hRB
  have hP : P = J ⊔ q.ker.map B.subtype := by
    dsimp only [P]
    rw [comap_map_eq,Subgroup.map_sup,map_subgroupOf_eq_of_le hJB]
  have hJP : J ≤ P := by rw [hP]; exact le_sup_left
  have hPR : P ≤ R := by
    rw [hP]
    exact sup_le (thompsonJ_le R j)
      ((map_mono hker).trans_eq (map_subgroupOf_eq_of_le hRB))
  have hJ : J = thompsonJ P j := lemma_B_2_3_3 R P hj hJP hPR
  have hNP : ((normalizer ((J.subgroupOf B).map q : Set Q)).comap q).map B.subtype ≤
      normalizer (P : Set G) :=
    (map_mono (((J.subgroupOf B).map q).le_normalizer_comap q)).trans
      (le_normalizer_map _)
  intro x hx
  have hxP := hNP hx
  change x ∈ normalizer (J : Set G)
  rw [hJ]
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (thompsonJ P j).map (MulAut.conj x).toMonoidHom = _
  have he : P.map (MulAut.conj x).toMonoidHom = P := mem_normalizer_iff_map_conj_eq.mp hxP
  rw [←thompsonJ_map_equiv,he]

end CFSG.Quasithin.ChapterB
