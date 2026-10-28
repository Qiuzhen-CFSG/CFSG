module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Theory.PGroupCore

/-!
# Intersections of a normal subgroup with two generators

If a normal subgroup `Q` normalizes two generating subgroups `V` and `W`,
then `(Q ∩ V)(Q ∩ W)` is a normal subgroup. If the generators are abelian,
their intersection is central. The proofs use the bounds `[Q,V] ≤ Q ∩ V`
and `[Q,W] ≤ Q ∩ W`, and the fact that both generators centralize their
intersection.

These are the elementary subgroup arguments in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
Proposition E.2.10(1), printed pp. 222–223. No classification assumption is
needed here.
-/

namespace Subgroup

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Two abelian subgroups centralize their intersection. -/
public theorem sup_le_centralizer_inf_of_abelian (V W : Subgroup G)
    [IsMulCommutative V] [IsMulCommutative W] :
    V ⊔ W ≤ centralizer (V ⊓ W : Subgroup G) := by
  exact sup_le (V.le_centralizer.trans (centralizer_le inf_le_left))
    (W.le_centralizer.trans (centralizer_le inf_le_right))

/-- The intersection of two abelian generating subgroups is central. -/
public theorem inf_le_center_of_abelian_generators (V W : Subgroup G)
    [IsMulCommutative V] [IsMulCommutative W] (hgen : V ⊔ W = ⊤) :
    V ⊓ W ≤ center G := by
  intro z hz
  rw [← centralizer_univ, ← coe_top, ← hgen, sup_eq_closure, centralizer_closure]
  rw [mem_centralizer_iff]
  intro x hx
  rcases hx with hx | hx
  · exact mem_centralizer_iff.mp (V.le_centralizer hz.1) x hx
  · exact mem_centralizer_iff.mp (W.le_centralizer hz.2) x hx

/-- A central intersection of abelian generators lies in the prime core
when one generator is a group of that prime power type. -/
public theorem abelian_generator_intersection_le_pCore (p : ℕ) (V W : Subgroup G)
    [IsMulCommutative V] [IsMulCommutative W] (hV : IsPGroup p V)
    (hgen : V ⊔ W = ⊤) : V ⊓ W ≤ pCore p G := by
  have hZ := inf_le_center_of_abelian_generators V W hgen
  have hnormal : (V ⊓ W).Normal := ⟨fun z hz g => by
    rw [(mem_center_iff.mp (hZ hz)) g, mul_inv_cancel_right]
    exact hz⟩
  exact le_sSup ⟨hnormal, hV.of_injective (inclusion inf_le_left)
    (inclusion_injective inf_le_left)⟩

/-- A normal subgroup normalizing `V` also normalizes the join of `V` with
any conjugate. Conjugation here is `x ↦ g*x*g⁻¹`. -/
public theorem normal_le_normalizer_conjugate_join (Q V : Subgroup G) [Q.Normal]
    (hQV : Q ≤ normalizer (V : Set G)) (g : G) :
    Q ≤ normalizer ((V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have hQg : Q.map (MulAut.conj g).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hQVg : Q ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [← map_equiv_normalizer_eq V (MulAut.conj g)]
    simpa only [hQg] using map_mono (f := (MulAut.conj g).toMonoidHom) hQV
  exact (le_inf hQV hQVg).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Intersecting a normal subgroup with two generators and taking the join
gives a normal subgroup when the normal subgroup normalizes both generators. -/
public theorem normal_sup_inf_of_normal_normalizes_generators
    (V W Q : Subgroup G) [Q.Normal] (hgen : V ⊔ W = ⊤)
    (hQV : Q ≤ normalizer (V : Set G)) (hQW : Q ≤ normalizer (W : Set G)) :
    ((Q ⊓ V) ⊔ (Q ⊓ W)).Normal := by
  let P := (Q ⊓ V) ⊔ (Q ⊓ W)
  have hPQ : P ≤ Q := sup_le inf_le_left inf_le_left
  have hVP : ⁅P, V⁆ ≤ P :=
    (le_inf ((commutator_mono hPQ le_rfl).trans (commutator_le_left Q V))
      (le_normalizer_iff_commutator_le_right.mp (hPQ.trans hQV))).trans le_sup_left
  have hWP : ⁅P, W⁆ ≤ P :=
    (le_inf ((commutator_mono hPQ le_rfl).trans (commutator_le_left Q W))
      (le_normalizer_iff_commutator_le_right.mp (hPQ.trans hQW))).trans le_sup_right
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  exact sup_le (le_normalizer_iff_commutator_le_left.mpr hVP)
    (le_normalizer_iff_commutator_le_left.mpr hWP)

/-- The join of the two intersections is their setwise product. -/
public theorem coe_sup_inf_eq_mul_of_normal_normalizes
    (V W Q : Subgroup G) [Q.Normal] (hQV : Q ≤ normalizer (V : Set G)) :
    (((Q ⊓ V) ⊔ (Q ⊓ W) : Subgroup G) : Set G) =
      ((Q ⊓ V : Subgroup G) : Set G) * ((Q ⊓ W : Subgroup G) : Set G) := by
  have hn : Q ⊓ W ≤ normalizer (Q ⊓ V : Subgroup G) :=
    (le_inf le_normalizer_of_normal (inf_le_left.trans hQV)).trans
      inf_normalizer_le_normalizer_inf
  exact coe_mul_of_right_le_normalizer_left _ _ hn

end Subgroup
