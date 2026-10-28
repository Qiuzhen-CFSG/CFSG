module
public import Theory.GroupTheory.ElementaryThompsonComponent
public import Theory.Order.UniqueMaximalOver
/-!
# A central seed forces Thompson movement in a minimal parabolic

Let U be normal and contain a Sylow-central seed Z which is not central
in the full group. Then C(U)T is proper. If J(T) centralizes U, Thompson
heredity and Frattini give G=N(J(T))C(U). The unique maximal overgroup
of T contains both factors unless J(T) is normal, a contradiction.

The result needs no classification or odd-core theorem. It supplies the
movement step for the original omega-center orbit in source 3.1.7.
Source: Aschbacher–Smith, Lemma 3.1.7, pp.575–576, using the Frattini
argument underlying B.2.7.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem thompson_not_centralizes_of_unique_maximal
    (T : Sylow 2 G) (U Z : Subgroup G) [U.Normal]
    (hZ : Z ≤ U) (hZT : Z ≤ centralizer (T : Set G))
    (hZc : ¬ Z ≤ center G)
    (hu : Order.HasUniqueMaximalOver (T : Subgroup G) ⊤)
    (hJn : ¬ (elementaryAbelianMaxJ (T : Subgroup G)).Normal) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
  intro hJ
  let N := normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)
  let C := centralizer (U : Set G)
  obtain ⟨B, hB, hb⟩ := hu.2
  have hTN : (T : Subgroup G) ≤ N := by
    intro t ht
    rw [mem_normalizer_iff_map_conj_eq]
    change (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj t).toMonoidHom = _
    have ht' : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    rw [← elementaryAbelianMaxJ_map_equiv, ht']
  have hNlt : N < ⊤ := lt_top_iff_ne_top.mpr fun he =>
    hJn (normalizer_eq_top_iff.mp he)
  have hNB : N ≤ B := hu.le_maximal hB hTN hNlt
  have hCTlt : C ⊔ (T : Subgroup G) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    apply hZc
    intro z hz
    exact mem_center_iff.mpr fun g => by
      have hCZ : C ⊔ (T : Subgroup G) ≤ centralizer (Z : Set G) :=
        sup_le (centralizer_le hZ) (le_centralizer_iff.mp hZT)
      have hg : g ∈ centralizer (Z : Set G) := hCZ (he.symm ▸ mem_top g)
      exact (hg z hz).symm
  have hCB : C ≤ B := le_sup_left.trans (hu.le_maximal hB le_sup_right hCTlt)
  have hgen := elementaryAbelianMaxJ_frattini_of_le_normal T C hJ
  have htop : (⊤ : Subgroup G) ≤ B := by rw [← hgen]; exact sup_le hNB hCB
  exact hB.2.ne (top_unique htop)

end Theory.GroupTheory
