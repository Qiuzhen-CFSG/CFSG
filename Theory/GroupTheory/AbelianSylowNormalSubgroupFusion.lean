module

public import Theory.GroupTheory.WeakClosureSetFusion
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Normalizer-invariant subgroups of an abelian Sylow group

Burnside fusion controls conjugation of subgroups inside an abelian Sylow
group. Consequently a subgroup normalized by the full Sylow normalizer has
no distinct ambient conjugate inside that Sylow group. The proof applies
the existing set-fusion theorem, retaining the exact subgroup conjugator.

Source: Aschbacher--Smith A.1.35, applied in J.3.6, printed pp.30 and439.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem conjugate_subgroup_eq_of_abelian_normalizer (P : Sylow p G)
    [IsMulCommutative P] (B : Subgroup G) (hBP : B ≤ (P : Subgroup G))
    (hn : normalizer (P : Set G) ≤ normalizer (B : Set G))
    (g : G) (hg : B.conjBy g ≤ (P : Subgroup G)) : B.conjBy g = B := by
  have hweak (x : G) (hx : (P : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ P) :
      x ∈ normalizer (P : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hx (by rw [card_map_of_injective (MulAut.conj x).injective])
  have hnorm {A : Subgroup G} (hAP : A ≤ (P : Subgroup G)) :
      (P : Subgroup G) ≤ normalizer (A : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro x hx a ha
    exact (P : Subgroup G).le_centralizer hx a (hAP ha)
  obtain ⟨n,hnP,he⟩ := P.weakly_closed_normalizer_controls_set_fusion
    (P : Subgroup G) le_rfl hweak (B : Set G) (B.conjBy g : Set G)
    (hnorm hBP) (hnorm hg) g rfl
  apply SetLike.coe_injective
  exact he.symm.trans (mem_normalizer_iff_conj_image_eq.mp (hn hnP))
end Sylow
