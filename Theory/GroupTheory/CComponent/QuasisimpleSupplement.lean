module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SolvableRadical.Transport
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!+# Radical supplements above a quasisimple quotient

Let G be perfect and Q normal with G/Q quasisimple. A supplement B to the
solvable radical is G itself if Q normalizes B. Indeed, the radical has
central image in G/Q, so perfectness makes the image of B all of G/Q.
Consequently G = BQ normalizes B. The remaining quotient G/B is both
perfect and solvable, hence trivial.

This handles the quasisimple two-core-quotient branch of the replacement
in Aschbacher–Smith, Lemma 13.6.16(2), combined 1 March 2004 manuscript,
printed p.930. It does not require the radical to be a two-group.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The solvable radical of a finite quasisimple group is central. -/
theorem IsQuasisimple.solvableRadical_le_center [IsQuasisimple G] :
    solvableRadical G ≤ center G := by
  rcases IsQuasisimple.normal_le_center_or_eq_top (solvableRadical G) with h | h
  · exact h
  · let : Group.IsSolvable (⊤ : Subgroup G) := h ▸ inferInstance
    let : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) topEquiv.surjective
    let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
    let : Nontrivial G := (QuotientGroup.mk'_surjective (center G)).nontrivial
    exact (Group.IsPerfect.not_isSolvable G inferInstance).elim

omit [Finite G] in
private theorem central_supplement_eq_top [Group.IsPerfect G] (B R : Subgroup G)
    (hR : R ≤ center G) (hgen : R ⊔ B = ⊤) : B = ⊤ := by
  have hn : (⊤ : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [← hgen]
    exact sup_le (hR.trans (center_le_normalizer _)) B.le_normalizer
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hbc : B ⊔ center G = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le (hR.trans le_sup_right) le_sup_left
  apply top_unique
  simpa using Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    hbc (inferInstance : IsMulCommutative (center G))

/-- A radical supplement normalized by the kernel of a quasisimple
quotient of a perfect group is the whole group. The kernel is only
required to be normal; its solvability is unnecessary. -/
theorem eq_top_of_radical_supplement_of_quasisimple_quotient [Group.IsPerfect G]
    (Q B : Subgroup G) [Q.Normal] [IsQuasisimple (G ⧸ Q)]
    (hQB : Q ≤ normalizer (B : Set G))
    (hgen : solvableRadical G ⊔ B = ⊤) : B = ⊤ := by
  let q := QuotientGroup.mk' Q
  have hcentral : (solvableRadical G).map q ≤ center (G ⧸ Q) :=
    (map_solvableRadical_le_of_surjective q (QuotientGroup.mk'_surjective Q)).trans
      IsQuasisimple.solvableRadical_le_center
  have hgenq : (solvableRadical G).map q ⊔ B.map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen,
      map_top_of_surjective q (QuotientGroup.mk'_surjective Q)]
  have hBq : B.map q = ⊤ := central_supplement_eq_top (B.map q) _ hcentral hgenq
  have hBQ : B ⊔ Q = ⊤ := by
    have he := congrArg (comap q) hBq
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using he
  have hn : (⊤ : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [← hBQ]
    exact sup_le B.le_normalizer hQB
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  let f := (QuotientGroup.mk' B).comp (solvableRadical G).subtype
  have hsur : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top]
    have he := congrArg (map (QuotientGroup.mk' B)) hgen
    simpa only [Subgroup.map_sup,
      (map_eq_bot_iff B).mpr (show B ≤ (QuotientGroup.mk' B).ker by simp), sup_bot_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective B),
      f, MonoidHom.range_comp, range_subtype] using he
  let : Group.IsSolvable (G ⧸ B) := Group.isSolvable_of_surjective hsur
  exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ B)

end Theory.GroupTheory
end
