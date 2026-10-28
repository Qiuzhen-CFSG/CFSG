module
public import Theory.GroupTheory.AbelianCommutatorIndex.IndexTwo
public import Theory.GroupAction.SymmetricSixChiefBudget.Quotient
public import Theory.GroupAction.SymmetricSixChiefBudget.SmallConstituents
public import Theory.GroupAction.NormalPChiefSeries.CubicBound

/-!
# A chief-factor bound from a line of commutators

For a finite group above S₆ with two-group kernel, take a normal abelian
section V/Z in that kernel. An actor above an even involution that moves
an index-two subgroup into a line has fixed index at most four on the
whole quotient. Each noncentral chief factor costs at least four, so the
literal quotient admits at most one such factor. The model catalogue identifies each
surviving factor as a natural four-space. Coprime additivity bounds every
cubic action on the quotient by two. The projection to S₆,
its two-kernel and the actor marking descend through the same quotient.

Source application: Aschbacher--Smith, Lemma 13.8.33, printed p.967,
the chief-factor and cubic-action bounds on V_H/U_H. The subsequent
comparison with the Steinberg lower bound remains separate.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement.SymmetricSixBudget
variable {H : Type*} [Group H] [Finite H]

/-- A line of movement on an index-two subgroup permits at most one
noncentral chief factor in the literal abelian normal section above S₆. -/
theorem quotient_noncentralCount_le_one_of_index_two
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z X W : Subgroup H) [V.Normal] [Z.Normal]
    (hZV : Z ≤ V) (hV : V ≤ q.ker) (hXV : X ≤ V) (habelian : ⁅V,V⁆ ≤ Z)
    (y : H) (ha : orderOf (q y) = 2) (heven : q y ∈ alternatingGroup (Fin 6))
    (hc : ⁅X,zpowers y⁆ ≤ W) (hW : Z.relIndex W ≤ 2) (hindex : X.relIndex V ≤ 2) :
    letI : (V.map (QuotientGroup.mk' Z)).Normal :=
      Normal.map inferInstance (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    ∀ s : SeriesOn (V.map (QuotientGroup.mk' Z)), s.noncentralCount ≤ 1 := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  intro s
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hactor : q y ∈ (zpowers (π y)).map qbar := mem_map_of_mem qbar (mem_zpowers (π y))
  have hfixed := quotient_centralizer_relIndex_le_four_of_index_two
    V Z X W hZV hXV habelian y hc hW hindex
  exact noncentralCount_le_one_of_le_ker qbar hqbar hpbar (V.map π) hVbar
    (zpowers (π y)) (q y) ha heven hactor (hfixed.trans (by decide)) s
/-- The same literal quotient has at most one noncentral constituent, each
such constituent has order sixteen, and every three-subgroup has cubic
movement length at most two. No natural marking is chosen. -/
theorem quotient_chief_structure_of_index_two
    (q : H →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q) (hp : IsPGroup 2 q.ker)
    (V Z X W : Subgroup H) [V.Normal] [Z.Normal]
    (hZV : Z ≤ V) (hV : V ≤ q.ker) (hXV : X ≤ V) (habelian : ⁅V,V⁆ ≤ Z)
    (y : H) (ha : orderOf (q y) = 2) (heven : q y ∈ alternatingGroup (Fin 6))
    (hc : ⁅X,zpowers y⁆ ≤ W) (hW : Z.relIndex W ≤ 2) (hindex : X.relIndex V ≤ 2) :
    letI : (V.map (QuotientGroup.mk' Z)).Normal :=
      Normal.map inferInstance (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z)
    ∀ s : SeriesOn (V.map (QuotientGroup.mk' Z)),
      s.noncentralCount ≤ 1 ∧
      (∀ i, ¬ s.Central i → Nat.card (s.Factor i) = 16) ∧
      ∀ B : Subgroup (H ⧸ Z), IsPGroup 3 B →
        conjugationCubicLength B (V.map (QuotientGroup.mk' Z)) ≤ 2 := by
  let π := QuotientGroup.mk' Z
  let qbar := QuotientGroup.lift Z q (hZV.trans hV)
  have hqbar : Function.Surjective qbar :=
    QuotientGroup.lift_surjective_of_surjective Z q hq _
  have hker : qbar.ker = q.ker.map π := QuotientGroup.ker_lift Z q _
  have hpbar : IsPGroup 2 qbar.ker := by rw [hker]; exact hp.map π
  let : (V.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective Z)
  intro s
  have hVbar : V.map π ≤ qbar.ker := by rw [hker]; exact map_mono hV
  have hactor : q y ∈ (zpowers (π y)).map qbar := mem_map_of_mem qbar (mem_zpowers (π y))
  have hfixed := quotient_centralizer_relIndex_le_four_of_index_two
    V Z X W hZV hXV habelian y hc hW hindex
  have hs := noncentralCount_le_one_of_le_ker qbar hqbar hpbar (V.map π) hVbar
    (zpowers (π y)) (q y) ha heven hactor (hfixed.trans (by decide)) s
  have hcard : ∀ i, ¬ s.Central i → Nat.card (s.Factor i) = 16 :=
    noncentral_factor_card_sixteen qbar hqbar hpbar (V.map π) hVbar
      (zpowers (π y)) (π y) (mem_zpowers _) ha heven hfixed s
  refine ⟨hs, hcard, fun B hB => ?_⟩
  have hh := s.cubic_length_le_twice_count (hpbar.to_le hVbar)
    (fun i hi => (hcard i hi).le) B hB
  omega
end NoncentralChiefRefinement.SymmetricSixBudget
