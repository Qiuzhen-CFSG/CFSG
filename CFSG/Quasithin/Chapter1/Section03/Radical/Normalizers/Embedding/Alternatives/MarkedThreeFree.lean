module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Setup
public import Theory.GroupTheory.SylowInvariantThreeFree
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups

/-!
# The original radical image excludes the Held containing carrier

The literal image of Ξ_p(L) in N/O₂(N) is two-perfect, three-free and
normalized by the image of the original full Sylow. It is nontrivial
because the original radical obstruction survives this quotient.
The certified Held theorem makes every three-free Sylow-invariant
subgroup a two-group, contradicting two-perfection and nontriviality.

Source: Aschbacher–Smith 1.3.8, printed p.513, with the actual Held
Sylow-overgroup calculation imported below. No case-ten conclusion
or identification of p with five is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 Alternatives
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
variable {C : Subgroup (radicalCore p L T)} {K : Subgroup G}

/-- The marked three-free, two-perfect radical image retains the literal
Sylow normalization and is nontrivial inside the actual containing image. -/
theorem SourceData.marked_xi_image_setup (h : SourceData 𝒦 p r L T C K) :
    let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
    let X := quotientImage (XiP p L) N
    let D := quotientImage K N
    ∃ S : Sylow 2 (XiQuotient N),
      (S : Subgroup (XiQuotient N)) ≤ normalizer (X : Set (XiQuotient N)) ∧
      D.IsCComponent ∧ X ≤ D ∧ IsPPerfect 2 X ∧ ¬ 3 ∣ Nat.card X ∧ X ≠ ⊥ := by
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let X₀ := XiP p L
  let q := QuotientGroup.mk' (pCore 2 N)
  let X := quotientImage X₀ N
  have hXK : X₀ ≤ K := h.contains_xi.trans h.contains_Y
  have hXN : X₀ ≤ N := hXK.trans h.component.1
  obtain ⟨S,hS,_,_,_,_,_,hD⟩ := h.marked_image_setup
  have hnN : (T : Subgroup G).subgroupOf N ≤ normalizer (X₀.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hXN]
    exact comap_mono h.xi.invariant
  have hn : (S : Subgroup (XiQuotient N)) ≤ normalizer (X : Set (XiQuotient N)) := by
    rw [hS]
    exact (map_mono (f := q) hnN).trans ((X₀.subgroupOf N).le_normalizer_map q)
  let a : X₀.subgroupOf N ≃* X₀ := subgroupOfEquivOfLe hXN
  have hp : IsPPerfect 2 X :=
    (h.xi.perfect.of_surjective a.symm.toMonoidHom a.symm.surjective).of_surjective
      (q.subgroupMap _) (q.subgroupMap_surjective _)
  let : Fact p.Prime := ⟨h.prime⟩
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  have hx3 : ¬ 3 ∣ Nat.card X₀ := by
    intro hd
    have hs := XiP_join_radicalCore_primeSupport p p ho h.invariant Nat.prime_three
      (hd.trans (card_dvd_of_le (show X₀ ≤ X₀ ⊔ radicalCore p L T from le_sup_left)))
    rcases hs with hs | hs <;> have := h.large <;> omega
  have hthree : ¬ 3 ∣ Nat.card X := by
    intro hd
    apply hx3
    rw [← Nat.card_congr a.toEquiv]
    exact hd.trans (card_dvd_of_surjective (q.subgroupMap _) (q.subgroupMap_surjective _))
  refine ⟨S,hn,hD,map_mono (comap_mono hXK),hp,hthree,?_⟩
  intro he
  apply actual_image_not_le_radical hXK h.component.1 h.radical_exclusion
  change quotientImage (XiP p L) N ≤ _
  rw [he]
  exact bot_le

/-- The actual Held carrier cannot contain the original radical image. -/
theorem SourceData.containing_not_held (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃* Held.He) := by
  rintro ⟨e⟩
  obtain ⟨S,hn,hD,hXD,hp,hthree,hne⟩ := h.marked_xi_image_setup
  exact hne (eq_bot_of_three_free_model S hD.subnormal hXD hn hp hthree e
    Held.LocalPairs.SylowGeometry.inner_normalized_three_prime_isPGroup)

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
