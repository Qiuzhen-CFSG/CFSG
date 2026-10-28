module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalData
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Lifting the M₂₄ local quotient's normal three-subgroup

Suppose H contains R and the normalizer of S, and maps to S₃ × SL₃(2)
with two-group kernel. The map is injective on the odd complement R.
The quotient order excludes the extraspecial order 27, so R is elementary
abelian of order nine and maps onto a Sylow three-subgroup. This image
contains the normal C₃ in the symmetric factor. Its inverse image in R
has order three and survives in the Frattini quotient, since Φ(R) = 1.

Every abstract M₂₄ automorphism is inner. Thus a pair automorphism is
implemented by an element of N(S), hence of H, and preserves this inverse
image by normality of the quotient's C₃. This proves invariance for the
whole pair automizer, in particular for each of its two-subgroups.

The result is conditional on the actual local map and normalizer containment;
constructing the M₂₄ local overgroups remains a separate obligation.
Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528);
GLS3, Table 5.3e, E₆₄.N(3B).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- The normal three-subgroup of the symmetric factor, with trivial linear factor. -/
def distinguishedThree : Subgroup LocalQuotient :=
  (alternatingGroup (Fin 3)).prod ⊥

instance : distinguishedThree.Normal := inferInstanceAs
  ((alternatingGroup (Fin 3)).prod
    (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))).Normal

/-- The local quotient has three-part nine. -/
theorem localQuotient_card : Nat.card LocalQuotient = 1008 := by
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Matrix.PSL3Two.card_SL]
  norm_num

/-- The distinguished normal subgroup has order three. -/
theorem distinguishedThree_card : Nat.card distinguishedThree = 3 := by
  change Nat.card ((alternatingGroup (Fin 3)).prod
    (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) = 3
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_bot, mul_one, nat_card_alternatingGroup]
  norm_num

/-- Actual pair automorphisms are implemented by elements normalizing S. -/
theorem pairAutomizer_inner (S R : Subgroup Sporadic.Mathieu.M24)
    {a : MulAut R} (ha : a ∈ pairAutomizer S R) :
    ∃ g ∈ normalizer (S : Set Sporadic.Mathieu.M24),
      ∀ r : R, (a r : Sporadic.Mathieu.M24) = g * r * g⁻¹ := by
  obtain ⟨b, hb, he⟩ := ha
  obtain ⟨g, rfl⟩ := Sporadic.Mathieu.M24OuterRestriction.conj_surjective b
  refine ⟨g, mem_normalizer_iff.mpr (fun x => (hb x).symm), he⟩

/-- Lift the normal three-subgroup of the local quotient to an invariant
Frattini line. Normalizer containment ensures compatibility with every
extending automorphism, using the proved innerness of Aut(M₂₄). -/
theorem pairReducible_of_local_quotient
    (S R : Subgroup Sporadic.Mathieu.M24) (hR : XiOddQuotient 3 R)
    (H : Subgroup Sporadic.Mathieu.M24) (hRH : R ≤ H)
    (hNH : normalizer (S : Set Sporadic.Mathieu.M24) ≤ H)
    (f : H →* LocalQuotient) (hker : IsPGroup 2 f.ker) : PairReducible S R := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let fR : R →* LocalQuotient := f.comp (inclusion hRH)
  have hfR : Function.Injective fR := by
    apply (MonoidHom.ker_eq_bot_iff fR).mp
    apply bot_unique
    intro x hx
    have hd : Disjoint (R.subgroupOf H) f.ker :=
      (hR.isPGroup.comap_of_injective H.subtype H.subtype_injective).disjoint_of_coprime
        hker (by decide)
    have he : inclusion hRH x = 1 := hd.le_bot ⟨x.property, hx⟩
    exact Subtype.ext (congrArg (fun z : H => (z : Sporadic.Mathieu.M24)) he)
  have hc : Nat.card R ∣ 1008 := localQuotient_card ▸ card_dvd_of_injective fR hfR
  have hec : IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
    rcases hR with he | ⟨_, hcard, _⟩
    · exact he
    · norm_num [hcard] at hc
  let _ := hec.1
  let _ : Fact (IsPGroup 3 R) := ⟨hR.isPGroup⟩
  have hrange : Nat.card fR.range = 9 :=
    (Nat.card_congr (MonoidHom.ofInjective hfR).toEquiv).symm.trans hec.2
  have hindex : ¬ 3 ∣ fR.range.index := by
    have hh := fR.range.card_mul_index
    rw [hrange, localQuotient_card] at hh
    have hh' : fR.range.index = 112 := by omega
    rw [hh']
    decide
  let T : Sylow 3 LocalQuotient :=
    (hR.isPGroup.of_surjective fR.rangeRestrict fR.rangeRestrict_surjective).toSylow hindex
  have hthree : IsPGroup 3 distinguishedThree :=
    IsPGroup.of_card (n := 1) distinguishedThree_card
  have hle : distinguishedThree ≤ fR.range := hthree.le_sylow_of_normal T
  let A := distinguishedThree.comap fR
  have hmap : A.map fR = distinguishedThree := map_comap_eq_self hle
  have hAcard : Nat.card A = 3 := by
    rw [← card_map_of_injective (K := A) hfR, hmap, distinguishedThree_card]
  have hAb : A ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hAcard
    omega
  have hAt : A ≠ ⊤ := by
    intro hh
    rw [hh, card_top, hec.2] at hAcard
    omega
  have hAinv : ∀ a ∈ pairAutomizer S R, ∀ r ∈ A, a r ∈ A := by
    intro a ha r hr
    obtain ⟨g, hg, he⟩ := pairAutomizer_inner S R ha
    let gH : H := ⟨g, hNH hg⟩
    have hcj : inclusion hRH (a r) = gH * inclusion hRH r * gH⁻¹ :=
      Subtype.ext (he r)
    change f (inclusion hRH (a r)) ∈ distinguishedThree
    rw [hcj, map_mul, map_mul, map_inv]
    exact (inferInstance : distinguishedThree.Normal).conj_mem _ hr (f gH)
  let q := QuotientGroup.mk' (frattini R)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk', frattini_eq_bot_of_isElementaryAbelian (p := 3)]
  apply pairReducible_of_invariant
  refine ⟨A.map q, ?_, ?_, ?_⟩
  · intro hb
    exact hAb ((A.map_eq_bot_iff_of_injective hq).mp hb)
  · intro ht
    apply hAt
    apply map_injective hq
    rw [ht, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · intro a ha x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨a r, hAinv a ha r hr, (quotientAut_apply_mk _ _ _).symm⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction
