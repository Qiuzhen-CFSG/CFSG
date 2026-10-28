module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.SourceSet
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.EmptyCase
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Elementary
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Intersections
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.SixSetCorrection

/-!
# Geometric obligations for the A₆ fusion branches

The compatible transport of 16.4.2(4), together with T_C = ⟨z⟩, identifies
the actual outer involution r as a conjugate of z. The marked permutation
model supplies the independence needed to apply the common intersection
lemma to any three distinct generators. Thus conjugate LE overgroups of
the marked points imply the pair and triple fusion exclusions.

`MarkedOvergroups` is the precise remaining geometric construction target;
this module does not assert its existence. `FullAutomorphismCase` means
surjectivity of the actual normalizer action transported through L ≃ A₆,
not an unrelated group-family label. The ordinary and full-automorphism
fusion branches and the local stabilizer computation remain separate tasks.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.Six
open Subgroup
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- Surjectivity of the actual normalizer conjugation action on the marked A₆. -/
def FullAutomorphismCase (e : L ≃* alternatingGroup (Fin 6)) : Prop :=
  Function.Surjective ((MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom)

/-- The geometric obligation used to exclude products: each marked point is the
center of a conjugate of LE containing all four marked points, with the source
index-two component overgroup. This condition contains no fusion exclusions. -/
def MarkedOvergroups (M : AlternatingProductModel L z r 6) : Prop :=
  ∀ k : Fin 4, ∃ x : G, MulAut.conj x z = generator M k ∧
    ((L ⊔ zpowers z).conjBy x).relIndex ((AlternatingOvergroup L z r).conjBy x) = 2 ∧
    ∀ i : Fin 4, generator M i ∈ (AlternatingOvergroup L z r).conjBy x

/-- The exclusions proved from those overgroups, kept separate from the
geometric construction so both fusion branches can proceed conditionally. -/
def ProductExclusions (M : AlternatingProductModel L z r 6) : Prop :=
  (∀ i j, i ≠ j → ¬ IsConj z (generator M i * generator M j)) ∧
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    ¬ IsConj z (generator M i * generator M j * generator M k))

variable [Finite G]

theorem conjugate_outer_of_transport {T : Sylow 2 G} {g : G} {R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hTC : commutingSylow T L = zpowers z)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤ (T : Subgroup G).conjBy g)
    (hr : r ∈ R) (hr2 : orderOf r = 2) : IsConj z r := by
  apply isConj_iff.mpr
  exact ⟨g, (h.involution_eq_conjugate_of_commutingSylow hTC htransport hr hr2).symm⟩

/-- Independence is supplied by the actual binary model; only the overgroup
containments and index are needed from the Sylow geometry. -/
theorem productExclusions_of_markedOvergroups {T : Sylow 2 G}
    (h : StandardSetup T z L) (hsmall : OrderTwoOutsideDeltaZero L)
    (hempty : ¬ (deltaZero L).Nonempty)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hr : IsConj z r) (hgeom : MarkedOvergroups M) : ProductExclusions M := by
  classical
  have hdis := disjoint_centralizer_of_alternating_equiv (by decide : 4 ≤ 6) e
  have hconj (i : Fin 4) : IsConj z (generator M i) :=
    (alpha_subset_beta M hr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).2
  have hpair (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
      ¬ IsConj z (generator M i * generator M j) ∧
        ¬ IsConj z (generator M i * generator M j * generator M k) := by
    obtain ⟨x, hx, hindex, hmem⟩ := hgeom k
    have ha : generator M i ≠ MulAut.conj x z := by
      rw [hx]
      exact fun he => hik (generator_injective M he)
    have hb : generator M j ≠ MulAut.conj x z := by
      rw [hx]
      exact fun he => hjk (generator_injective M he)
    have hab : generator M i ≠ generator M j := fun he => hij (generator_injective M he)
    have habc : generator M i * generator M j ≠ MulAut.conj x z := by
      rw [hx]
      exact generator_pair_ne_generator M i j k hij
    simpa only [hx] using h.two_three_products_not_conjugate hsmall hempty hdis x hindex
      (hmem i) (hmem j) (hconj i) (hconj j) ha hb hab habc
  constructor
  · intro i j hij
    have hex : ∃ k : Fin 4, i ≠ k ∧ j ≠ k := by
      revert i j; decide +kernel
    obtain ⟨k, hik, hjk⟩ := hex
    exact (hpair i j k hij hik hjk).1
  · intro i j k hij hik hjk
    exact (hpair i j k hij hik hjk).2

end CFSG.Quasithin.Chapter16.Intersections.Six
