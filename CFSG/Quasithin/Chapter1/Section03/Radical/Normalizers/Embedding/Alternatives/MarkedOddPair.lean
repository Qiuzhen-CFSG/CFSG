module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddSylowPairs.Finite
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.SylowTransport

/-!
# The original radical supplies an actual odd-complement Sylow pair

Choose a Sylow p-subgroup of Ξ_p(L). The two factorizations in 1.3.2
make its ambient image permute with T. Relative normality of K inside
the characteristic normalizer restricts T to a full Sylow of K.
The complement lies in K, and survives K → K/O₂(K) injectively.
The actual component-quotient equivalence then transports the pair to
the literal image of K in N/O₂(N). This excludes J₄ through the checked
eleven-pair theorem, with no case-ten premise.

Source: Aschbacher–Smith 1.3.2 and 1.3.8, printed pp.508 and 513,
using the full-Sylow sporadic exclusions developed for 1.3.4, pp.510–511.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
open Section02 XiEmbedding XiEmbedding.InvariantLarge
universe u
variable {G : Type u} [Group G] [Finite G]
variable {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G} {T : Sylow 2 G}
variable {C : Subgroup (radicalCore p L T)} {K : Subgroup G}

/-- The actual pre-embedding source data yields a full odd-complement
Sylow pair in the literal containing image, including its central cover. -/
theorem SourceData.containing_oddSylowPair (h : SourceData 𝒦 p r L T C K) :
    HasOddSylowPair p (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G))) := by
  let : Fact p.Prime := ⟨h.prime⟩
  let := h.characteristic
  have ho : Odd p := h.prime.odd_of_ne_two (by have := h.large; omega)
  let N := normalizer (C.map (radicalCore p L T).subtype : Set G)
  let X := XiP p L
  let P : Sylow p X := default
  let P₀ := (P : Subgroup X).map X.subtype
  have hXK : X ≤ K := h.contains_xi.trans h.contains_Y
  have hXN : X ≤ N := hXK.trans h.component.1
  have hTN : (T : Subgroup G) ≤ N :=
    (t_le_normalizer_radicalCore p L T).trans
      (normalizer_le_normalizer_characteristic_image _ C)
  have hSyl : IsSylowIn 2 (T : Subgroup G) N :=
    ⟨T.subtype hTN, map_subgroupOf_eq_of_le hTN⟩
  have hi : LocalInput p (T : Subgroup G) X P₀ N :=
    localInput_of_mem_Xi h.xi hSyl (sup_le hXN hTN) ho h.xi_shape P
  have hPK : P₀ ≤ K := (map_subtype_le _).trans hXK
  have hpair : HasOddSylowPair p K := by
    obtain ⟨S,hS⟩ := exists_component_sylow_of_sylow hSyl h.component.1 h.normal
    refine ⟨S,P₀.subgroupOf K,
      hi.odd_complement.of_mulEquiv (subgroupOfEquivOfLe hPK).symm,?_⟩
    change (P₀.subgroupOf K : Set K) * ((S : Subgroup K) : Set K) =
      ((S : Subgroup K) : Set K) * (P₀.subgroupOf K : Set K)
    rw [hS]
    exact complement_mul_component_intersection hi hPK
  have hquot : HasOddSylowPair p (XiQuotient K) := by
    apply hpair.map (QuotientGroup.mk' (pCore 2 K)) (QuotientGroup.mk'_surjective _)
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn]
    exact ho.coprime_two_right.pow_right n
  exact hquot.of_mulEquiv (componentQuotientEquiv h.component.1 h.component.2)

/-- The original pair rules out the genuine J₄ carrier at its forced
prime eleven, without identifying p before the model-order argument. -/
theorem SourceData.containing_not_janko_four (h : SourceData 𝒦 p r L T C K) :
    ¬ Nonempty (quotientImage K
      (normalizer (C.map (radicalCore p L T).subtype : Set G)) ≃* Janko4.Model) := by
  rintro ⟨e⟩
  let : Fact p.Prime := ⟨h.prime⟩
  exact h.containing_oddSylowPair.not_jankoFour h.large e

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase
