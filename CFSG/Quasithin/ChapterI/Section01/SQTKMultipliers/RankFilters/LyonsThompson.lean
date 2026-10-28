module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterA.Section02.Sporadic.LyonsThompsonSections
public import Theory.Quasithin.InvolutionCentralizerQuotientRank
public import Theory.GroupTheory.CommutingCubicTriple
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.Words
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Words
public import Theory.SpecificGroups.Lyons.Atlas111InvolutionElementaryThree.Certificates
public import Theory.SpecificGroups.Thompson.Model.InvolutionCentralizer.ElementaryThree.Certificates

/-!
# The Lyons and Thompson local rank exclusions

The published involution-centralizer sections have targets A₁₁ and A₉,
both of 3-rank at least three. Coprimality of each literal quotient kernel
with three therefore excludes quasithinness, without the general section
bound A.2.15(2). Alternatively, an actual elementary subgroup of order 27
in the same numerator gives this obstruction directly.

The imported matrix certificates now construct such elementary subgroups
unconditionally in both actual carriers. They prove one base cube and three
pairwise commutations per model; the literal A₁₁ and A₉ quotient images detect
the three independent coordinates. Containment in the certified involution
centralizers gives local 3-rank at least three, excluding quasithinness and
hence strong quasithinness.

The earlier conditional kernel and word-relation interfaces are retained.
The unconditional exclusions use the elementary embeddings and require no
kernel identification, section-rank bound or ambient simplicity certificate.
They transport along actual group isomorphisms, including for finite simple
source models with their inherited instances. These are the Lyons and Thompson
exclusions needed by the full simple SQTK multiplier table in I.1.3.

Source: Aschbacher--Smith, A.2.19 and I.1.3, printed pp.40--41 and 407;
GLS3, Lyons involution table (p.278) and Table 5.3x (Thompson).
-/

namespace CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters

open ChapterA

private theorem three_le_rank_of_elementary_embedding
    {G : Type*} [Group G] [Finite G]
    (f : (Fin 3 → Multiplicative (ZMod 3)) →* G) (hf : Function.Injective f) :
    3 ≤ primeRank 3 G := by
  apply primeRank_ge_of_elementary_embedding (f := f) (hf := hf)
  · intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    congr 1
    simp only [nsmul_eq_mul]
    exact zero_mul _
  · simp [Nat.card_eq_fintype_card]

private theorem three_le_local_rank_of_elementary_embedding
    {G : Type*} [Group G] [Finite G] {t : G} (ht : orderOf t = 2)
    (L : Subgroup G) (hL : L ≤ Subgroup.centralizer ({t} : Set G))
    (f : (Fin 3 → Multiplicative (ZMod 3)) →* L) (hf : Function.Injective f) :
    3 ≤ twoLocalPrimeRank 3 G :=
  (three_le_rank_of_elementary_embedding f hf).trans
    ((primeRank_mono 3 hL).trans
      ((Theory.GroupTheory.isTwoLocal_involution_centralizer ht).primeRank_le 3))

private theorem not_quasithin_of_three_le_local_rank
    {G : Type*} [Group G] [Finite G] (hr : 3 ≤ twoLocalPrimeRank 3 G) :
    ¬ IsQuasithin G := by
  intro hG
  exact (Nat.not_succ_le_self 2)
    (hr.trans (isQuasithin_iff_twoLocalPrimeRank.mp hG 3 (by decide) (by decide)))

private theorem not_quasithin_transport
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (h : ¬ IsQuasithin H) : ¬ IsQuasithin G :=
  fun hG => h ((isQuasithin_congr (G := G) (H := H) e).mp hG)

/-- The literal Lyons quotient contributes rank three if its kernel is coprime to three. -/
public theorem lyons_three_le_local_rank_of_coprime_kernel
    (hk : Nat.Coprime 3 (Nat.card lyonsA11Section.quotientMap.ker)) :
    3 ≤ twoLocalPrimeRank 3 Lyons.LyonsGroup :=
  (Nat.succ_le_of_lt lyonsA11_primeRank_three_gt_two).trans
    (Theory.Quasithin.primeRank_le_twoLocalPrimeRank_of_centralizer_quotient
      lyonsA11Section.involution_order lyonsA11Section.numerator
      lyonsA11Section.centralizes lyonsA11Section.quotientMap lyonsA11Section.surjective 3 hk)

/-- The literal Thompson quotient contributes rank three if its kernel is coprime to three. -/
public theorem thompson_three_le_local_rank_of_coprime_kernel
    (hk : Nat.Coprime 3 (Nat.card thompsonA9Section.quotientMap.ker)) :
    3 ≤ twoLocalPrimeRank 3 Thompson.Model :=
  (Nat.succ_le_of_lt thompsonA9_primeRank_three_gt_two).trans
    (Theory.Quasithin.primeRank_le_twoLocalPrimeRank_of_centralizer_quotient
      thompsonA9Section.involution_order thompsonA9Section.numerator
      thompsonA9Section.centralizes thompsonA9Section.quotientMap thompsonA9Section.surjective 3 hk)

/-- Conditional Lyons exclusion, using only the actual quotient's kernel order. -/
public theorem lyons_not_quasithin_of_coprime_kernel
    (hk : Nat.Coprime 3 (Nat.card lyonsA11Section.quotientMap.ker)) :
    ¬ IsQuasithin Lyons.LyonsGroup :=
  not_quasithin_of_three_le_local_rank (lyons_three_le_local_rank_of_coprime_kernel hk)

/-- Conditional Thompson exclusion, using only the actual quotient's kernel order. -/
public theorem thompson_not_quasithin_of_coprime_kernel
    (hk : Nat.Coprime 3 (Nat.card thompsonA9Section.quotientMap.ker)) :
    ¬ IsQuasithin Thompson.Model :=
  not_quasithin_of_three_le_local_rank (thompson_three_le_local_rank_of_coprime_kernel hk)

/-- Strong quasithinness is also impossible under the Lyons kernel hypothesis. -/
public theorem lyons_not_stronglyQuasithin_of_coprime_kernel
    (hk : Nat.Coprime 3 (Nat.card lyonsA11Section.quotientMap.ker)) :
    ¬ IsStronglyQuasithin Lyons.LyonsGroup :=
  fun h => lyons_not_quasithin_of_coprime_kernel hk h.quasithin

/-- Strong quasithinness is also impossible under the Thompson kernel hypothesis. -/
public theorem thompson_not_stronglyQuasithin_of_coprime_kernel
    (hk : Nat.Coprime 3 (Nat.card thompsonA9Section.quotientMap.ker)) :
    ¬ IsStronglyQuasithin Thompson.Model :=
  fun h => thompson_not_quasithin_of_coprime_kernel hk h.quasithin

/-- An actual elementary 27-subgroup in the Lyons numerator suffices independently of its kernel. -/
public theorem lyons_three_le_local_rank_of_elementary_embedding
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Lyons.SimplicityCertificate.involutionLocalSubgroup) (hf : Function.Injective f) :
    3 ≤ twoLocalPrimeRank 3 Lyons.LyonsGroup :=
  three_le_local_rank_of_elementary_embedding
    Lyons.SimplicityCertificate.orderOf_involutionLocalT
    Lyons.SimplicityCertificate.involutionLocalSubgroup
    Lyons.SimplicityCertificate.involutionLocalSubgroup_le_centralizer_certified f hf

/-- An actual elementary 27-subgroup in the Thompson numerator suffices independently of its kernel. -/
public theorem thompson_three_le_local_rank_of_elementary_embedding
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup)
    (hf : Function.Injective f) :
    3 ≤ twoLocalPrimeRank 3 Thompson.Model :=
  three_le_local_rank_of_elementary_embedding
    Thompson.InvolutionCentralizer.orderOf_generatorA
    Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup
    Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup_le_centralizer f hf

/-- Direct elementary-subgroup route to the Lyons quasithin exclusion. -/
public theorem lyons_not_quasithin_of_elementary_embedding
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Lyons.SimplicityCertificate.involutionLocalSubgroup) (hf : Function.Injective f) :
    ¬ IsQuasithin Lyons.LyonsGroup :=
  not_quasithin_of_three_le_local_rank (lyons_three_le_local_rank_of_elementary_embedding f hf)

/-- Direct elementary-subgroup route to the Thompson quasithin exclusion. -/
public theorem thompson_not_quasithin_of_elementary_embedding
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup)
    (hf : Function.Injective f) :
    ¬ IsQuasithin Thompson.Model :=
  not_quasithin_of_three_le_local_rank (thompson_three_le_local_rank_of_elementary_embedding f hf)

/-- Direct elementary-subgroup route to the Lyons strong-quasithin exclusion. -/
public theorem lyons_not_stronglyQuasithin_of_elementary_embedding
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Lyons.SimplicityCertificate.involutionLocalSubgroup) (hf : Function.Injective f) :
    ¬ IsStronglyQuasithin Lyons.LyonsGroup :=
  fun h => lyons_not_quasithin_of_elementary_embedding f hf h.quasithin

/-- Direct elementary-subgroup route to the Thompson strong-quasithin exclusion. -/
public theorem thompson_not_stronglyQuasithin_of_elementary_embedding
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup)
    (hf : Function.Injective f) :
    ¬ IsStronglyQuasithin Thompson.Model :=
  fun h => thompson_not_quasithin_of_elementary_embedding f hf h.quasithin

/-- Matrix cubic and commutation identities, detected by the literal A₁₁ map,
suffice for the Lyons exclusion. This is the consumer of the cubic constructor. -/
public theorem lyons_not_quasithin_of_cubic_lifts
    (b : Fin 3 → Lyons.SimplicityCertificate.involutionLocalSubgroup)
    (hb : ∀ i, b i ^ 3 = 1) (hc : ∀ i j, Commute (b i) (b j))
    (hi : Function.Injective fun a : Fin 3 → Multiplicative (ZMod 3) =>
      Lyons.SimplicityCertificate.AlternatingQuotient.quotient (b 0) ^ (a 0).toAdd.val *
        (Lyons.SimplicityCertificate.AlternatingQuotient.quotient (b 1) ^ (a 1).toAdd.val *
          Lyons.SimplicityCertificate.AlternatingQuotient.quotient (b 2) ^ (a 2).toAdd.val)) :
    ¬ IsQuasithin Lyons.LyonsGroup :=
  lyons_not_quasithin_of_elementary_embedding
    (Theory.GroupTheory.CommutingCubicTriple.hom b hb hc)
    (Theory.GroupTheory.CommutingCubicTriple.hom_injective_of_images b hb hc
      Lyons.SimplicityCertificate.AlternatingQuotient.quotient hi)

/-- Matrix cubic and commutation identities, detected by the literal A₉ map,
suffice for the Thompson exclusion. No full action-kernel theorem is needed. -/
public theorem thompson_not_quasithin_of_cubic_lifts
    (b : Fin 3 → Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup)
    (hb : ∀ i, b i ^ 3 = 1) (hc : ∀ i j, Commute (b i) (b j))
    (hi : Function.Injective fun a : Fin 3 → Multiplicative (ZMod 3) =>
      Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (b 0) ^ (a 0).toAdd.val *
        (Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (b 1) ^ (a 1).toAdd.val *
          Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom (b 2) ^ (a 2).toAdd.val)) :
    ¬ IsQuasithin Thompson.Model :=
  thompson_not_quasithin_of_elementary_embedding
    (Theory.GroupTheory.CommutingCubicTriple.hom b hb hc)
    (Theory.GroupTheory.CommutingCubicTriple.hom_injective_of_images b hb hc
      Thompson.InvolutionCentralizer.AlternatingQuotient.quotientHom hi)

/-- The fixed Lyons words need only their cube and commutation certificates;
their independence under the actual A₁₁ quotient is already proved. -/
public theorem lyons_not_quasithin_of_word_relations
    (hb : Lyons.SimplicityCertificate.InvolutionElementaryThree.base ^ 3 = 1)
    (hc : ∀ i j, Commute (Lyons.SimplicityCertificate.InvolutionElementaryThree.triple i)
      (Lyons.SimplicityCertificate.InvolutionElementaryThree.triple j)) :
    ¬ IsQuasithin Lyons.LyonsGroup :=
  lyons_not_quasithin_of_elementary_embedding
    (Lyons.SimplicityCertificate.InvolutionElementaryThree.embeddingOfRelations hb hc)
    (Lyons.SimplicityCertificate.InvolutionElementaryThree.embeddingOfRelations_injective hb hc)

/-- The fixed Thompson words need only their cube and commutation certificates;
their independence under the actual A₉ quotient is already proved. -/
public theorem thompson_not_quasithin_of_word_relations
    (hb : Thompson.InvolutionCentralizer.ElementaryThree.base ^ 3 = 1)
    (hc : ∀ i j, Commute (Thompson.InvolutionCentralizer.ElementaryThree.triple i)
      (Thompson.InvolutionCentralizer.ElementaryThree.triple j)) :
    ¬ IsQuasithin Thompson.Model :=
  thompson_not_quasithin_of_elementary_embedding
    (Thompson.InvolutionCentralizer.ElementaryThree.embeddingOfRelations hb hc)
    (Thompson.InvolutionCentralizer.ElementaryThree.embeddingOfRelations_injective hb hc)

/-- The same fixed Lyons matrix relations exclude strong quasithinness. -/
public theorem lyons_not_stronglyQuasithin_of_word_relations
    (hb : Lyons.SimplicityCertificate.InvolutionElementaryThree.base ^ 3 = 1)
    (hc : ∀ i j, Commute (Lyons.SimplicityCertificate.InvolutionElementaryThree.triple i)
      (Lyons.SimplicityCertificate.InvolutionElementaryThree.triple j)) :
    ¬ IsStronglyQuasithin Lyons.LyonsGroup :=
  fun h => lyons_not_quasithin_of_word_relations hb hc h.quasithin

/-- The same fixed Thompson matrix relations exclude strong quasithinness. -/
public theorem thompson_not_stronglyQuasithin_of_word_relations
    (hb : Thompson.InvolutionCentralizer.ElementaryThree.base ^ 3 = 1)
    (hc : ∀ i j, Commute (Thompson.InvolutionCentralizer.ElementaryThree.triple i)
      (Thompson.InvolutionCentralizer.ElementaryThree.triple j)) :
    ¬ IsStronglyQuasithin Thompson.Model :=
  fun h => thompson_not_quasithin_of_word_relations hb hc h.quasithin

/-- The certified elementary subgroup in the Lyons involution centralizer
gives local 3-rank at least three, with every word-relation premise discharged. -/
public theorem lyons_three_le_local_rank :
    3 ≤ twoLocalPrimeRank 3 Lyons.LyonsGroup :=
  lyons_three_le_local_rank_of_elementary_embedding
    Lyons.SimplicityCertificate.InvolutionElementaryThree.embedding
    Lyons.SimplicityCertificate.InvolutionElementaryThree.embedding_injective

/-- The certified elementary subgroup in the Thompson involution centralizer
gives local 3-rank at least three, with every word-relation premise discharged. -/
public theorem thompson_three_le_local_rank :
    3 ≤ twoLocalPrimeRank 3 Thompson.Model :=
  thompson_three_le_local_rank_of_elementary_embedding
    Thompson.InvolutionCentralizer.ElementaryThree.embedding
    Thompson.InvolutionCentralizer.ElementaryThree.embedding_injective

/-- The actual Lyons carrier is not quasithin. -/
public theorem lyons_not_quasithin : ¬ IsQuasithin Lyons.LyonsGroup :=
  not_quasithin_of_three_le_local_rank lyons_three_le_local_rank

/-- The actual Thompson carrier is not quasithin. -/
public theorem thompson_not_quasithin : ¬ IsQuasithin Thompson.Model :=
  not_quasithin_of_three_le_local_rank thompson_three_le_local_rank

/-- The unconditional Lyons exclusion from the simple SQTK domain of I.1.3. -/
public theorem lyons_not_stronglyQuasithin : ¬ IsStronglyQuasithin Lyons.LyonsGroup :=
  fun h => lyons_not_quasithin h.quasithin

/-- The unconditional Thompson exclusion from the simple SQTK domain of I.1.3. -/
public theorem thompson_not_stronglyQuasithin : ¬ IsStronglyQuasithin Thompson.Model :=
  fun h => thompson_not_quasithin h.quasithin

variable {S : Type*} [Group S] [Finite S]

/-- Every finite source group actually isomorphic to Lyons is not quasithin. -/
public theorem not_quasithin_of_equiv_lyons
    (e : S ≃* Lyons.LyonsGroup) : ¬ IsQuasithin S :=
  not_quasithin_transport (G := S) (H := Lyons.LyonsGroup) e lyons_not_quasithin

/-- Every finite source group actually isomorphic to Thompson is not quasithin. -/
public theorem not_quasithin_of_equiv_thompson
    (e : S ≃* Thompson.Model) : ¬ IsQuasithin S :=
  not_quasithin_transport (G := S) (H := Thompson.Model) e thompson_not_quasithin

/-- The Lyons filter for I.1.3, inheriting the source group's instances and
using its actual model isomorphism without any further rank premise. -/
public theorem not_stronglyQuasithin_of_equiv_lyons
    (e : S ≃* Lyons.LyonsGroup) : ¬ IsStronglyQuasithin S :=
  fun h => not_quasithin_of_equiv_lyons e h.quasithin

/-- The Thompson filter for I.1.3, inheriting the source group's instances and
using its actual model isomorphism without any further rank premise. -/
public theorem not_stronglyQuasithin_of_equiv_thompson
    (e : S ≃* Thompson.Model) : ¬ IsStronglyQuasithin S :=
  fun h => not_quasithin_of_equiv_thompson e h.quasithin

/-- The concrete Lyons obstruction transports to every actually identified source model. -/
public theorem not_quasithin_of_equiv_lyons_elementary_embedding
    (e : S ≃* Lyons.LyonsGroup)
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Lyons.SimplicityCertificate.involutionLocalSubgroup) (hf : Function.Injective f) :
    ¬ IsQuasithin S :=
  not_quasithin_transport (G := S) (H := Lyons.LyonsGroup) e
    (lyons_not_quasithin_of_elementary_embedding f hf)

/-- The concrete Thompson obstruction transports to every actually identified source model. -/
public theorem not_quasithin_of_equiv_thompson_elementary_embedding
    (e : S ≃* Thompson.Model)
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup)
    (hf : Function.Injective f) :
    ¬ IsQuasithin S :=
  not_quasithin_transport (G := S) (H := Thompson.Model) e
    (thompson_not_quasithin_of_elementary_embedding f hf)

/-- Source-model form of the Lyons strong-quasithin obstruction. -/
public theorem not_stronglyQuasithin_of_equiv_lyons_elementary_embedding
    (e : S ≃* Lyons.LyonsGroup)
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Lyons.SimplicityCertificate.involutionLocalSubgroup) (hf : Function.Injective f) :
    ¬ IsStronglyQuasithin S :=
  fun h => not_quasithin_of_equiv_lyons_elementary_embedding e f hf h.quasithin

/-- Source-model form of the Thompson strong-quasithin obstruction. -/
public theorem not_stronglyQuasithin_of_equiv_thompson_elementary_embedding
    (e : S ≃* Thompson.Model)
    (f : (Fin 3 → Multiplicative (ZMod 3)) →*
      Thompson.InvolutionCentralizer.AlternatingQuotient.wordSubgroup)
    (hf : Function.Injective f) :
    ¬ IsStronglyQuasithin S :=
  fun h => not_quasithin_of_equiv_thompson_elementary_embedding e f hf h.quasithin

end CFSG.Quasithin.ChapterI.SQTKMultipliers.RankFilters
