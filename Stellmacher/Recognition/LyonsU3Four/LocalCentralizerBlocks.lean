module

public import Stellmacher.Recognition.LyonsU3Four.CentralizerFiveActionCompatibility
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveCharacters
public import Theory.Character.ModularBlock.SmallQuotientCartan
public import Theory.Character.ModularBlock.LocalColumnNorm
public import Theory.Character.ModularBlock.OddClassNonvanishing
public import Theory.GroupTheory.ConjugacyClassSize

/-!
# Genuine principal blocks of the Lyons centralizers

The prescribed modular place on an actual centralizer descends through its
odd core and transports to the order-five semidirect product. Its five genuine
Brauer characters then inflate back, preserving their values, degrees and
Cartan matrix. The order-four centralizer instead has a two-group quotient of
order sixteen, giving its singleton Cartan matrix. Local column orthogonality
converts these computations to actual ambient principal-block column norms.

No local odd core is assumed trivial. These are the local inputs to the ambient
generalized decomposition calculation, not its six ambient columns.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), pp. 373–374, Lemma 2 and the local computation preceding (3.1).
-/

public section
noncomputable section

namespace Stellmacher.Recognition.LyonsU3Four
open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction Cartan CompatibleLocalBlock
attribute [local instance] Fintype.ofFinite

variable {G : Type*} [Group G] [Finite G]

/-- Transport the genuine five-character family through the actual odd core,
retaining its values in the supplied semidirect-product coordinates. -/
theorem involutionCentralizer_principal_decomposition_of_equiv
    (S : Sylow 2 G) (h : SylowStructure S)
    (β : MulAut S) (hβ : orderOf β = 15)
    (α : FiveComplement →* MulAut S)
    (hα : α (Multiplicative.ofAdd 1) = β ^ (3 : ℕ)) (z : G)
    (e : (centralizer ({z} : Set G) ⧸ pPrimeCore 2 (centralizer ({z} : Set G))) ≃*
      LocalFiveGroup S α)
    (b : PrincipalCongruenceBlockData (centralizer ({z} : Set G))) :
    ∃ a : PrincipalDecompositionData b 5,
      (∀ j, a.family.degree j = 1) ∧
      (∀ j k, a.cartan j k = 4 * (3 + if j = k then 1 else 0)) ∧
      (∀ j v, Odd (orderOf v) → BrauerCharacter.value b (a.family.rep j) v =
        fiveLinearEnumeration j (e (QuotientGroup.mk' (pPrimeCore 2 _) v)).right) := by
  let C := centralizer ({z} : Set G)
  let N := pPrimeCore 2 C
  let q := compatibleQuotientPrincipalCongruenceBlockData b N
  have hN : Odd (Nat.card N) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  obtain ⟨aK, hd, hv, hc⟩ :=
    exists_localFivePrincipalDecompositionData S h β hβ α hα (q.transport e)
  let aQ := aK.transportBack e
  let a := aQ.ofOddQuotient b N hN
  refine ⟨a, hd, ?_, ?_⟩
  · intro j k
    exact (aQ.ofOddQuotient_cartan b N hN j k).trans
      ((aK.transportBack_cartan e j k).trans (hc j k))
  · intro j v hvodd
    change BrauerCharacter.value b
      (inflateQuotientRepresentation b N (aQ.family.rep j)) v = _
    rw [inflateQuotientRepresentation_brauerValue b N _ v hvodd]
    have hqodd : Odd (orderOf (QuotientGroup.mk' N v)) :=
      hvodd.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' N) v)
    change BrauerCharacter.value q ((aK.family.rep j).comp e.toMonoidHom)
      (QuotientGroup.mk' N v) = _
    rw [← brauerValue_transport q e _ _ hqodd]
    exact hv j _

/-- The compatible actual involution-centralizer block has degrees all one
and Cartan matrix with diagonal sixteen and off-diagonal twelve. -/
theorem involutionCentralizer_principal_cartan
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (b : PrincipalCongruenceBlockData (centralizer ({z} : Set G))) :
    ∃ a : PrincipalDecompositionData b 5,
      (∀ j, a.family.degree j = 1) ∧
      (∀ j k, a.cartan j k = 4 * (3 + if j = k then 1 else 0)) := by
  obtain ⟨β, α, hβ, hα, e, _⟩ :=
    exists_orderFifteen_centralizerFive_equiv S h d hz hz1
  obtain ⟨a, hd, hc, _⟩ :=
    involutionCentralizer_principal_decomposition_of_equiv S h β hβ α hα z e b
  exact ⟨a, hd, hc⟩

/-- The actual order-four centralizer has the genuine singleton Cartan matrix
`(16)`, at any prescribed characteristic-two modular place. -/
theorem orderFourCentralizer_principal_cartan
    (S : Sylow 2 G) (d : LocalCentralizerData S) (t : S) (ht : orderOf t = 4)
    (b : PrincipalCongruenceBlockData (centralizer ({(t : G)} : Set G))) :
    ∃ a : PrincipalDecompositionData b 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 16 := by
  let C := centralizer ({(t : G)} : Set G)
  have hN : Odd (Nat.card (pPrimeCore 2 C)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := C))
  have hQ : IsPGroup 2 (C ⧸ pPrimeCore 2 C) :=
    IsPGroup.of_card (n := 4) (by simpa using d.orderFour_quotient_card t ht)
  obtain ⟨a, hd, hc⟩ := exists_twoGroup_oddQuotient_cartan b (pPrimeCore 2 C) hN hQ
  exact ⟨a, hd, hc.trans (d.orderFour_quotient_card t ht)⟩

/-- The actual principal-block involution column has squared norm 320. -/
theorem ambient_involution_column_norm
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    {z : G} (hz : z ∈ centerImage S) (hz1 : z ≠ 1)
    (b : PrincipalCongruenceBlockData G) :
    ∑ i ∈ b.block, b.chi i (ConjClasses.mk z) *
      star (b.chi i (ConjClasses.mk z)) = (320 : ℂ) := by
  let l := CompatibleBrauerBlock.localData b (centralizer ({z} : Set G))
  obtain ⟨a, hd, hc⟩ := involutionCentralizer_principal_cartan S h d hz hz1 l
  obtain ⟨n, hn⟩ := S.isPGroup' (⟨z, centerImage_le S hz⟩ : S)
  rw [LocalColumnNorm.principalBlock_local_column_norm b z
    ⟨n, congrArg Subtype.val hn⟩, a.sum_degree_sq]
  norm_num [hd, hc, mul_add, Finset.sum_add_distrib]

/-- The actual principal-block order-four column has squared norm sixteen. -/
theorem ambient_orderFour_column_norm
    (S : Sylow 2 G) (d : LocalCentralizerData S) (t : S) (ht : orderOf t = 4)
    (b : PrincipalCongruenceBlockData G) :
    ∑ i ∈ b.block, b.chi i (ConjClasses.mk (t : G)) *
      star (b.chi i (ConjClasses.mk (t : G))) = (16 : ℂ) := by
  let l := CompatibleBrauerBlock.localData b (centralizer ({(t : G)} : Set G))
  obtain ⟨a, hd, hc⟩ := orderFourCentralizer_principal_cartan S d t ht l
  obtain ⟨n, hn⟩ := S.isPGroup' t
  exact (LocalColumnNorm.principalBlock_local_column_norm b (t : G)
    ⟨n, congrArg Subtype.val hn⟩).trans (singleton_sum_degree_sq l a hd hc)

/-- Nonvanishing of every genuine principal-block row at a central Sylow
element follows directly from its odd conjugacy-class size. -/
theorem ambient_principal_character_center_ne_zero
    (S : Sylow 2 G) {z : G} (hz : z ∈ centerImage S)
    (b : PrincipalCongruenceBlockData G) (i : b.I) (hi : i ∈ b.block) :
    b.chi i (ConjClasses.mk z) ≠ 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply b.character_ne_zero_of_odd_class i hi
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
  apply Nat.coprime_two_left.mp
  apply Nat.prime_two.coprime_iff_not_dvd.mpr
  exact fun hn => S.not_dvd_index (hn.trans
    (Subgroup.index_dvd_of_le (sylow_le_involutionCentralizer S hz)))

end Stellmacher.Recognition.LyonsU3Four
