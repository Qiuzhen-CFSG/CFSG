module
public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.FiniteStructure
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# One-involution centralizer exclusions for J₁, J₄, Held and Rudvalis

Actual involution fusion reduces each specified involution to its native
centralizer models. J₁, Held and the second J₄ model have a factor three in
their orders; the first J₄ model retains an order-three scalar in its actual
two-core quotient. Both Rudvalis models have a factor five, including the
class whose centralizer is three-free. Hence none of these carriers has an
involution with a two-group centralizer. No Sylow-centrality premise is used.

Source: Aschbacher--Smith G.4.1, printed p.342, and the involution-centralizer
inspection referenced there; the imported native proofs retain their GLS3
and ATLAS conventions.
-/

public section

open Subgroup Theory.GroupTheory.CentralizerSmallKernelTransport
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem not_two_of_prime_dvd {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card G) :
    ¬ IsPGroup 2 G := by
  intro h
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp h
  have hd2 : p ∣ 2 := hp.dvd_of_dvd_pow (hd.trans hn)
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one)

theorem Janko1.not_isPGroup_involution_centralizer (i : Janko1.Model) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set Janko1.Model)) := by
  intro hp
  obtain ⟨g, hg⟩ := Janko1.involution_fusion_of_card Janko1.card_model i hi
  have he : MulAut.conj g i = Janko1.a := hg
  have hp' := hp.of_equiv (centralizerEquiv (MulAut.conj g) i)
  rw [he] at hp'
  have hp'' := hp'.of_equiv Janko1.InvolutionCentralizer.productEquiv
  apply not_two_of_prime_dvd Nat.prime_three (by decide) (G := Janko1.InvolutionCentralizer.ProductModel) _ hp''
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  change 3 ∣ Nat.card (Multiplicative (ZMod 2) × alternatingGroup (Fin 5))
  rw [Nat.card_prod, hA]
  norm_num

theorem Janko4.not_isPGroup_involution_centralizer (i : Janko4.Model) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set Janko4.Model)) := by
  intro hp
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second i hi with h | h
  · obtain ⟨e⟩ := h
    have hp0 : IsPGroup 2 Janko4.InvolutionCentralizers.First.centralizer := hp.of_equiv e
    have hp' := hp0.to_quotient (pCore 2 Janko4.InvolutionCentralizers.First.centralizer)
    have hc := hp'.orderOf_coprime (by decide : Nat.Coprime 2 3)
      (Janko4.InvolutionCentralizers.First.tripleCoverQuotientExtension.inl
        Sporadic.Mathieu.M22TripleCover.scalar)
    rw [Janko4.InvolutionCentralizers.First.tripleCoverQuotientExtension_scalar_order] at hc
    norm_num at hc
  · obtain ⟨e⟩ := h
    have hp0 : IsPGroup 2 Janko4.InvolutionCentralizers.Second.ambientCentralizer := hp.of_equiv e
    apply not_two_of_prime_dvd Nat.prime_three (by decide) _ hp0
    rw [Janko4.InvolutionCentralizers.Second.ambient_card]
    decide

theorem Held.not_isPGroup_involution_centralizer (i : Held.He) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set Held.He)) := by
  intro hp
  rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage i hi with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · have hp' := hp.of_equiv (centralizerEquiv (MulAut.conj g) Held.a).symm
    apply not_two_of_prime_dvd Nat.prime_three (by decide) _ hp'
    rw [← Held.InvolutionFixedData.TwoA.centralizer_eq,
      Held.InvolutionFixedData.TwoA.FiniteStructure.centralizer_card]
    decide
  · have hp' := hp.of_equiv (centralizerEquiv (MulAut.conj g)
      (Held.TwoLocalCandidates.max5First ^ 4)).symm
    apply not_two_of_prime_dvd Nat.prime_three (by decide) _ hp'
    rw [Held.InvolutionFixedData.TwoB.centralizer_eq_max5,
      Held.InvolutionFixedData.TwoB.max5_card]
    decide

theorem Rudvalis.not_isPGroup_involution_centralizer (i : Rudvalis.Model) (hi : orderOf i = 2) :
    ¬ IsPGroup 2 (centralizer ({i} : Set Rudvalis.Model)) := by
  apply not_two_of_prime_dvd (by decide : Nat.Prime 5) (by decide)
  rcases Rudvalis.InvolutionCentralizers.centralizer_representatives i hi with h | h
  · rw [Rudvalis.InvolutionCentralizers.first_centralizer_card h.1]
    decide
  · rw [Rudvalis.InvolutionCentralizers.second_class_centralizer_card h.1]
    decide
