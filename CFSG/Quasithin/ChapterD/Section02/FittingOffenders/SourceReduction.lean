module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Preliminaries
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourcePrime
public import Theory.PPrimeCore

/-!
# Three-core faithfulness for a noncyclic minimum actor

A noncyclic starred cubic actor centralizes every odd prime core except the
three-core, by the original D.2.13 support theorem. The complementary prime
cores generate a normal subgroup of order prime to six. Their join with O₃ is
the literal Fitting subgroup; faithfulness on Fitting therefore gives
faithfulness on O₃, without assuming elementary structure of the three-core.

Source: Aschbacher–Smith, D.2.14, first two paragraphs, printed p.186.
The consumer is the noncyclic D.2.19 reduction with F*=F and O₂=1.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.SourceReduction
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

def oddComplement (G : Type*) [Group G] [Finite G] : Subgroup G :=
  ⨆ p : (Nat.card G).primeFactors.attach, ⨆ (_ : p.1.1 ≠ 3), pCore p.1.1 G

theorem complement_le_fitting : oddComplement G ≤ fittingSubgroup G := by
  exact iSup_le fun p => iSup_le fun _ => pCore_le_fitting G _

theorem fitting_eq_three_sup_complement :
    fittingSubgroup G = pCore 3 G ⊔ oddComplement G := by
  apply le_antisymm
  · rw [fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 3
    · rw [hp]; exact le_sup_left
    · apply le_sup_of_le_right
      change pCore p.1.1 G ≤ ⨆ q : (Nat.card G).primeFactors.attach,
        ⨆ (_ : q.1.1 ≠ 3), pCore q.1.1 G
      exact le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  · exact sup_le (pCore_le_fitting G 3) complement_le_fitting

theorem complement_coprime (hcore : pCore 2 G = ⊥) :
    Nat.Coprime (Nat.card (oddComplement G)) 6 := by
  have hle : oddComplement G ≤ pPrimeCore 3 G := by
    refine iSup_le fun p => iSup_le fun hp => ?_
    have hc : Nat.Coprime 3 (Nat.card (pCore p.1.1 G)) := by
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p.1.1) (G := G)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes (by decide) Fact.out).mpr hp.symm).pow_right n
    exact le_sSup ⟨inferInstance, hc⟩
  have h2 : Nat.Coprime (Nat.card (oddComplement G)) 2 :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).coprime_two_right.of_dvd_left
      (card_dvd_of_le complement_le_fitting)
  have h3 : Nat.Coprime (Nat.card (oddComplement G)) 3 :=
    pPrimeCore_coprime_card.symm.of_dvd_left (card_dvd_of_le hle)
  exact h2.mul_right h3

theorem complement_centralizes (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : 1 < rank A)
    (hcore : pCore 2 G = ⊥) :
    oddComplement G ≤ centralizer (A : Set G) := by
  refine iSup_le fun p => iSup_le fun hp => ?_
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_cases he : p.1.1 = 2
  · rw [he, hcore, commutator_bot_left]
  · by_contra hm
    exact hp (source_lemma_D_2_13_noncyclic_prime ρ hf hA hr
      ((Fact.out : p.1.1.Prime).odd_of_ne_two he) hm)

theorem actor_faithful_three (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥) :
    A ⊓ centralizer (pCore 3 G : Set G) = ⊥ := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hfaith := twoSubgroup_faithful_on_fitting hF hcore A
    (IsElementaryAbelian.isPGroup 2 A)
  apply le_bot_iff.mp
  rw [← hfaith]
  refine le_inf inf_le_left ?_
  rw [fitting_eq_three_sup_complement]
  apply le_centralizer_iff.mpr
  refine sup_le ?_ ?_
  · exact le_centralizer_iff.mp inf_le_right
  · exact (complement_centralizes ρ hf hA hr hcore).trans (centralizer_le inf_le_left)

end CFSG.Quasithin.ChapterD.SourceReduction
