module

public import Theory.Mathieu.M12.Properties.InvolutionClasses
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators
public import Theory.Comparator.Defs
public import BenderSuzuki.SE.StrongEmbeddingConjugacy

@[expose] public section

open scoped Pointwise

noncomputable section

namespace Stellmacher.SectionNine.M12Realization

open Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def centerPerm : Equiv.Perm (Fin 12) :=
  Equiv.swap 1 5 * Equiv.swap 3 4 * Equiv.swap 6 8 * Equiv.swap 10 11

def planePerm : Equiv.Perm (Fin 12) :=
  Equiv.swap 1 5 * Equiv.swap 2 0 * Equiv.swap 6 8 * Equiv.swap 7 9

private theorem mem_of_blocks (permutation : Equiv.Perm (Fin 12))
    (hblocks : permutation • m12Blocks = m12Blocks) : permutation ∈ M12 := by
  apply (mem_M12_iff permutation).mpr
  exact_mod_cast hblocks

theorem centerPerm_mem : centerPerm ∈ M12 := by
  apply mem_of_blocks
  decide +kernel

theorem planePerm_mem : planePerm ∈ M12 := by
  apply mem_of_blocks
  decide +kernel

def centerElement : M12 := ⟨centerPerm, centerPerm_mem⟩

def planeElement : M12 := ⟨planePerm, planePerm_mem⟩

def centerPlane : Subgroup M12 :=
  Subgroup.closure ({centerElement, planeElement} : Set M12)

def firstLocal : Subgroup M12 :=
  Subgroup.normalizer (centerPlane : Set M12)

def secondLocal : Subgroup M12 :=
  Subgroup.centralizer ({centerElement} : Set M12)

def sylowCandidate : Subgroup M12 := firstLocal ⊓ secondLocal

theorem centerElement_order : orderOf centerElement = 2 := by
  rw [← Subgroup.orderOf_coe]
  change orderOf centerPerm = 2
  apply orderOf_eq_prime <;> decide +kernel

theorem planeElement_order : orderOf planeElement = 2 := by
  rw [← Subgroup.orderOf_coe]
  change orderOf planePerm = 2
  apply orderOf_eq_prime <;> decide +kernel

theorem centerPlane_isKleinFour : IsKleinFour centerPlane := by
  apply Subgroup.isKleinFour_closure_pair_of_orderOf centerElement planeElement
    centerElement_order planeElement_order
  · intro heq
    have hperm := congrArg (fun element : M12 => (element : Equiv.Perm (Fin 12)) 2) heq
    change (2 : Fin 12) = 0 at hperm
    contradiction
  · change centerElement * planeElement = planeElement * centerElement
    apply Subtype.ext
    decide +kernel

theorem centerPlane_card : Nat.card centerPlane = 4 := centerPlane_isKleinFour.card_four

end Stellmacher.SectionNine.M12Realization

namespace Stellmacher.SectionNine.M12Realization

open Sporadic.Mathieu

theorem no_strongly_embedded :
    ¬ ∃ subgroup : Subgroup M12, _root_.IsStronglyEmbedded subgroup := by
  rintro ⟨subgroup, hproper, hinvolution, hintersection⟩
  have hstrong : BenderSuzuki.IsStronglyEmbedded subgroup := by
    refine ⟨hproper, hinvolution, ?_⟩
    intro conjugator hout element hmem hconj
    apply hintersection conjugator⁻¹ (by simpa using hout) element
    exact ⟨hmem, hconj⟩
  have hfirst : BenderSuzuki.PFAppendixIII.IsInvolution m12Involution2A := by
    exact ⟨fun heq => by simpa [heq] using m12Involution2A_order,
      by simpa only [m12Involution2A_order] using pow_orderOf_eq_one m12Involution2A⟩
  have hsecond : BenderSuzuki.PFAppendixIII.IsInvolution m12Involution2B := by
    exact ⟨fun heq => by simpa [heq] using m12Involution2B_order,
      by simpa only [m12Involution2B_order] using pow_orderOf_eq_one m12Involution2B⟩
  obtain ⟨conjugator, heq⟩ := hstrong.involutions_conjugate hfirst hsecond
  have hsupp := congrArg (fun element : M12 =>
    (element : Equiv.Perm (Fin 12)).support.card) heq
  change ((conjugator : Equiv.Perm (Fin 12))⁻¹ *
    (m12Involution2A : Equiv.Perm (Fin 12)) * conjugator).support.card =
      (m12Involution2B : Equiv.Perm (Fin 12)).support.card at hsupp
  have hcard := Equiv.Perm.card_support_conj
    (σ := (conjugator : Equiv.Perm (Fin 12))⁻¹)
    (τ := (m12Involution2A : Equiv.Perm (Fin 12)))
  simp only [inv_inv] at hcard
  rw [hcard] at hsupp
  rw [m12Involution2A_support_card, m12Involution2B_support_card] at hsupp
  contradiction

end Stellmacher.SectionNine.M12Realization
