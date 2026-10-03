module

public import Stellmacher.FinalTheorem
public import Stellmacher.Recognition.SimpleInputs
public import Stellmacher.Recognition.DihedralSimple
public import Stellmacher.Recognition.L3TwoSylow
public import Stellmacher.Recognition.OddCoreInvolution
public import BenderSuzuki.FinalTheorem

/-!
# The actual recognized branches of the simple N2 reduction

For a finite nonsolvable simple N2 group, the proved odd-order theorem and
simplicity supply the evenness and trivial two-core needed by Stellmacher's
Theorem 2. Its dihedral alternative, and its local L3(2) alternative, now give
actual A7 or odd-field PSL2 isomorphisms by Gorenstein--Walter. A strongly
embedded subgroup gives actual Bender--Suzuki models. A two-local odd core is
detected in the full centralizer of an involution.

The remaining local types, semidihedral alternative, and order-32 local
configuration remain explicit. This is an intermediate global reduction:
each remaining branch still requires recognition or exclusion before the
isomorphism-based N-group classification is complete.

Source: Stellmacher, Theorem 2 and Section 11; Gorenstein--Walter and
Bender--Suzuki; Kurzweil--Stellmacher 12.1.2 for the odd-core detection.
-/

namespace Stellmacher.Recognition
universe u

public theorem simple_nTwo_recognition_reduction
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S0 : Sylow 2 G) :
    IsSimpleBenderGroup G ∨
    (Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
      ∃ (K : Type u) (instK : Field K) (_ : Finite K),
        let : Field K := instK
        Odd (Nat.card K) ∧ Nonempty (G ≃* GorensteinWalter.PSL2 K)) ∨
    (IsOfSp4TwoType G ∨ IsOfGTwoTwoDerivedType G ∨ IsOfTwistedF4TwoDerivedType G) ∨
    IsSemidihedralGroup S0 ∨
    (Nat.card S0 = 2 ^ 5 ∧ ∃ U : Subgroup G, IsMaximalTwoLocal U ∧
      Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  obtain ⟨heven, hcore, _⟩ := simple_nonsolvable_inputs hns
  rcases theorem_two hN heven hcore S0 with htype | hsylow | h32 | hstrong | hodd
  · rcases htype with hL3 | hSp4 | hG2 | hTits
    · exact Or.inr (Or.inl
        (simple_dihedral_recognition hns S0 (dihedral_sylow_of_l3Two_type S0 hL3)))
    · exact Or.inr (Or.inr (Or.inl (Or.inl hSp4)))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hG2))))
    · exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hTits))))
  · rcases hsylow with hdihedral | hsemidihedral
    · exact Or.inr (Or.inl (simple_dihedral_recognition hns S0 hdihedral))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hsemidihedral)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h32))))
  · obtain ⟨M, hM⟩ := hstrong
    exact Or.inl (bender_suzuki M hM)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (exists_involution_bad_oddCore hN hodd)))))

end Stellmacher.Recognition
