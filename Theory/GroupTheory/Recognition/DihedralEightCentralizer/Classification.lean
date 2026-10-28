module

public import Theory.GroupTheory.Recognition.DihedralEightCentralizer.FieldRestriction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.DihedralModels.FieldCard
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.LinearThreeEquiv
public import GorensteinWalter.LinearRingEquiv

/-!
# Classification with a self-centralizing dihedral Sylow subgroup of order eight

The odd core is trivial, the full centralizer of the specified involution is
an actual dihedral Sylow subgroup of order eight, and three divides the group
order. These intrinsic hypotheses give exactly the four possibilities S4,
S5, PSL2(7), and A6. No hypothesis excludes normal index-two subgroups.

Unconditional Gorenstein–Walter and involution fusion first give the whole
PSL2 or PGL2 model. The full centralizer restricts the fields to seven or
nine in PSL2, and three or five in PGL2. The final identifications use the
existing concrete field/permutation comparisons, not recognition by order.
-/

open Subgroup GorensteinWalter
noncomputable section
namespace Theory.GroupTheory.DihedralEightCentralizer
universe u

/-- The four genuine models with a self-centralizing dihedral Sylow subgroup
of order eight, trivial odd core, and order divisible by three. -/
public theorem model_alternative
    {H : Type u} [Group H] [Finite H]
    (S : Sylow 2 H) (eS : S ≃* DihedralGroup 4)
    (t : H) (ht : orderOf t = 2) (hC : centralizer ({t} : Set H) = S)
    (hO : pPrimeCore 2 H = ⊥) (hthree : 3 ∣ Nat.card H) :
    Nonempty (H ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (H ≃* PSL2 (ZMod 7)) ∨
      Nonempty (H ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, iF, finF, hF, hmodels⟩ := exists_linear_model S eS t ht hC hO hthree
  let : Field F := iF
  let : Finite F := finF
  have hCcard : Nat.card (centralizer ({t} : Set H)) = 8 := by
    rw [hC]
    exact (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
  rcases hmodels with hPSL | hPGL
  · let eF := hPSL.some
    rcases DihedralEightRecognition.field_card_of_model hF eF t ht hCcard with hseven | hnine
    · let : Fintype F := Fintype.ofFinite F
      let eK : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
        (by simpa only [Nat.card_eq_fintype_card] using hseven)
      exact Or.inr (Or.inr (Or.inl ⟨eF.trans (psl2RingEquiv eK).symm⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨eF.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hnine)⟩))
  · let eF := hPGL.some
    rcases field_card_of_pgl2_model S eS t ht hC hF eF with hthree | hfive
    · let : Fintype F := Fintype.ofFinite F
      let eK : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three
        (by simpa only [Nat.card_eq_fintype_card] using hthree)
      exact Or.inl ⟨eF.trans ((pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm)⟩
    · exact Or.inr (Or.inl ⟨eF.trans (Theory.PSL2.exists_pgl2_five_equiv F hfive).some⟩)

end Theory.GroupTheory.DihedralEightCentralizer
