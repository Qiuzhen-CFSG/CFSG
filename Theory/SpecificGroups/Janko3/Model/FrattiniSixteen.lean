module
public import Theory.SpecificGroups.Janko3.Model.OuterSimpleSections
public import Theory.GroupTheory.SylowFrattiniBounds

/-!
# Four Frattini generators for the actual J₃ Sylow subgroup

The squares of the generator products (1,2), (1,3), (2,3) have eight
distinct ordered products. Evaluation at the single letter zero proves
distinctness using the existing kernel-checked ATLAS permutation tables.
Thus the order-128 Sylow subgroup has Frattini quotient of order at most
sixteen. Sylow conjugacy transports the bound to every actual J₃ marking.
The exterior odd-normalizer consumer uses the missing prime divisor 31
in GL₄(2) to exclude its PSL₅(2) outer section.

Source: Aschbacher--Smith 4.4.10--11, printed p.621; ATLAS J3G1-p6156B0,
with the unchanged generator and composition conventions of
`Model/TwoLocal/Centralizer/S0.lean`.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Janko3.TwoLocal
open CentralizerCertificate

private def squareWord (i : Fin 8) : Model :=
  ((sylowGenerator 1 * sylowGenerator 2)^2)^(i.val%2) *
    ((sylowGenerator 1 * sylowGenerator 3)^2)^((i.val/2)%2) *
    ((sylowGenerator 2 * sylowGenerator 3)^2)^((i.val/4)%2)

private theorem squareWord_injective : Function.Injective squareWord := by
  have h : Function.Injective (fun i : Fin 8 =>
      ((((S0G1 * S0G2)^2)^(i.val%2) * ((S0G1 * S0G3)^2)^((i.val/2)%2) *
        ((S0G2 * S0G3)^2)^((i.val/4)%2)) (0 : Fin 6156))) := by decide +kernel
  intro i j he
  apply h
  rw [S0G1_eq_generator,S0G2_eq_generator,S0G3_eq_generator]
  exact congrArg (fun x : Model => x.val 0) he

/-- Eight square words force a Frattini subgroup of order at least eight. -/
theorem candidate_frattini_card_le_sixteen :
    Nat.card (sylowCandidate ⧸ frattini sylowCandidate) ≤ 16 := by
  let x : Fin 5 → sylowCandidate := fun k => ⟨sylowGenerator k,sylowGenerator_mem k⟩
  let : Fact (IsPGroup 2 sylowCandidate) := ⟨sylowCandidate_isPGroup⟩
  have hx (i j : Fin 5) : (x i * x j)^2 ∈ frattini sylowCandidate :=
    pth_power_mem_frattini_of_isPGroup (p := 2) (x i * x j)
  let w (i : Fin 8) : sylowCandidate :=
    ((x 1 * x 2)^2)^(i.val%2) * ((x 1 * x 3)^2)^((i.val/2)%2) *
      ((x 2 * x 3)^2)^((i.val/4)%2)
  have hw (i : Fin 8) : w i ∈ frattini sylowCandidate :=
    mul_mem (mul_mem (pow_mem (hx 1 2) _) (pow_mem (hx 1 3) _)) (pow_mem (hx 2 3) _)
  let f : Fin 8 → frattini sylowCandidate := fun i => ⟨w i,hw i⟩
  have hf : Function.Injective f := by
    intro i j he
    apply squareWord_injective
    exact congrArg (fun z : frattini sylowCandidate => (z.val : Model)) he
  have h8 : 8 ≤ Nat.card (frattini sylowCandidate) := by
    simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  have hprod := card_eq_card_quotient_mul_card_subgroup (frattini sylowCandidate)
  have hc : Nat.card sylowCandidate = 128 := sylowCandidate_card
  rw [hc] at hprod
  nlinarith

/-- The sharper bound on any carrier marked by the actual J₃ model. -/
theorem sylow_frattini_card_le_sixteen {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* Model) (P : Sylow 2 Q) : Nat.card (P ⧸ frattini P) ≤ 16 := by
  let R := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* R := e.subgroupMap (P : Subgroup Q)
  let S : Sylow 2 Model := sylowCandidate_isPGroup.toSylow (by
    have hc := sylowCandidate.index_mul_card
    rw [sylowCandidate_card,model_card] at hc
    omega)
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr a,
    Theory.GroupTheory.SylowFrattiniBounds.card_congr (R.equiv S)]
  exact candidate_frattini_card_le_sixteen

end Sporadic.Janko3.TwoLocal
