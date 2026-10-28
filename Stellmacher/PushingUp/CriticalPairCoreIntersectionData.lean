module

public import Stellmacher.PushingUp.VertexOmegaGeneration

/-!
# The exact critical-pair fixed line and its relative index

For a positive critical pair `(a,b)`, the omega center of the source Sylow
`Z_b Q_a` is exactly `Z_a ∩ Q_b`, and this intersection has relative index
two in `Z_a`. The index is for the actual vertex subgroup, including its
possibly nontrivial global center part.

The omega center lies in `Z_a` and centralizes `Z_b`. Endpoint containment
and the odd-index centralizer theorem therefore place it in `Q_b`.
Conversely, an element of `Z_a ∩ Q_b` has square one and centralizes both
`Q_a` and `Z_b`, so it lies in the source Sylow's omega center.
For the relative index, the reversed fixed-space data identify it with the
cardinality of the opposite acting subgroup in the faithful `SL₂(2)` quotient.
That subgroup is a nontrivial 2-group. A Sylow subgroup of the six-element
quotient has order two, forcing the same cardinality for this actor.

Source: Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (1.4)(a), (2.2),
and the size calculations in (3.3)(1), specialized to `p = 2`, `n = 1`.
Only vertex stabilizers are finite; no finiteness of the graph or amalgam
is assumed.
-/

namespace Stellmacher.PushingUp

open scoped commutatorElement
open AmalgamGraph

universe u

variable {M : Type u} [Group M]

private theorem omega_source_le_core
    [Finite M] (S : Subgroup M) (a b : Vertex S)
    (P : Subgroup (FreeAmalgam S))
    (hSylow : IsSylowSubgroupIn P (stabilizer S a))
    (hZb : vertexZ S b ≤ P)
    (hZaGb : vertexZ S a ≤ stabilizer S b)
    (hOdd : CriticalVertexCentralizer.Conclusion S b) :
    omegaOneCenterAmbient P ≤ vertexZ S a ⊓ vertexTwoCore S b := by
  have hOZa : omegaOneCenterAmbient P ≤ vertexZ S a := by
    obtain ⟨PI, hPI⟩ := hSylow
    rw [← hPI]
    exact le_sSup ⟨PI, rfl⟩
  have hOGb := hOZa.trans hZaGb
  have hOp : IsPGroup 2 (omegaOneCenterAmbient P) :=
    (omegaOneCenterAmbient_elementaryAbelian P).isPGroup
  let O : Subgroup (stabilizer S b) :=
    (omegaOneCenterAmbient P).subgroupOf (stabilizer S b)
  have hOlocal : IsPGroup 2 O :=
    hOp.of_equiv (Subgroup.subgroupOfEquivOfLe hOGb).symm
  have hOC : O ≤ vertexCentralizerLocal S b := by
    intro x hx
    apply (mem_vertexCentralizerLocal_iff S b x).mpr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (mem_omegaOneCenterAmbient_iff P x).mp hx |>.2.2 z (hZb hz)
  have hOcore : O ≤ pCore 2 (stabilizer S b) :=
    hOlocal.le_pCore_of_le_oddIndexOverCore
      hOdd.core_le_centralizer hOdd.centralizer_mod_core_odd hOC
  refine le_inf hOZa ?_
  intro x hx
  exact Subgroup.mem_map_of_mem (stabilizer S b).subtype
    (hOcore (show (⟨x, hOGb hx⟩ : stabilizer S b) ∈ O from hx))

private theorem pSubgroup_card_two_of_sl2Two
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Nat.card P = 2 := by
  obtain ⟨T, hPT⟩ := hp.exists_le_sylow
  have hcardG : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨e⟩
  have hcardT : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, hcardG]
    norm_num [Nat.factorization_mul (by decide : 3 ≠ 0) (by decide : 2 ≠ 0),
      show 6 = 3 * 2 from rfl, Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hdvd : Nat.card P ∣ 2 := by
    rw [← hcardT]
    exact Subgroup.card_dvd_of_le hPT
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact (hne (P.eq_bot_of_card_eq h1)).elim
  · exact h2

/-- The source Sylow omega center is the opposite-core intersection,
which has relative index two in the critical vertex center. -/
public theorem criticalPair_coreIntersection_data [Finite M]
    (S : Subgroup M) (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a b : Vertex S) (hcrit : IsCriticalPair S a b)
    (hb : 0 < criticalDistance S) :
    omegaOneCenterAmbient (vertexZ S b ⊔ vertexTwoCore S a) =
      vertexZ S a ⊓ vertexTwoCore S b ∧
    (vertexZ S a ⊓ vertexTwoCore S b).relIndex (vertexZ S a) = 2 := by
  obtain ⟨hV, hbGa, h22⟩ := criticalPair_sl2Two S T hTS hP hSne hA a b hcrit hb
  obtain ⟨_, _, hinp⟩ := criticalPair_actionInputs S T hTS hP hSne hA a b hcrit hb
  constructor
  · apply le_antisymm
    · exact omega_source_le_core S a b _ h22.sourceSylow le_sup_left
        hinp.left_Z_le_right_stabilizer hinp.oppositeCentralizer_odd
    · intro z hz
      have hzA := (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) z).mp
        (hinp.left_Z_le_coreOmega hz.1)
      apply (mem_omegaOneCenterAmbient_iff _ z).mpr
      refine ⟨Subgroup.mem_sup_right hzA.1, hzA.2.1, ?_⟩
      have hZbcent : z ∈ Subgroup.centralizer (vertexZ S b : Set (FreeAmalgam S)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwB := (mem_omegaOneCenterAmbient_iff (vertexTwoCore S b) w).mp
          (hinp.right_Z_le_coreOmega hw)
        exact (hwB.2.2 z hz.2).symm
      have hQacent : z ∈ Subgroup.centralizer (vertexTwoCore S a : Set (FreeAmalgam S)) := by
        rw [Subgroup.mem_centralizer_iff]
        exact hzA.2.2
      have hPcent : z ∈ Subgroup.centralizer
          ((vertexZ S b ⊔ vertexTwoCore S a : Subgroup (FreeAmalgam S)) : Set _) := by
        rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure,
          Subgroup.mem_centralizer_iff]
        rintro w (hw | hw)
        · exact (Subgroup.mem_centralizer_iff.mp hZbcent) w hw
        · exact (Subgroup.mem_centralizer_iff.mp hQacent) w hw
      exact Subgroup.mem_centralizer_iff.mp hPcent
  · obtain ⟨hVb, haGb, hrevInp⟩ := criticalPair_actionInputs S T hTS hP hSne hA b a
      hinp.critical.reverse_critical hb
    have hfixed := criticalPair_fixedSpaceData S b a haGb hVb hrevInp
    obtain ⟨_, _, hrev22⟩ := criticalPair_sl2Two S T hTS hP hSne hA b a
      hinp.critical.reverse_critical hb
    obtain ⟨e, _⟩ := hrev22.sl2AndNaturalModule
    rw [← hfixed.oppositeImage_card]
    exact pSubgroup_card_two_of_sl2Two _ hrevInp.oppositeImage_isPGroup
      hrevInp.oppositeImage_ne_bot e

end Stellmacher.PushingUp
