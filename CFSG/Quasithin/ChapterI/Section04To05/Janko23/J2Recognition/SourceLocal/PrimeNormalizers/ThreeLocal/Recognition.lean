module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Preparation

/-!
# The index-six step of the source three-centralizer recognition

The literal component K = E(C_G(t)) embeds in C_G(X)/X. The earlier
five-local theorem shows that its Sylow fives remain Sylow in C_G(X).
Frattini's argument and the preliminary seven-normalizer ratio exclude
the extra factor seven once the two- and three-parts have been calculated.
This module connects those results to the actual relative index [C_G(X):KX].

An inverting element alone proves [N_G(X):C_G(X)] = 2, so that step does
not depend on an already recognized central cover. The inverting element
and the two possible centralizer orders remain explicit premises here.
The source constructions of the actors and Sylow bounds, and recognition
and perfectness of the A₆ cover, are assembled in `CoreRecognition.Source`.
The descendant `Recognition.Source` exposes the completed construction of
`CentralizerCalculation` from the exact 47.1–47.2 inputs and applies it to
the genuine PGL₂(9) quotient. It is a separate entry point because the
actor construction uses the index lemma in this module.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- A genuine inverting actor supplies the index used in the Frattini argument,
without perfectness, a quotient identification, or a Sylow-two model. -/
theorem centralizer_index_of_inverting_element (m : M D)
    (hinv : ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹) :
    (CM D).index = 2 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  have hnot : (m : G) ∉ C D := by
    intro hm
    obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := D.X)
    have hfix : (m : G) * x * (m : G)⁻¹ = x := by
      rw [← hm x x.property, mul_inv_cancel_right]
    have he : x = x⁻¹ := Subtype.ext (hfix.symm.trans (hinv x))
    have hp : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x⁻¹ * x := congrArg (· * x) he
        _ = 1 := inv_mul_cancel x
    have hd := orderOf_dvd_of_pow_eq_one hp
    rw [hx, D.card_X] at hd
    norm_num at hd
  have hd := card_dvd_of_injective _
    (QuotientGroup.kerLift_injective D.X.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut, D.card_X] at hd
  have hd' : (CM D).index ∣ 2 := by
    simpa only [Nat.totient_prime (by decide : Nat.Prime 3)] using hd
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd' with h | h
  · exact (hnot (relIndex_eq_one.mp h m.property)).elim
  · exact h

/-- Application to the source KX, with the seven factor removed. The actor
producer must supply `m`, and the centralizer-core producer must supply the
Sylow bounds; neither premise is hidden in `EarlierConclusions`. -/
theorem component_index_six_of_local_bounds (E : EarlierConclusions D) (m : M D)
    (hinv : ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹)
    (hcard : Nat.card (C D) = 1080 ∨ Nat.card (C D) = 7560) :
    (InvolutionGeometry.rootComponent E.geometry.t ⊔ D.X).relIndex (C D) = 6 := by
  rw [E.component_relIndex]
  exact E.quotientComponent_index_of_card (E.centralizer_card_of_sylow_bounds
    (centralizer_index_of_inverting_element m hinv) hcard)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
