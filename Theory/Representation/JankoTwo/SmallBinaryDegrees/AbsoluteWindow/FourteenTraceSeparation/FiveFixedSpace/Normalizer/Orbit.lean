module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneOrbit
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group

/-!
# Three conjugate lines from a fixed-point-free cubic

In a group of order 25, an automorphism with cube one and no nonidentity
fixed points moves every subgroup of order five. Otherwise its restriction
would have order dividing both three and |Aut(C₅)| = 4. The starting line and
its first two images are therefore distinct members of the literal ambient
normalizer orbit. This supplies the orbit bound for the ATLAS five-plane.
-/

namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveNormalizer
open Subgroup Representation.BinaryCoprimeDegree

variable {E : Type*} [Group E] [Finite E]

private theorem line_moved (e : MulAut E) (he3 : e ^ 3 = 1)
    (hfix : ∀ u : E, e u = u → u = 1)
    (H : Subgroup E) (hH : Nat.card H = 5) : H.map e.toMonoidHom ≠ H := by
  intro he
  let f : MulAut H := (e.subgroupMap H).trans (MulEquiv.subgroupCongr he)
  have hf (u : H) : (f u : E) = e u := rfl
  have hf3 : f ^ 3 = 1 := by
    ext u
    change e (e (e (u : E))) = u
    have h := congrArg (fun a : MulAut E => a u) he3
    simpa [pow_succ] using h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic H := isCyclic_of_prime_card hH
  have hc : Nat.card (MulAut H) = 4 := by rw [IsCyclic.card_mulAut, hH]; decide
  have hf4 : f ^ 4 = 1 := by simpa [hc] using (pow_card_eq_one' (x := f))
  have hf1 : f = 1 := by
    calc
      f = f ^ 4 * (f ^ 3)⁻¹ := by group
      _ = 1 := by rw [hf3, hf4]; simp
  have hbot : H = ⊥ := by
    apply eq_bot_iff.mpr
    intro u hu
    apply (mem_bot).mpr
    apply hfix
    have h := congrArg (fun a : MulAut H => (a ⟨u, hu⟩ : E)) hf1
    exact h
  rw [hbot] at hH
  simp at hH

variable {G : Type*} [Group G] [Finite G]

public theorem orbit_three (P : Subgroup G) (hP : Nat.card P = 25)
    (n : normalizer (P : Set G)) (hn : n ^ 3 = 1)
    (hfix : ∀ u : P, P.normalizerMonoidHom n u = u → u = 1)
    (H : Subgroup P) (hH : H.index = 5) :
    3 ≤ Nat.card (normalizerHyperplaneOrbit P H) := by
  let e := P.normalizerMonoidHom n
  have he3 : e ^ 3 = 1 := by rw [← map_pow, hn, map_one]
  have hc : Nat.card H = 5 := by
    have h := H.card_mul_index
    rw [hP, hH] at h
    omega
  let F : Subgroup P → Subgroup P := fun K => K.map e.toMonoidHom
  have hF3 (K : Subgroup P) : F (F (F K)) = K := by
    change ((K.map e.toMonoidHom).map e.toMonoidHom).map e.toMonoidHom = K
    rw [map_map, map_map]
    have hh : (e.toMonoidHom.comp e.toMonoidHom).comp e.toMonoidHom = MonoidHom.id P := by
      ext u
      have h := congrArg (fun a : MulAut P => a u) he3
      simpa [pow_succ] using h
    rw [hh, map_id]
  have h01 : F H ≠ H := line_moved e he3 hfix H hc
  have h02 : F (F H) ≠ H := by
    intro hh
    have h := congrArg F hh
    rw [hF3] at h
    exact h01 h.symm
  have h12 : F H ≠ F (F H) := by
    intro hh
    have h := congrArg (fun K => F (F K)) hh
    simp only [hF3] at h
    exact h01 h.symm
  have hm0 : H ∈ normalizerHyperplaneOrbit P H := mem_normalizerHyperplaneOrbit P H
  have hm1 : F H ∈ normalizerHyperplaneOrbit P H := ⟨n, rfl⟩
  have hm2 : F (F H) ∈ normalizerHyperplaneOrbit P H := by
    refine ⟨n * n, ?_⟩
    change H.map (P.normalizerMonoidHom (n * n)).toMonoidHom = _
    rw [map_mul]
    change H.map (e * e).toMonoidHom = (H.map e.toMonoidHom).map e.toMonoidHom
    exact (H.map_map e.toMonoidHom e.toMonoidHom).symm
  have hs : ({H, F H, F (F H)} : Set (Subgroup P)) ⊆ normalizerHyperplaneOrbit P H := by
    intro K hK
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl | rfl
    · exact hm0
    · exact hm1
    · exact hm2
  have hb := Set.ncard_le_ncard hs
  have ht : ({H, F H, F (F H)} : Set (Subgroup P)).ncard = 3 := by
    simp [Set.ncard_insert_of_notMem, h01.symm, h02.symm, h12]
  rw [ht] at hb
  exact hb
end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveNormalizer
