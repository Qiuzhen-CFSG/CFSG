module

public import Theory.Representation.SL2FourNaturalOrbits.Model
import Mathlib.Data.Finset.Prod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Determinants and counts of binary planes in F₄²

An ordered binary basis of a four-element subspace is a pair of distinct
nonzero vectors. Its determinant is independent of the six possible choices
of basis. Counting these bases gives 35 actual subspaces, with determinant
fibers of size five at zero and ten at each nonzero field element.

The only finite calculation enumerates pairs of the sixteen actual vectors;
all passage from pairs to subspaces is proved by explicit equivalences.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §6.2.5,
printed pp.680–681 (PDF pp.697–698).
-/

@[expose] public section

open scoped BigOperators
namespace Representation.SL2FourNatural.PlaneGeometry

abbrev Frame (M : Type*) [Zero M] := {p : M × M // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2}

lemma frame_card {M : Type*} [Zero M] [Finite M] :
    Nat.card (Frame M) = (Nat.card M - 1) * (Nat.card M - 1) - (Nat.card M - 1) := by
  classical
  let := Fintype.ofFinite M
  let s := (Finset.univ : Finset M).erase 0
  have e : Frame M ≃ ↥s.offDiag := Equiv.subtypeEquivRight (fun p => by
    simp [s, Finset.mem_offDiag])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, Finset.offDiag_card]
  simp [s, Nat.card_eq_fintype_card]

lemma four_span {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Finite M] (hc : Nat.card M = 4) (p : Frame M) (w : M) :
    w = 0 ∨ w = p.1.1 ∨ w = p.1.2 ∨ w = p.1.1 + p.1.2 := by
  classical
  let := Fintype.ofFinite M
  obtain ⟨⟨u,v⟩, hu, hv, huv⟩ := p
  have huv0 : u + v ≠ 0 := by
    intro h
    have he := congrArg (u + ·) h
    rw [← add_assoc, ZModModule.add_self, zero_add, add_zero] at he
    exact huv he.symm
  have hs : ({0,u,v,u+v} : Finset M).card = 4 := by
    simp [hu, hv, huv, Ne.symm hu, Ne.symm hv, Ne.symm huv0]
  have he := Finset.eq_univ_of_card ({0,u,v,u+v} : Finset M)
    (by simpa only [← Nat.card_eq_fintype_card, hc] using hs)
  have hw := Finset.mem_univ w
  rw [← he] at hw
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hw

lemma frame_nonempty (U : Plane) : Nonempty (Frame U.1) := by
  have hc : Nat.card (Frame U.1) = 6 := by rw [frame_card, U.2]
  exact (Nat.card_pos_iff.mp (show 0 < Nat.card (Frame U.1) by omega)).1

lemma mem_binary_span (u v w : V) :
    w ∈ Submodule.span (ZMod 2) ({u,v} : Set V) ↔
      w = 0 ∨ w = u ∨ w = v ∨ w = u + v := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a,b,rfl⟩
    have ht (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide
    rcases ht a with rfl | rfl <;> rcases ht b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0,0,by simp⟩
    · exact ⟨1,0,by simp⟩
    · exact ⟨0,1,by simp⟩
    · exact ⟨1,1,by simp⟩

lemma card_binary_span (p : Frame V) :
    Nat.card (Submodule.span (ZMod 2) ({p.1.1,p.1.2} : Set V)) = 4 := by
  classical
  obtain ⟨⟨u,v⟩, hu,hv,huv⟩ := p
  have hsum : u + v ≠ 0 := by
    intro h
    have he := congrArg (u + ·) h
    rw [← add_assoc, ZModModule.add_self, zero_add, add_zero] at he
    exact huv he.symm
  let s : Finset V := {0,u,v,u+v}
  have e : (Submodule.span (ZMod 2) ({u,v} : Set V)) ≃ ↥s :=
    Equiv.subtypeEquivRight (fun w => by simp [mem_binary_span, s])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  simp [s, hu, hv, huv, Ne.symm hu, Ne.symm hv, Ne.symm hsum]

noncomputable def planeOfFrame (p : Frame V) : Plane :=
  ⟨Submodule.span (ZMod 2) {p.1.1,p.1.2}, card_binary_span p⟩

lemma plane_eq_span (U : Plane) (p : Frame U.1) :
    U.1 = Submodule.span (ZMod 2) ({(p.1.1 : V),(p.1.2 : V)} : Set V) := by
  apply le_antisymm
  · intro w hw
    rw [mem_binary_span]
    rcases four_span U.2 p ⟨w,hw⟩ with h | h | h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (Or.inl (congrArg Subtype.val h))
    · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
    · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))
  · rw [Submodule.span_le]
    rintro w (rfl | rfl) <;> exact Subtype.property _

lemma wedge_swap (u v : V) : wedge v u = wedge u v := by
  simpa [wedge, CharTwo.neg_eq, mul_comm] using (neg_sub (u 0 * v 1) (u 1 * v 0)).symm

lemma wedge_self (u : V) : wedge u u = 0 := by simp [wedge, mul_comm]
lemma wedge_add_left (u v w : V) : wedge (u+v) w = wedge u w + wedge v w := by
  simp only [wedge, Pi.add_apply]
  ring
lemma wedge_add_right (u v w : V) : wedge u (v+w) = wedge u v + wedge u w := by
  simp only [wedge, Pi.add_apply]
  ring

lemma wedge_frame_eq (U : Plane) (p q : Frame U.1) :
    wedge (p.1.1 : V) (p.1.2 : V) = wedge (q.1.1 : V) (q.1.2 : V) := by
  obtain ⟨⟨u,v⟩,hu,hv,huv⟩ := p
  obtain ⟨⟨x,y⟩,hx,hy,hxy⟩ := q
  dsimp only at hu hv huv hx hy hxy
  have hx_cases := four_span U.2 ⟨(u,v),hu,hv,huv⟩ x
  have hy_cases := four_span U.2 ⟨(u,v),hu,hv,huv⟩ y
  rcases hx_cases with rfl | rfl | rfl | rfl <;>
    rcases hy_cases with rfl | rfl | rfl | rfl <;>
    first | exact (hx rfl).elim | exact (hy rfl).elim | exact (hxy rfl).elim |
      simp [Submodule.coe_add, wedge_add_right, wedge_self, wedge_swap]

noncomputable def chosenFrame (U : Plane) : Frame U.1 := (frame_nonempty U).some
noncomputable def determinant (U : Plane) : F :=
  wedge ((chosenFrame U).1.1 : V) ((chosenFrame U).1.2 : V)
lemma determinant_eq (U : Plane) (p : Frame U.1) :
    determinant U = wedge (p.1.1 : V) (p.1.2 : V) :=
  wedge_frame_eq U (chosenFrame U) p


def forgetFrame (U : Plane) (p : Frame U.1) : Frame V :=
  ⟨((p.1.1 : V), (p.1.2 : V)),
    (fun h => p.2.1 (Subtype.ext h)),
    (fun h => p.2.2.1 (Subtype.ext h)),
    (fun h => p.2.2.2 (Subtype.ext h))⟩

lemma planeOfFrame_forget (U : Plane) (p : Frame U.1) :
    planeOfFrame (forgetFrame U p) = U := by
  apply Subtype.ext
  exact (plane_eq_span U p).symm

lemma forgetFrame_injective (U : Plane) : Function.Injective (forgetFrame U) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg (fun x : Frame V => x.1.1) h
  · exact congrArg (fun x : Frame V => x.1.2) h

lemma forget_bijective : Function.Bijective (fun p : Σ U : Plane, Frame U.1 => forgetFrame p.1 p.2) := by
  constructor
  · rintro ⟨U,p⟩ ⟨W,q⟩ he
    change forgetFrame U p = forgetFrame W q at he
    have hUW : U = W := by
      rw [← planeOfFrame_forget U p, ← planeOfFrame_forget W q, he]
    subst W
    have hpq : p = q := forgetFrame_injective U he
    subst q
    rfl
  · intro p
    let U := planeOfFrame p
    have hu : p.1.1 ∈ U.1 := Submodule.subset_span (by simp)
    have hv : p.1.2 ∈ U.1 := Submodule.subset_span (by simp)
    let q : Frame U.1 := ⟨(⟨p.1.1,hu⟩,⟨p.1.2,hv⟩),
      (fun h => p.2.1 (congrArg Subtype.val h)),
      (fun h => p.2.2.1 (congrArg Subtype.val h)),
      (fun h => p.2.2.2 (congrArg Subtype.val h))⟩
    exact ⟨⟨U,q⟩, rfl⟩

noncomputable def frameEquiv : (Σ U : Plane, Frame U.1) ≃ Frame V :=
  Equiv.ofBijective _ forget_bijective

instance : Finite Plane := by
  apply Finite.of_surjective planeOfFrame
  intro U
  exact ⟨forgetFrame U (chosenFrame U), planeOfFrame_forget U _⟩

lemma card_planes : Nat.card Plane = 35 := by
  classical
  let := Fintype.ofFinite Plane
  have hf (U : Plane) : Nat.card (Frame U.1) = 6 := by rw [frame_card, U.2]
  have h := Nat.card_congr frameEquiv
  rw [Nat.card_sigma, frame_card, Nat.card_eq_fintype_card (α := V), card_vector] at h
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card]
  omega

noncomputable def determinantFiberEquiv (d : F) :
    (Σ U : {U : Plane // determinant U = d}, Frame U.1.1) ≃
      {p : Frame V // wedge p.1.1 p.1.2 = d} :=
  (Equiv.subtypeSigmaEquiv (fun U : Plane => Frame U.1) (fun U => determinant U = d)).symm.trans
    (frameEquiv.subtypeEquiv (fun p => by
      change determinant p.1 = d ↔ wedge (p.2.1.1 : V) (p.2.1.2 : V) = d
      rw [determinant_eq p.1 p.2]))

lemma card_frame_determinant : ∀ d : F,
    Fintype.card {p : V × V // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ wedge p.1 p.2 = d} =
      if d = 0 then 30 else 60 := by decide +kernel

lemma card_determinant_fiber (d : F) :
    Nat.card {U : Plane // determinant U = d} = if d = 0 then 5 else 10 := by
  classical
  let := Fintype.ofFinite {U : Plane // determinant U = d}
  have hf (U : {U : Plane // determinant U = d}) : Nat.card (Frame U.1.1) = 6 := by
    rw [frame_card, U.1.2]
  have he : {p : Frame V // wedge p.1.1 p.1.2 = d} ≃
      {p : V × V // p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2 ∧ wedge p.1 p.2 = d} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun p : V × V => p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.1 ≠ p.2)
      (fun p : V × V => wedge p.1 p.2 = d)).trans
      (Equiv.subtypeEquivRight (fun _ => by tauto))
  have h := Nat.card_congr ((determinantFiberEquiv d).trans he)
  rw [Nat.card_sigma, Nat.card_eq_fintype_card (α := {p : V × V // _}),
    card_frame_determinant] at h
  simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card]
  split_ifs at h ⊢ <;> omega

end Representation.SL2FourNatural.PlaneGeometry
