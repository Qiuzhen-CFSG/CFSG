module

public import Theory.GroupTheory.WeakClosureNormalizer
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The weak-closure contradiction in 13.9.10

The literal intersection `B ⊓ Q` contains both marked involutions `z,t`.
Consequently 13.9.7 puts its ambient centralizer inside `J(T)`, where the
marked local calculation identifies it with `B`. This identity transports
to every actual conjugate of the intersection.

In the factor-alignment argument, an order-sixteen subgroup of
`C_G((B ⊓ Q)^g)` lying in `K = N_G(B)` therefore equals `B^g`. Weak
closure excludes the marked vector `z^g` outside `B`. The final theorem
applies this contradiction to a witness obtained from `E ≰ R₁`; the
construction of that witness and the factor comparison remain explicit
inputs, not conclusions asserted by this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.9.10, printed p.973 (PDF p.990).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.FusionAlignment

open Subgroup

variable {G : Type*} [Group G]

/-- The pair-centralizer result 13.9.7 applies to the literal `B ∩ Q`. -/
theorem centralizer_intersection_le (B Q J : Subgroup G) (z t : G)
    (hz : z ∈ B ⊓ Q) (ht : t ∈ B ⊓ Q)
    (hpair : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) = J) :
    centralizer (B ⊓ Q : Set G) ≤ J := by
  rw [← hpair]
  exact le_inf
    (centralizer_le (Set.singleton_subset_iff.mpr hz))
    (centralizer_le (Set.singleton_subset_iff.mpr ht))

/-- The local centralizer computation inside `J(T)` determines the full
ambient centralizer of `B ∩ Q`. -/
theorem centralizer_intersection_eq (B Q J : Subgroup G) (z t : G)
    (hz : z ∈ B ⊓ Q) (ht : t ∈ B ⊓ Q)
    (hpair : centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G) = J)
    (hlocal : J ⊓ centralizer (B ⊓ Q : Set G) = B) :
    centralizer (B ⊓ Q : Set G) = B := by
  calc
    centralizer (B ⊓ Q : Set G) = J ⊓ centralizer (B ⊓ Q : Set G) :=
      (inf_eq_right.mpr (centralizer_intersection_le B Q J z t hz ht hpair)).symm
    _ = B := hlocal

private theorem conjugate_centralizer (D : Subgroup G) (g : G) :
    centralizer (D.map (MulAut.conj g).toMonoidHom : Set G) =
      (centralizer (D : Set G)).map (MulAut.conj g).toMonoidHom := by
  let f := MulAut.conj g
  apply le_antisymm
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using
      hx (f y) (mem_map_of_mem f.toMonoidHom hy)
  · exact map_centralizer_le_centralizer_image _ _

/-- Conjugation preserves the actual intersection and its full centralizer. -/
theorem centralizer_conjugate_intersection (B Q : Subgroup G)
    (hC : centralizer (B ⊓ Q : Set G) = B) (g : G) :
    centralizer
      (B.map (MulAut.conj g).toMonoidHom ⊓ Q.map (MulAut.conj g).toMonoidHom : Set G) =
      B.map (MulAut.conj g).toMonoidHom := by
  calc
    _ = centralizer ((B ⊓ Q).map (MulAut.conj g).toMonoidHom : Set G) :=
      congrArg (fun D : Subgroup G => centralizer (D : Set G))
        (map_inf B Q (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
    _ = (centralizer (B ⊓ Q : Set G)).map (MulAut.conj g).toMonoidHom :=
      conjugate_centralizer (B ⊓ Q) g
    _ = B.map (MulAut.conj g).toMonoidHom :=
      congrArg (fun D : Subgroup G => D.map (MulAut.conj g).toMonoidHom) hC

/-- An equal-size subgroup inside the conjugate intersection centralizer
identifies the conjugate of `B`. This is the order-sixteen comparison on p.973. -/
theorem conjugate_eq_of_centralizer_card [Finite G]
    (B Q D : Subgroup G) (g : G)
    (hC : centralizer (B ⊓ Q : Set G) = B)
    (hD : D ≤ centralizer
      (B.map (MulAut.conj g).toMonoidHom ⊓ Q.map (MulAut.conj g).toMonoidHom : Set G))
    (hcard : Nat.card D = Nat.card B) :
    B.map (MulAut.conj g).toMonoidHom = D := by
  rw [centralizer_conjugate_intersection B Q hC g] at hD
  apply (eq_of_le_of_card_ge hD ?_).symm
  rw [Nat.card_congr (B.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv] at hcard
  exact hcard.ge

/-- The source weak-closure contradiction, retaining `K = N_G(B)`,
the literal `B^g ∩ Q^g`, and the conjugated marked vector. -/
theorem false_of_conjugate_centralizer_witness [Finite G]
    (T : Sylow 2 G) (B Q D : Subgroup G) (z g : G)
    (hBT : B ≤ (T : Subgroup G))
    (hweak : ∀ a : G, B.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) →
      B.map (MulAut.conj a).toMonoidHom = B)
    (hzB : z ∈ B) (houtside : MulAut.conj g z ∉ B)
    (hC : centralizer (B ⊓ Q : Set G) = B)
    (hD : D ≤ centralizer
      (B.map (MulAut.conj g).toMonoidHom ⊓ Q.map (MulAut.conj g).toMonoidHom : Set G))
    (hcard : Nat.card D = Nat.card B) (hDK : D ≤ normalizer (B : Set G)) : False := by
  have hBD := conjugate_eq_of_centralizer_card B Q D g hC hD hcard
  have hfix := T.conjugate_eq_of_le_normalizer_of_weakly_closed B hBT hweak g
    (hBD.le.trans hDK)
  apply houtside
  rw [← hfix]
  exact mem_map_of_mem _ hzB

/-- The factor-alignment implication. Its witness premise is the explicit
local `R₁ O₂(X)` construction in the source, still to be discharged. -/
theorem factor_alignment_of_centralizer_witnesses [Finite G]
    (T : Sylow 2 G) (B Q E R₁ : Subgroup G) (z : G)
    (hBT : B ≤ (T : Subgroup G))
    (hweak : ∀ a : G, B.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) →
      B.map (MulAut.conj a).toMonoidHom = B)
    (hzB : z ∈ B) (hC : centralizer (B ⊓ Q : Set G) = B)
    (hwitness : ¬ E ≤ R₁ → ∃ (g : G) (D : Subgroup G),
      MulAut.conj g z ∉ B ∧
      D ≤ centralizer
        (B.map (MulAut.conj g).toMonoidHom ⊓ Q.map (MulAut.conj g).toMonoidHom : Set G) ∧
      Nat.card D = Nat.card B ∧ D ≤ normalizer (B : Set G)) : E ≤ R₁ := by
  by_contra hE
  obtain ⟨g, D, hout, hD, hc, hDK⟩ := hwitness hE
  exact false_of_conjugate_centralizer_witness T B Q D z g hBT hweak hzB hout hC hD hc hDK

end CFSG.Quasithin.Chapter13.Section09.FusionAlignment
