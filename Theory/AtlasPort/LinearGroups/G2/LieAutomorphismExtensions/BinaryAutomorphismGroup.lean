module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.LocalAmalgam
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound

/-!
# Automorphisms of the actual binary derived group

Full-group conjugation on G₂(2)′ is faithful. Every abstract automorphism
of G₂(2)′ can be corrected by an inner automorphism to preserve both marked
parabolics. These parabolics generate G₂(2)′, so equality on their amalgam
gives equality on the whole group. The full Borel already supplies 64
distinct compatible amalgam automorphisms.

The checked local bound `Nat.card BinaryAmalgamAut ≤ 64` makes this Borel
action exhaustive and proves surjectivity of the actual conjugation map.
Thus full-group conjugation identifies G₂(2) with Aut(G₂(2)′), pointwise
by the original ambient conjugation. In particular every automorphism
preserves both marked types with one common derived-group conjugation.
The conditional assembly is retained as a separate reusable interface.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, and Definition F.4.3,
printed p.274. The inherited G₂ point/line marking is preserved throughout.
-/

@[expose] public section

namespace Atlas.G2.LieAutomorphismExtensions
open LieParabolicSetup

/-- The local count makes the faithful Borel action exhaustive. -/
theorem binaryBorelAmalgamAction_bijective_of_card_le
    (hlocal : Nat.card BinaryAmalgamAut ≤ 64) :
    Function.Bijective binaryBorelAmalgamAction :=
  binaryBorelAmalgamAction_injective.bijective_of_nat_card_le
    (by simpa only [card_binaryBorel] using hlocal)

/-- Local amalgam coverage gives full-group conjugation on every derived automorphism. -/
theorem binaryConjugation_surjective_of_amalgam_card_le
    (hlocal : Nat.card BinaryAmalgamAut ≤ 64) :
    Function.Surjective binaryConjugation := by
  intro a
  obtain ⟨h, hh⟩ := binaryAut_normalize_marked_pair a
  let c : BinaryPairStabilizer := ⟨MulAut.conj h * a, hh 0, hh 1⟩
  obtain ⟨b, hb⟩ := (binaryBorelAmalgamAction_bijective_of_card_le hlocal).2
    (binaryAmalgamRestriction c)
  have he : binaryConjugation b.val = MulAut.conj h * a :=
    congrArg Subtype.val (binaryAmalgamRestriction_injective hb)
  refine ⟨h.val⁻¹ * b.val, ?_⟩
  rw [map_mul, map_inv, binaryConjugation_inner, he, inv_mul_cancel_left]

/-- Conditional assembly from the order bound for the actual finite amalgam. -/
theorem binaryConjugation_bijective_of_amalgam_card_le
    (hlocal : Nat.card BinaryAmalgamAut ≤ 64) :
    Function.Bijective binaryConjugation :=
  ⟨binaryConjugation_injective, binaryConjugation_surjective_of_amalgam_card_le hlocal⟩

/-- The conditional identification uses the original pointwise conjugation map. -/
noncomputable def binaryAutomorphismEquivOfAmalgamCardLe
    (hlocal : Nat.card BinaryAmalgamAut ≤ 64) :
    Model (ZMod 2) ≃* MulAut BinaryDerived :=
  MulEquiv.ofBijective binaryConjugation
    (binaryConjugation_bijective_of_amalgam_card_le hlocal)

@[simp] theorem binaryAutomorphismEquivOfAmalgamCardLe_apply
    (hlocal : Nat.card BinaryAmalgamAut ≤ 64) (g : Model (ZMod 2)) :
    binaryAutomorphismEquivOfAmalgamCardLe hlocal g = binaryConjugation g := rfl

@[simp] theorem binaryAutomorphismEquivOfAmalgamCardLe_apply_val
    (hlocal : Nat.card BinaryAmalgamAut ≤ 64) (g : Model (ZMod 2)) (x : BinaryDerived) :
    (binaryAutomorphismEquivOfAmalgamCardLe hlocal g x).val = g * x.val * g⁻¹ := rfl

/-- Every compatible automorphism of the marked amalgam comes from the full Borel. -/
theorem binaryBorelAmalgamAction_bijective :
    Function.Bijective binaryBorelAmalgamAction :=
  binaryBorelAmalgamAction_bijective_of_card_le card_binaryAmalgamAut_le

/-- Every automorphism of the actual commutator is induced by full-group conjugation. -/
theorem binaryConjugation_surjective : Function.Surjective binaryConjugation :=
  binaryConjugation_surjective_of_amalgam_card_le card_binaryAmalgamAut_le

/-- Full-group conjugation identifies G₂(2) with the automorphisms of G₂(2)′. -/
theorem binaryConjugation_bijective : Function.Bijective binaryConjugation :=
  ⟨binaryConjugation_injective, binaryConjugation_surjective⟩

/-- The automorphism identification is the original conjugation homomorphism. -/
noncomputable def binaryAutomorphismEquiv : Model (ZMod 2) ≃* MulAut BinaryDerived :=
  MulEquiv.ofBijective binaryConjugation binaryConjugation_bijective

@[simp] theorem binaryAutomorphismEquiv_apply (g : Model (ZMod 2)) :
    binaryAutomorphismEquiv g = binaryConjugation g := rfl

@[simp] theorem binaryAutomorphismEquiv_apply_val
    (g : Model (ZMod 2)) (x : BinaryDerived) :
    (binaryAutomorphismEquiv g x).val = g * x.val * g⁻¹ := rfl

/-- Every abstract automorphism retains the inherited G₂ marking, with one
common inner conjugation for both parabolics. -/
theorem binaryAut_preserves_marked_types (a : MulAut BinaryDerived) :
    ∃ h : BinaryDerived, ∀ i : Fin 2,
      (binaryMarkedParabolic i).map a.toMonoidHom =
        (binaryMarkedParabolic i).map (MulAut.conj h).toMonoidHom := by
  obtain ⟨g, rfl⟩ := binaryAutomorphismEquiv.surjective a
  exact binaryConjugation_preserves_marked_types g

end Atlas.G2.LieAutomorphismExtensions
