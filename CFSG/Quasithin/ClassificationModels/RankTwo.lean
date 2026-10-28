module

public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.SpecificGroups.ReeF4.Model

/-!
# The complete rank-two output family

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Theorem 0.1.2 (printed p.4), Remark A.2.4 (p.33),
and Theorem D/14.8.2 (pp.1078–1079).

The field parameter is `2^f`, including for the twisted groups. In particular
the Ree alternative has `f = 2*m+1` with `m ≥ 1` and uses the fixed subgroup
of the exceptional F4 field twist. The full group at `m = 0` is not an output:
the simple endpoint is separately represented by `Tits.ParrottGroup`.
The unitary parameter is the fixed-field order, so U₅ occurs only at q = 4.

The earlier partial family remains unchanged. Its inclusion and the exact
decomposition below add precisely the Ree alternative, preserving all actual
isomorphism witnesses and the small derived-group conventions. These are
definitions and catalogue transports, not classification or simplicity results.
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.ClassificationModels

/-- All simple rank-two outputs over the field of order `2^f`, with U₅ only
at q = 4, as required by the Main Theorem. -/
inductive IsRankTwoModel (G : Type u) [Group G] (f : ℕ) : Prop
  | linear (hf : 1 ≤ f) (iso : ClassicalGroup.IsPSL G 3 (2 ^ f))
  | unitary_four (hf : 1 ≤ f) (iso : ClassicalGroup.IsPSU G 4 (2 ^ f))
  | unitary_five (hf : f = 2) (iso : ClassicalGroup.IsPSU G 5 (2 ^ f))
  | symplectic (hf : 2 ≤ f) (iso : ClassicalGroup.IsPSp G 2 (2 ^ f))
  | g2 (hf : 2 ≤ f) (iso : IsG2At G (2 ^ f))
  | triality (hf : 1 ≤ f) (iso : Triality.Standard.IsTrialityGroupAt (2 ^ f) G)
  | ree_f4 (m : ℕ) (hm : 1 ≤ m) (hf : f = 2 * m + 1)
      (iso : Nonempty (G ≃* ReeF4.Model m))
  | symplectic_derived (hf : f = 1)
      (iso : Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))))
  | g2_derived (hf : f = 1)
      (iso : Nonempty (G ≃* commutator (Atlas.G2.Model (ZMod 2))))
  | tits (hf : f = 1) (iso : Nonempty (G ≃* Tits.ParrottGroup))

variable {G : Type u} {H : Type v} [Group G] [Group H] {f : ℕ}

theorem IsRankTwoModelWithoutReeF4.toRankTwoModel
    (h : IsRankTwoModelWithoutReeF4 G f) : IsRankTwoModel G f := by
  cases h with
  | linear hf iso => exact .linear hf iso
  | unitary_four hf iso => exact .unitary_four hf iso
  | unitary_five hf iso => exact .unitary_five hf iso
  | symplectic hf iso => exact .symplectic hf iso
  | g2 hf iso => exact .g2 hf iso
  | triality hf iso => exact .triality hf iso
  | symplectic_derived hf iso => exact .symplectic_derived hf iso
  | g2_derived hf iso => exact .g2_derived hf iso
  | tits hf iso => exact .tits hf iso

/-- The extension adds exactly the genuine Ree family at its specified field
exponents. In particular it adds no general Ree model at exponent one. -/
theorem isRankTwoModel_iff_withoutReeF4_or_reeF4 :
    IsRankTwoModel G f ↔ IsRankTwoModelWithoutReeF4 G f ∨
      ∃ m : ℕ, 1 ≤ m ∧ f = 2 * m + 1 ∧ Nonempty (G ≃* ReeF4.Model m) := by
  constructor
  · intro h
    cases h with
    | linear hf iso => exact .inl (.linear hf iso)
    | unitary_four hf iso => exact .inl (.unitary_four hf iso)
    | unitary_five hf iso => exact .inl (.unitary_five hf iso)
    | symplectic hf iso => exact .inl (.symplectic hf iso)
    | g2 hf iso => exact .inl (.g2 hf iso)
    | triality hf iso => exact .inl (.triality hf iso)
    | ree_f4 m hm hf iso => exact .inr ⟨m, hm, hf, iso⟩
    | symplectic_derived hf iso => exact .inl (.symplectic_derived hf iso)
    | g2_derived hf iso => exact .inl (.g2_derived hf iso)
    | tits hf iso => exact .inl (.tits hf iso)
  · rintro (h | ⟨m, hm, hf, iso⟩)
    · exact h.toRankTwoModel
    · exact .ree_f4 m hm hf iso

theorem IsRankTwoModel.of_mulEquiv (h : IsRankTwoModel G f) (e : H ≃* G) :
    IsRankTwoModel H f := by
  cases h with
  | linear hf iso => exact .linear hf (iso.of_mulEquiv e)
  | unitary_four hf iso => exact .unitary_four hf (iso.of_mulEquiv e)
  | unitary_five hf iso => exact .unitary_five hf (iso.of_mulEquiv e)
  | symplectic hf iso => exact .symplectic hf (iso.of_mulEquiv e)
  | g2 hf iso => exact .g2 hf (iso.of_mulEquiv e)
  | triality hf iso => exact .triality hf (iso.of_mulEquiv e)
  | ree_f4 m hm hf iso => exact .ree_f4 m hm hf (iso.map fun a => e.trans a)
  | symplectic_derived hf iso => exact .symplectic_derived hf (iso.map fun a => e.trans a)
  | g2_derived hf iso => exact .g2_derived hf (iso.map fun a => e.trans a)
  | tits hf iso => exact .tits hf (iso.map fun a => e.trans a)

theorem isRankTwoModel_mulEquiv_iff (e : G ≃* H) :
    IsRankTwoModel G f ↔ IsRankTwoModel H f :=
  ⟨fun h => h.of_mulEquiv e.symm, fun h => h.of_mulEquiv e⟩

end CFSG.Quasithin.ClassificationModels
