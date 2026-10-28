module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.SectionLinear
/-!
# Exactness of fixed spaces for a cubic element in characteristic two

For an element with cube one, the averaging operator is `1 + g + g²`.
It lifts every fixed quotient vector to a fixed vector. Rank-nullity therefore
adds the fixed dimensions in an invariant subspace and its quotient.
This supplies the numerical compatibility check in H.15.4 without any
transvection-factor hypothesis.

Source: Aschbacher--Smith, H.15.4, printed p.400; the proof is the elementary
coprime averaging argument specialized to characteristic two.
-/

public section

open Representation.BinaryOffender
namespace BinaryPermutation.PointedSix
noncomputable section
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

lemma cubic_fixed_finrank_add (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) (g : G) (hg : g ^ 3 = 1) :
    Module.finrank (ZMod 2) (fixedSpace W.toRepresentation (Subgroup.zpowers g)) +
      Module.finrank (ZMod 2) (fixedSpace W.quotientRepresentation (Subgroup.zpowers g)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers g)) := by
  let A := Subgroup.zpowers g
  let f : fixedSpace ρ A →ₗ[ZMod 2] fixedSpace W.quotientRepresentation A :=
    (W.toSubmodule.mkQ.domRestrict (fixedSpace ρ A)).codRestrict _ (by
      intro v a
      exact congrArg W.toSubmodule.mkQ (v.property a))
  have hs : Function.Surjective f := by
    intro v
    obtain ⟨a,ha⟩ := W.toSubmodule.mkQ_surjective v.val
    have hp : ρ g (ρ g (ρ g a)) = a := by
      simpa only [pow_succ, pow_zero, one_mul, map_mul, Module.End.mul_apply,
        map_one, Module.End.one_apply] using
        (LinearMap.congr_fun (congrArg ρ hg) a)
    have hq1 : W.toSubmodule.mkQ (ρ g a) = v.val := by
      change W.quotientRepresentation g (W.toSubmodule.mkQ a) = _
      rw [ha]
      exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property
    have hq2 : W.toSubmodule.mkQ (ρ g (ρ g a)) = v.val := by
      change W.quotientRepresentation g (W.toSubmodule.mkQ (ρ g a)) = _
      rw [hq1]
      exact (mem_fixedSpace_zpowers_iff _ _ _).mp v.property
    refine ⟨⟨a + ρ g a + ρ g (ρ g a), ?_⟩, ?_⟩
    · apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      rw [map_add, map_add, hp]
      abel
    · apply Subtype.ext
      change W.toSubmodule.mkQ (a + ρ g a + ρ g (ρ g a)) = v.val
      rw [map_add, map_add, ha, hq1, hq2, ← two_smul (ZMod 2),
        show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  let e : f.ker ≃ₗ[ZMod 2] fixedSpace W.toRepresentation A :=
    { toFun := fun v => ⟨⟨v.val.val, (Submodule.Quotient.mk_eq_zero _).mp
          (congrArg Subtype.val v.property)⟩,
        fun a => Subtype.ext (v.val.property a)⟩
      invFun := fun v => ⟨⟨v.val.val, fun a => congrArg Subtype.val (v.property a)⟩,
        Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr v.val.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top, e.finrank_eq] at h
  exact (Nat.add_comm _ _).trans h
end
end BinaryPermutation.PointedSix
