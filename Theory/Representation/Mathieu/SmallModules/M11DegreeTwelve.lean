module

public import Theory.Representation.Mathieu.SmallModules.M11DegreeTwelve.FixedVectors
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.Completeness
public import Theory.Representation.SimpleHeadQuotient
public import Mathlib.RepresentationTheory.Induced

/-!
# Reducing binary M11 recognition to one fixed induced module

The reference module already classifies degree ten. A hypothetical faithful
irreducible module of degree eleven or twelve has a nonzero vector fixed by
the actual Sylow-eleven normalizer. Frobenius reciprocity therefore realizes
it as a simple quotient of the induction of that normalizer's trivial module.
The representation, inclusion and quotient kernel below are all literal.

`SmallInducedHeads` states the outstanding finite-module calculation. No
character table or classification assertion is assumed to have been proved.
Source: James, J. Algebra 27 (1973), 57--111; the application is the M11
exclusion in Aschbacher--Smith K.4, printed p.457/PDF p.468.
-/

@[expose] public noncomputable section
open scoped MonoidAlgebra TensorProduct
namespace Representation.MathieuSmall.M11DegreeTwelve
open Sporadic.Mathieu M12Recognition

/-- The trivial binary module for the actual subgroup of order fifty-five. -/
def normalizerTrivial : Representation (ZMod 2) m11Sylow11Normalizer (ZMod 2) :=
  Representation.trivial _ _ _

/-- The fixed induction has 144 cosets; both the subgroup and its index
refer to the native M11 carrier. -/
theorem normalizer_index : m11Sylow11Normalizer.index = 144 := by
  have h := m11Sylow11Normalizer.card_mul_index
  rw [m11Sylow11_normalizer_card, m11_order] at h
  omega

/-- The literal induction along the existing normalizer inclusion in M11. -/
abbrev InducedSpace := IndV m11Sylow11Normalizer.subtype normalizerTrivial

def inducedRepresentation : Representation (ZMod 2) M11 InducedSpace :=
  ind m11Sylow11Normalizer.subtype normalizerTrivial

instance inducedFiniteDimensional : FiniteDimensional (ZMod 2) InducedSpace := by
  dsimp [InducedSpace, IndV]
  infer_instance

/-- The one remaining finite-module degree gap, stated on actual maximal
quotients rather than on arbitrary representations. -/
def SmallInducedHeads : Prop :=
  ∀ N : Subrepresentation inducedRepresentation, IsCoatom N →
    Module.finrank (ZMod 2) (InducedSpace ⧸ N.toSubmodule) ≤ 10 ∨
      12 < Module.finrank (ZMod 2) (InducedSpace ⧸ N.toSubmodule)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) M11 V)

private def fixedLine (v : V)
    (hv : v ∈ Representation.invariants (σ.comp m11Sylow11Normalizer.subtype)) :
    IntertwiningMap normalizerTrivial (σ.comp m11Sylow11Normalizer.subtype) where
  toLinearMap := (LinearMap.id : ZMod 2 →ₗ[ZMod 2] ZMod 2).smulRight v
  isIntertwining' g := by
    apply LinearMap.ext
    intro c
    change c • v = σ g.val (c • v)
    have hg : σ g.val v = v := hv g
    rw [map_smul, hg]

private def inducedMap
    (f : IntertwiningMap normalizerTrivial (σ.comp m11Sylow11Normalizer.subtype)) :
    IntertwiningMap inducedRepresentation σ where
  toLinearMap := Coinvariants.lift _
    (TensorProduct.lift <| (Finsupp.lift _ _ _ fun g =>
      σ g⁻¹ ∘ₗ f.toLinearMap) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap)
    (fun g => by
      ext h
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidAlgebra.lsingle_apply]
      simp [Representation.ofMulAction_single, mul_inv_rev]
      rw [IntertwiningMap.isIntertwining _ _ f]
      simp)
  isIntertwining' g := by ext; simp [inducedRepresentation]

private theorem inducedMap_mk_one
    (f : IntertwiningMap normalizerTrivial (σ.comp m11Sylow11Normalizer.subtype))
    (c : ZMod 2) :
    inducedMap σ f (IndV.mk m11Sylow11Normalizer.subtype normalizerTrivial 1 c) = f c := by
  simp [inducedMap]

/-- An exceptional small irreducible module is an actual quotient of the
fixed normalizer induction. No module-equivalence premise is used. -/
theorem exists_surjective_induced [FiniteDimensional (ZMod 2) V] [σ.IsIrreducible]
    (hf : Function.Injective σ)
    (hd : Module.finrank (ZMod 2) V = 11 ∨ Module.finrank (ZMod 2) V = 12) :
    ∃ f : IntertwiningMap inducedRepresentation σ, Function.Surjective f := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (normalizer_invariants_ne_bot σ hf hd)
  let f := inducedMap σ (fixedLine σ v hv)
  have hf0 : f ≠ 0 := by
    intro hz
    have he := congrArg (fun T : IntertwiningMap inducedRepresentation σ =>
      T (IndV.mk m11Sylow11Normalizer.subtype normalizerTrivial 1 1)) hz
    change inducedMap σ (fixedLine σ v hv) _ = 0 at he
    rw [inducedMap_mk_one] at he
    exact hv0 (by simpa [fixedLine] using he)
  exact ⟨f, (IsIrreducible.surjective_or_eq_zero f).resolve_right hf0⟩

/-- The finite induced-module gap supplies exactly the two missing dimensions
in the faithful degree-at-most-twelve recognition statement. -/
theorem equiv_point_of_smallInducedHeads [FiniteDimensional (ZMod 2) V]
    (hheads : SmallInducedHeads) (hf : Function.Injective σ) [σ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 12) :
    Nonempty (σ.Equiv pointRepresentation) := by
  have hlo := BinaryPrimeDegree.orderOf_le_finrank σ hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m11_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  apply PointClassification.equiv_point_of_faithful_degree_ten σ hf
  by_contra hne
  have hdim : Module.finrank (ZMod 2) V = 11 ∨ Module.finrank (ZMod 2) V = 12 := by omega
  obtain ⟨f, hsurj⟩ := exists_surjective_induced σ hf hdim
  have h := hheads f.ker (SimpleHeadQuotient.isCoatom_ker_of_surjective f hsurj)
  have he := (f.toLinearMap.quotKerEquivOfSurjective hsurj).finrank_eq
  change Module.finrank (ZMod 2) (InducedSpace ⧸ f.ker.toSubmodule) =
    Module.finrank (ZMod 2) V at he
  rw [he] at h
  omega

end Representation.MathieuSmall.M11DegreeTwelve
