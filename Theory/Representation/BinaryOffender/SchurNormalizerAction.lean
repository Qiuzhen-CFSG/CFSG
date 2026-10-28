module

public import Theory.Representation.BinaryOffender.SchurNormalizerDisplacement
public import Theory.Representation.EndFieldDegree
public import Theory.Representation.EndFieldFrobenius
public import Theory.Representation.CommonFixedSpaceTransport

/-!+# Literal Schur-linear normalizer operators and their fixed spaces

A normalizer element commuting with the component endomorphisms acts on the
original endomorphism-field module. Extend this operator, rather than replacing
the Schur field by the endomorphism field of an overgroup. Both single and
common fixed dimensions then descend with exactly the original Schur degree.

The construction follows the checked symplectic `OuterSchurDegree.Model` and
`FixedSpace.Transport` proofs; this general normalizer interface is used by
the SL₃ tensor calculation of K.3.2. Source: Guralnick–Malle, Classification
of 2F-modules II, §3.5 and Proposition 4.8, manuscript pp.26–28.
-/

@[expose] public section
noncomputable section
open scoped MonoidAlgebra TensorProduct
open LinearMap.FixedSpaceTransport

namespace Representation.BinaryOffender.SchurNormalizer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original normalizer operator over the original component Schur ring. -/
def schurActor (t : linearNormalizer ρ) (ht : IsSchurLinear ρ t) :
    Module.End (Module.End (ZMod 2)[G] ρ.asModule) ρ.asModule where
  toFun v := ρ.asModuleEquiv.symm (t.val.val (ρ.asModuleEquiv v))
  map_add' x y := by simp
  map_smul' c v :=
    congrArg ρ.asModuleEquiv.symm ((isSchurLinear_iff_endField ρ t).mp ht c v)

/-- The involution equation is preserved over the actual Schur ring. -/
theorem schurActor_square (t : linearNormalizer ρ) (ht : IsSchurLinear ρ t)
    (h2 : t ^ 2 = 1) : schurActor ρ t ht ^ 2 = 1 := by
  have hh := congrArg (fun x : linearNormalizer ρ => x.val.val) h2
  change t.val.val * t.val.val = 1 at hh
  ext v
  apply ρ.asModuleEquiv.injective
  exact LinearMap.congr_fun hh (ρ.asModuleEquiv v)

variable [FiniteDimensional (ZMod 2) V] [IsIrreducible ρ]
  (K : Type*) [Field K] [Algebra (Module.End (ZMod 2)[G] ρ.asModule) K]

/-- Scalar extension of the literal Schur-linear actor. -/
def absoluteActor (t : linearNormalizer ρ) (ht : IsSchurLinear ρ t) :
    Module.End K (K ⊗[Module.End (ZMod 2)[G] ρ.asModule] ρ.asModule) :=
  (schurActor ρ t ht).baseChange K

/-- Scalar extension retains the original square-one equation. -/
theorem absoluteActor_square (t : linearNormalizer ρ) (ht : IsSchurLinear ρ t)
    (h2 : t ^ 2 = 1) : absoluteActor ρ K t ht ^ 2 = 1 := by
  rw [absoluteActor, pow_two, ← LinearMap.baseChange_mul, ← pow_two,
    schurActor_square ρ t ht h2, LinearMap.baseChange_one]

/-- Exact descent of the common fixed dimension of two normalizer elements. -/
theorem binary_commonFixed_finrank (t u : linearNormalizer ρ)
    (ht : IsSchurLinear ρ t) (hu : IsSchurLinear ρ u) :
    Module.finrank (ZMod 2) ↥((t.val.val - 1).ker ⊓ (u.val.val - 1).ker) =
      Representation.schurDegree 2 ρ * Module.finrank K
        ↥((absoluteActor ρ K t ht - 1).ker ⊓ (absoluteActor ρ K u hu - 1).ker) := by
  let f := schurActor ρ t ht
  let g := schurActor ρ u hu
  let e := commonFixedEquiv ρ.asModuleEquiv
    (f.restrictScalars (ZMod 2)) (g.restrictScalars (ZMod 2)) t.val.val u.val.val
    (fun _ => rfl) (fun _ => rfl)
  have he := e.finrank_eq
  change Module.finrank (ZMod 2) ↥((f - 1).ker ⊓ (g - 1).ker) = _ at he
  rw [← he, ← Module.finrank_mul_finrank (ZMod 2)
    (Module.End (ZMod 2)[G] ρ.asModule) ↥((f - 1).ker ⊓ (g - 1).ker)]
  exact congrArg (Representation.schurDegree 2 ρ * ·)
    (finrank_commonFixed_baseChange (E := K) f g).symm

/-- Exact descent of a normalizer element's displacement dimension. -/
theorem binary_range_finrank (t : linearNormalizer ρ) (ht : IsSchurLinear ρ t) :
    Module.finrank (ZMod 2) (t.val.val - 1).range =
      Representation.schurDegree 2 ρ *
        Module.finrank K (absoluteActor ρ K t ht - 1).range := by
  have hk := binary_commonFixed_finrank ρ K t t ht ht
  rw [finrank_inf_self, finrank_inf_self] at hk
  have hb := (t.val.val - 1).finrank_range_add_finrank_ker
  have ha := (absoluteActor ρ K t ht - 1).finrank_range_add_finrank_ker
  have hd := Representation.finrank_eq_schurDegree_mul 2 ρ K
  have hh := congrArg (Representation.schurDegree 2 ρ * ·) ha
  rw [Nat.mul_add] at hh
  omega

end Representation.BinaryOffender.SchurNormalizer
