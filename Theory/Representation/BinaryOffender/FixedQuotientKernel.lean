module

public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.PGroupCore

/-!
# Kernel on the quotient by fixed vectors

The literal X-action on V/C_V(X) has a two-group kernel when V is binary
and the original representation is faithful. A kernel element x has all
its displacements in C_V(X), so (ρ(x)-1)² = 0 and ρ(x)² = 1. Faithfulness
then makes every element of the kernel have order dividing two. Its normality
as an actual representation kernel places it in O₂(X).

The normalizer acts on the same literal quotient. If an element stabilizes
one of two spanning Irr⁺ members and fixes their diagonal, the disjoint
quotient images and `fixes_sup_of_fixes_diagonal` make that element trivial
on the quotient. Its commutators with X then also act trivially there.

This is the quotient-kernel step of Aschbacher–Smith, *The Classification of
Quasithin Groups*, B.7.2, printed p.119 (PDF p.130).
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The subrepresentation consisting of X-fixed vectors. -/
noncomputable def restrictedFixedSubrepresentation (X : Subgroup G) : Subrepresentation (ρ.comp X.subtype) where
  toSubmodule := fixedSpace ρ X
  apply_mem_toSubmodule x v hv := by
    change ∀ y : X, ρ y (ρ x v) = ρ x v
    rw [show ρ x v = v from hv x]
    exact hv

/-- The actual X-action on V/C_V(X). -/
noncomputable def fixedQuotientRepresentation (X : Subgroup G) :
    Representation (ZMod 2) X (V ⧸ fixedSpace ρ X) :=
  (restrictedFixedSubrepresentation ρ X).quotientRepresentation

/-- Kernel membership is displacement into the fixed space. -/
theorem mem_fixedQuotient_ker_iff (X : Subgroup G) (x : X) :
    x ∈ (fixedQuotientRepresentation ρ X).ker ↔
      ∀ v : V, ρ x v - v ∈ fixedSpace ρ X := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v
    have hh := LinearMap.congr_fun h ((fixedSpace ρ X).mkQ v)
    change (fixedSpace ρ X).mkQ (ρ x v) = (fixedSpace ρ X).mkQ v at hh
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ X).mkQ (ρ x v - v) = 0
    rw [map_sub, hh, sub_self]
  · intro h
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (fixedSpace ρ X).mkQ_surjective q
    change (fixedSpace ρ X).mkQ (ρ x v) = (fixedSpace ρ X).mkQ v
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h v)

/-- Faithfulness puts the kernel on V/C_V(X) in O₂(X). -/
theorem fixedQuotient_ker_le_pCore (hf : Function.Injective ρ) (X : Subgroup G) :
    (fixedQuotientRepresentation ρ X).ker ≤ pCore 2 X := by
  have hp : IsPGroup 2 (fixedQuotientRepresentation ρ X).ker := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply hf
    change ρ ((x.val.val) ^ (2 ^ 1)) = ρ (1 : G)
    ext v
    have hd := (mem_fixedQuotient_ker_iff ρ X x.val).mp x.property v x.val
    change ρ (x : X) (ρ (x : X) v - v) = ρ (x : X) v - v at hd
    rw [map_sub] at hd
    have htwo (w : V) : w + w = 0 := by
      calc
        w + w = ((1 : ZMod 2) + 1) • w := by rw [add_smul, one_smul]
        _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
    have hv : ρ (x : X) (ρ (x : X) v) = v := by
      apply add_right_cancel (b := v)
      exact (sub_eq_sub_iff_add_eq_add.mp hd).trans ((htwo _).trans (htwo v).symm)
    simpa only [pow_one, pow_two, map_mul, Module.End.mul_apply,
      map_one, Module.End.one_apply] using hv
  exact le_sSup ⟨inferInstance, hp⟩
/-- Normalizers preserve fixed vectors. -/
theorem normalizer_le_stabilizer_fixedSpace (X : Subgroup G) :
    (normalizer (X : Set G)) ≤ subspaceStabilizer ρ (fixedSpace ρ X) := by
  apply le_subspaceStabilizer
  intro g hg v hv x
  have hconj : g⁻¹ * (x : G) * g ∈ X := by
    simpa using (mem_normalizer_iff.mp ((normalizer (X : Set G)).inv_mem hg) (x : G)).mp x.property
  have he := congrArg (ρ g) (hv ⟨g⁻¹ * (x : G) * g, hconj⟩)
  change ρ g (ρ (g⁻¹ * (x : G) * g) v) = ρ g v at he
  change ρ x (ρ g v) = ρ g v
  simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using he

/-- A stabilizer fixing the diagonal acts trivially modulo the fixed space. -/
theorem displacement_fixed_of_stabilizes_irrPlus
    {X : Subgroup G} {I : Submodule (ZMod 2) V} {a b : G}
    (hI : IsIrrPlus ρ X I) (hIa : IsIrrPlus ρ X (I.map (ρ a)))
    (hne : I ≠ I.map (ρ a)) (hsup : I ⊔ I.map (ρ a) = ⊤)
    (haN : a ∈ (normalizer (X : Set G))) (hbN : b ∈ (normalizer (X : Set G)))
    (hab : Commute a b) (hb : b ∈ subspaceStabilizer ρ I)
    (hd : ∀ v, ρ b (ρ a v - v) = ρ a v - v) :
    ∀ v : V, ρ b v - v ∈ fixedSpace ρ X := by
  let C : Subrepresentation (ρ.comp (normalizer (X : Set G)).subtype) :=
    invariantSubspace ρ (normalizer (X : Set G)) (fixedSpace ρ X)
      (normalizer_le_stabilizer_fixedSpace ρ X)
  let σ : Representation (ZMod 2) (normalizer (X : Set G)) (V ⧸ fixedSpace ρ X) :=
    C.quotientRepresentation
  let a' : (normalizer (X : Set G)) := ⟨a, haN⟩
  let b' : (normalizer (X : Set G)) := ⟨b, hbN⟩
  let q := (fixedSpace ρ X).mkQ
  have hq (g : (normalizer (X : Set G))) (v : V) : σ g (q v) = q (ρ (g : G) v) := rfl
  have hmap : (I.map q).map (σ a') = (I.map (ρ a)).map q := by
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    congr 1
  have hdis : Disjoint (I.map q) ((I.map q).map (σ a')) := by
    rw [hmap]
    exact IsIrrPlus.disjoint_quotientImages ρ hI hIa hne
  have hbi : ∀ v ∈ I.map q, σ b' v ∈ I.map q := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ b v, (hb v).mpr hv, (hq b' v).symm⟩
  have hbj : ∀ v ∈ (I.map q).map (σ a'), σ b' v ∈ (I.map q).map (σ a') := by
    rw [hmap]
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨ρ a (ρ b v), ⟨ρ b v, (hb v).mpr hv, rfl⟩, ?_⟩
    rw [hq]
    congr 1
    change (ρ a * ρ b) v = (ρ b * ρ a) v
    rw [← map_mul, ← map_mul, hab.eq]
  have hdiag : ∀ v ∈ I.map q, σ b' (σ a' v - v) = σ a' v - v := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hq, ← map_sub, hq, hd]
  have hfix := fixes_sup_of_fixes_diagonal σ (I.map q) a' b' hdis hbi hbj hdiag
  intro v
  apply (Submodule.Quotient.mk_eq_zero _).mp
  change q (ρ b v - v) = 0
  rw [map_sub, ← hq b']
  apply sub_eq_zero.mpr
  apply hfix
  rw [hmap, ← Submodule.map_sup, hsup]
  exact ⟨v, Submodule.mem_top, rfl⟩
/-- The displacement of [x,b] remains fixed when b is trivial modulo C_V(X). -/
theorem commutator_displacement_fixed {X : Subgroup G} {b : G}
    (hd : ∀ v : V, ρ b v - v ∈ fixedSpace ρ X)
    (x : X) (v : V) : ρ ⁅(x : G), b⁆ v - v ∈ fixedSpace ρ X := by
  have hbiv : ρ b (ρ b⁻¹ v) = v := by
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hbinv : ρ b⁻¹ v - v ∈ fixedSpace ρ X := by
    have hh := (fixedSpace ρ X).neg_mem (hd (ρ b⁻¹ v))
    rwa [hbiv, neg_sub] at hh
  let w := ρ (x : G)⁻¹ (ρ b⁻¹ v)
  have hxw : ρ x w = ρ b⁻¹ v := by
    dsimp [w]
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hfix : ρ x (ρ b w - w) = ρ b w - w := hd w x
  have he : ρ x (ρ b w) = (ρ b w - w) + ρ b⁻¹ v := by
    rw [map_sub, hxw] at hfix
    exact sub_eq_iff_eq_add.mp hfix
  change ρ ((x : G) * b * (x : G)⁻¹ * b⁻¹) v - v ∈ fixedSpace ρ X
  simp only [map_mul, Module.End.mul_apply]
  change ρ x (ρ b w) - v ∈ fixedSpace ρ X
  rw [he, add_sub_assoc]
  exact (fixedSpace ρ X).add_mem (hd w) hbinv

end Representation.BinaryOffender
