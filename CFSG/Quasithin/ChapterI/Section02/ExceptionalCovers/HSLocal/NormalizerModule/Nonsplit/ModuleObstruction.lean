module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# From a Frattini-module complement to a split central kernel

An invariant complement to the fixed space contains every displacement.
Its inverse image therefore contains [Q,M]. Central core elements map to
fixed vectors, and disjointness of the central kernel from Φ(Q) shows
that a complement would force [Q,M] to miss that kernel.

The literal central line is the binary span of the image of ker(localMap).
It is nonzero and fixed, and equals the invariant space when that space has
dimension one. These statements retain the given maps and actual Qbar.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423.
-/

@[expose] public section

open scoped IsMulCommutative
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
variable {K : Type*} [Group K] [Finite K]

private theorem displacement_mem_complement
    {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) D V) (W : Subrepresentation σ)
    (hW : IsCompl σ.invariants W.toSubmodule) (g : D) (v : V) :
    σ g v - v ∈ W.toSubmodule := by
  have hv : v ∈ σ.invariants ⊔ W.toSubmodule := by rw [hW.sup_eq_top]; trivial
  obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hc g, add_sub_add_left_eq_sub]
  exact W.toSubmodule.sub_mem (W.apply_mem_toSubmodule g hw) hw

/-- The inverse image of an invariant binary subspace in the literal core. -/
private def subspacePreimage
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (W : Subrepresentation (frattiniRepresentation e)) : Subgroup (M e) :=
  (((W.toSubmodule.toAddSubgroup.toSubgroup').comap (coreMap e)).map (Q e).subtype)

private theorem commutator_le_subspacePreimage
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (W : Subrepresentation (frattiniRepresentation e))
    (hW : IsCompl (frattiniRepresentation e).invariants W.toSubmodule) :
    ⁅Q e, ⊤⁆ ≤ subspacePreimage e W := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro m _ q hq
  let a : Q e := ⟨q, hq⟩
  refine ⟨MulAut.conjNormal m a * a⁻¹, ?_, rfl⟩
  change Additive.ofMul (coreMap e (MulAut.conjNormal m a * a⁻¹)) ∈ W.toSubmodule
  rw [map_mul, map_inv, ofMul_mul, ofMul_inv, ← sub_eq_add_neg]
  change Additive.ofMul (coreMap e (MulAut.conjNormal m a)) -
    Additive.ofMul (coreMap e a) ∈ W.toSubmodule
  rw [← frattiniRepresentation_coreMap]
  exact displacement_mem_complement _ W hW _ _

private theorem central_coreMap_fixed
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (q : Q e) (hq : (q : M e) ∈ (localMap e).ker) :
    Additive.ofMul (coreMap e q) ∈ (frattiniRepresentation e).invariants := by
  intro g
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q e) g
  rw [frattiniRepresentation_coreMap]
  congr 2
  apply Subtype.ext
  have hc : m * (q : M e) = q * m := by
    apply Subtype.ext
    exact mem_center_iff.mp (show (q : K) ∈ center K by
      rwa [localMap_ker] at hq) (m : K)
  change m * (q : M e) * m⁻¹ = q
  rw [hc, mul_inv_cancel_right]

/-- A complement to the fixed space forces the central kernel to meet [Q,M]
trivially, provided the central kernel survives the Frattini quotient. -/
theorem disjoint_commutator_kernel_of_complement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZE : Disjoint (localMap e).ker (E e))
    (W : Subrepresentation (frattiniRepresentation e))
    (hW : IsCompl (frattiniRepresentation e).invariants W.toSubmodule) :
    Disjoint ⁅Q e, ⊤⁆ (localMap e).ker := by
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨q, hq, hqx⟩ := commutator_le_subspacePreimage e W hW hx.1
  have hqc : (q : M e) ∈ (localMap e).ker := by
    change (Q e).subtype q ∈ (localMap e).ker
    rw [hqx]
    exact hx.2
  have hzero : Additive.ofMul (coreMap e q) = 0 :=
    hW.disjoint.le_bot ⟨central_coreMap_fixed e q hqc, hq⟩
  have he : (q : M e) ∈ E e := by
    apply (QuotientGroup.eq_one_iff (q : M e)).mp
    exact congrArg (fun v : Additive (Qbar e) => (v.toMul : M e ⧸ E e)) hzero
  have hone : (q : M e) = 1 := hZE.le_bot ⟨hqc, he⟩
  change x = 1
  exact hqx.symm.trans hone

/-- The literal image of the cover's central kernel in the binary Frattini
section. Taking its binary span avoids introducing a second quotient action. -/
def centralLine
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    Submodule (ZMod 2) (Additive (Qbar e)) :=
  Submodule.span (ZMod 2) {v | ∃ q : Q e, (q : M e) ∈ (localMap e).ker ∧
    v = Additive.ofMul (coreMap e q)}

theorem centralLine_le_invariants
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) :
    centralLine e ≤ (frattiniRepresentation e).invariants := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, hq, rfl⟩
  exact central_coreMap_fixed e q hq

/-- The central image is nonzero because the kernel of order two is
disjoint from Φ(Q). -/
theorem centralLine_ne_bot
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hZE : Disjoint (localMap e).ker (E e)) : centralLine e ≠ ⊥ := by
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (localMap e).ker) 2
    (by rw [localMap_ker_card, hZ])
  have hzQ : (z : M e) ∈ Q e := center_le_Q e hZ
    (show (z : M e) ∈ (center K).subgroupOf (M e) by
      rw [← localMap_ker]; exact z.property)
  let q : Q e := ⟨z, hzQ⟩
  have hv : Additive.ofMul (coreMap e q) ∈ centralLine e :=
    Submodule.subset_span ⟨q, z.property, rfl⟩
  intro h
  rw [h] at hv
  have he : (z : M e) ∈ E e := by
    apply (QuotientGroup.eq_one_iff (z : M e)).mp
    exact congrArg (fun v : Additive (Qbar e) => (v.toMul : M e ⧸ E e)) hv
  have hz1 : z = 1 := Subtype.ext (hZE.le_bot ⟨z.property, he⟩)
  simp [hz1] at hz

/-- In dimension one the fixed space is exactly the specified central image. -/
theorem centralLine_eq_invariants
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hZE : Disjoint (localMap e).ker (E e))
    (hline : Module.finrank (ZMod 2) (frattiniRepresentation e).invariants = 1) :
    centralLine e = (frattiniRepresentation e).invariants :=
  ((Submodule.isAtom_iff_finrank_eq_one.mpr hline).le_iff.mp
    (centralLine_le_invariants e)).resolve_left (centralLine_ne_bot e hZ hZE)
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
