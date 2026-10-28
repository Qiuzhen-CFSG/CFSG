module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-!
# Transport of the literal point centralizer residual

The source distinguishes centralizing V₂ from centralizing its image modulo
V₁. Since H centralizes the elementary binary layer V₁, every homomorphism
from a two-perfect subgroup into that layer vanishes. Apply this to the
commutator with each vector: the two-residual of C_H(V₂/V₁) centralizes V₂.
Monotonicity and idempotence of finite residuals give equality with the
literal K₂ = O²(C_H(V₂)). The final image calculation uses the marked A₄
residual of the duad stabilizer, retaining the quotient-centralizer image
bounds as explicit premises for the marking construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.7.6(3), printed p.939, and proof of 13.8.6(1), printed p.948.
-/

public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G]

private theorem perfect_centralizes_of_central_layer (R V Z : Subgroup G)
    [IsMulCommutative Z] (hp : IsPPerfect 2 R) (hZ : IsPGroup 2 Z)
    (hRZ : R ≤ centralizer (Z : Set G)) (hc : ⁅R, V⁆ ≤ Z) :
    R ≤ centralizer (V : Set G) := by
  let : CommGroup Z := IsMulCommutative.instCommGroup
  intro r hr v hv
  let f : R →* Z := {
    toFun a := ⟨⁅a.val, v⁆, hc (commutator_mem_commutator a.property hv)⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' a b := by
      apply Subtype.ext
      change ⁅a.val * b.val, v⁆ = ⁅a.val, v⁆ * ⁅b.val, v⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hab := hRZ a.property ⁅b.val, v⁆
        (hc (commutator_mem_commutator b.property hv))
      rw [← hab, mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm
        (⟨⁅b.val, v⁆, hc (commutator_mem_commutator b.property hv)⟩ : Z)
        ⟨⁅a.val, v⁆, hc (commutator_mem_commutator a.property hv)⟩) }
  have hf := hp.hom_eq_one_of_isPGroup hZ f
  have he := congrArg (fun q : R →* Z => (q ⟨r, hr⟩).val) hf
  change ⁅r, v⁆ = 1 at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp he).symm

/-- The full centralizer and the quotient centralizer have the same two-residual. -/
theorem centralizer_residual_eq_preimage [Finite G] (H V Z : Subgroup G)
    [IsElementaryAbelian 2 Z] (hHZ : H ≤ centralizer (Z : Set G)) :
    Source.K2 H V = (pResidual 2 (commutatorPreimage H V Z)).map
      (commutatorPreimage H V Z).subtype := by
  let A := commutatorPreimage H V Z
  let R := (pResidual 2 A).map A.subtype
  have hAZ : A ≤ centralizer (Z : Set G) := (commutatorPreimage_le H V Z).trans hHZ
  have hRZ : R ≤ centralizer (Z : Set G) := (map_subtype_le _).trans hAZ
  have hc : ⁅R, V⁆ ≤ Z := (commutator_mono (map_subtype_le _) le_rfl).trans
    (commutator_commutatorPreimage_le H V Z
      (hHZ.trans (centralizer_le_normalizer _)))
  have hRC : R ≤ H ⊓ centralizer (V : Set G) :=
    le_inf ((map_subtype_le _).trans (commutatorPreimage_le H V Z))
      (perfect_centralizes_of_central_layer R V Z
        (isPPerfect_embedded_pResidual 2 A) (IsElementaryAbelian.isPGroup 2 Z) hRZ hc)
  apply le_antisymm
  · apply embedded_pResidual_mono
    apply le_commutatorPreimage inf_le_left
    rw [commutator_eq_bot_iff_le_centralizer.mpr inf_le_right]
    exact bot_le
  · have hp : (pResidual 2 R).map R.subtype = R := by
      rw [(pResidual_eq_top_iff 2 R).mpr (isPPerfect_embedded_pResidual 2 A),
        ← MonoidHom.range_eq_map, range_subtype]
    exact hp.symm.le.trans (embedded_pResidual_mono 2 hRC)

/-- Restriction to a containing subgroup preserves the literal embedded residual. -/
theorem residual_subgroupOf [Finite G] (X H : Subgroup G) (hXH : X ≤ H) :
    ((pResidual 2 X).map X.subtype).subgroupOf H =
      (pResidual 2 (X.subgroupOf H)).map (X.subgroupOf H).subtype := by
  apply map_injective H.subtype_injective
  rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans hXH),
    map_embedded_pResidual, map_subgroupOf_eq_of_le hXH]

/-- Compute the marked image from the quotient centralizer, not from an assumed
identification of the centralizer of V with that of V/Z. -/
theorem K2_image [Finite G] (H V Z : Subgroup G)
    [IsElementaryAbelian 2 Z] (hHZ : H ≤ centralizer (Z : Set G))
    (φ : H →* Equiv.Perm (Fin 6))
    (hlo : Theory.SpecificGroups.SymmetricSix.BinaryFlags.K ≤
      ((commutatorPreimage H V Z).subgroupOf H).map φ)
    (hhi : ((commutatorPreimage H V Z).subgroupOf H).map φ ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.H1) :
    ((Source.K2 H V).subgroupOf H).map φ =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.K := by
  rw [centralizer_residual_eq_preimage H V Z hHZ,
    residual_subgroupOf _ H (commutatorPreimage_le H V Z), map_embedded_pResidual]
  exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.residual_eq_K_of_between _ hlo hhi

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking
