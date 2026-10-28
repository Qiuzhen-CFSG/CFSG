module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.MarkedPlane.Transport
public import Theory.Representation.HexacodeAction.Field
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry


/-!
# Definite-plane stability from the external scalar action

The actual two-residual `Y_E` is two-perfect and lies in `M`, so its
orthogonal action cannot interchange the two definite planes. Moreover
`V = [V,Y_E]` and `|V| = 16` force this action to be nontrivial.
Consequently, once its action on the full normal closure is identified
with cubic scalars, some nonidentity power of `hexZ` preserves each
marked plane. Either nonidentity power generates the same cubic group,
so `hexZ` itself preserves the actual plane.

Scalar identification remains an explicit premise of the final lemma.
It is to be discharged by `Scalar`, rather than assumed in the source
configuration. No orbit condition or replacement of the plane is used.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the
definite-plane decomposition on printed pp.1121–1122, 15.3.66(5) on
p.1152, and the terminal module argument on p.1155.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
variable {G : Type*} [Group G] {G₀ M V : Subgroup G}
  {d : NaturalOrthogonalAction M V}

namespace SourceConfiguration
variable (cfg : SourceConfiguration G₀ M V d)

/-- The source commutator equality forces nontrivial action on `V`. -/
theorem first_residual_not_centralizes : ¬ cfg.YE ≤ centralizer (V : Set G) := by
  intro h
  have hbot : V = ⊥ := cfg.first_commutator.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp h))
  have hc := d.card_vector
  rw [hbot] at hc
  norm_num at hc

/-- A two-residual cannot permute the two definite summands. -/
theorem first_residual_normalizes_planes [Finite G] (i : OrthogonalPlaneIndex) :
    cfg.YE ≤ normalizer (d.plane i : Set G) := by
  apply RankTwo.perfect_normalizes_planes d (cfg.first_residual_le.trans cfg.residual_le)
  rw [cfg.first_residual_eq]
  exact isPPerfect_embedded_pResidual 2 _
end SourceConfiguration

variable [IsElementaryAbelian 2 (moduleClosure (V.subgroupOf G₀))]
  {hC : IsPGroup 2 (centralizer (V.subgroupOf G₀ : Set G₀))}
  {hcore : pCore 2 G₀ ≤ centralizer (V.subgroupOf G₀ : Set G₀)}
  (c : HexacodeCoordinates (V.subgroupOf G₀) hC hcore)

/-- Every vector of the source `V` has coordinates in its normal closure. -/
theorem exists_ambientVector (hV : V ≤ G₀) {v : G} (hv : v ∈ V) :
    ∃ w : Atlas.Codes.hexacode, ambientVector c w = v := by
  let u : moduleClosure (V.subgroupOf G₀) := ⟨⟨v, hV hv⟩, le_normalClosure hv⟩
  refine ⟨c.vectors (Additive.ofMul u), ?_⟩
  simp only [ambientVector, c.vectors.symm_apply_apply]
  rfl

/-- Scalar identification must realize a nonidentity cubic scalar. -/
theorem scalarAction_nontrivial (cfg : SourceConfiguration G₀ M V d)
    (hs : ScalarActionOn c cfg.YE) :
    ∃ y ∈ cfg.YE, ∃ k : Fin 3, k ≠ 0 ∧ ∀ w : Atlas.Codes.hexacode,
      y * ambientVector c w * y⁻¹ =
        ambientVector c (Representation.Hexacode.action (Atlas.Codes.hexZ ^ k.val) w) := by
  classical
  by_contra hn
  apply cfg.first_residual_not_centralizes
  intro y hy v hv
  obtain ⟨k, hk⟩ := hs y hy
  have hk0 : k = 0 := by
    by_contra hk0
    exact hn ⟨y, hy, k, hk0, hk⟩
  obtain ⟨w, rfl⟩ := exists_ambientVector c cfg.vector_le hv
  have he := hk w
  rw [hk0] at he
  simp only [Fin.val_zero, pow_zero, map_one, Module.End.one_apply] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- An external normalizer acting by a scalar power stabilizes the marked image. -/
theorem scalarPower_mem_stabilizer (P : Subgroup G) {y : G}
    (hy : y ∈ normalizer (P : Set G)) (k : Fin 3)
    (hk : ∀ w : Atlas.Codes.hexacode,
      y * ambientVector c w * y⁻¹ =
        ambientVector c (Representation.Hexacode.action (Atlas.Codes.hexZ ^ k.val) w)) :
    Atlas.Codes.hexZ ^ k.val ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action (vectorImage c P) := by
  intro w
  rw [mem_vectorImage, ← hk, mem_vectorImage]
  exact ((mem_normalizer_iff.mp hy) (ambientVector c w)).symm

private theorem scalar_mem_of_nonzero_power (P : Submodule (ZMod 2) Atlas.Codes.hexacode)
    (k : Fin 3) (hk : k ≠ 0)
    (hP : Atlas.Codes.hexZ ^ k.val ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action P) :
    Atlas.Codes.hexZ ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action P := by
  have hkval : k.val = 1 ∨ k.val = 2 := by
    have hne : k.val ≠ 0 := by simpa using hk
    omega
  rcases hkval with he | he
  · simpa only [he, pow_one] using hP
  · rw [he] at hP
    have h := (Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action P).pow_mem hP 2
    have hz3 : Atlas.Codes.hexZ ^ 3 = 1 := by
      rw [← Atlas.Codes.hexZ_order]
      exact pow_orderOf_eq_one _
    have hz4 : (Atlas.Codes.hexZ ^ 2) ^ 2 = Atlas.Codes.hexZ := by
      rw [← pow_mul]
      change Atlas.Codes.hexZ ^ (3 + 1) = Atlas.Codes.hexZ
      rw [pow_succ, hz3, one_mul]
    rwa [hz4] at h

/-- The actual definite planes are scalar-stable once the external action is identified. -/
theorem plane_scalar_stable_of_scalarAction [Finite G]
    (cfg : SourceConfiguration G₀ M V d) (hs : ScalarActionOn c cfg.YE)
    (i : OrthogonalPlaneIndex) :
    Atlas.Codes.hexZ ∈ Representation.BinaryOffender.subspaceStabilizer
      Representation.Hexacode.action (vectorImage c (d.plane i)) := by
  obtain ⟨y, hy, k, hk, he⟩ := scalarAction_nontrivial c cfg hs
  exact scalar_mem_of_nonzero_power (vectorImage c (d.plane i)) k hk
    (scalarPower_mem_stabilizer c (d.plane i) (cfg.first_residual_normalizes_planes i hy) k he)

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.MarkedPlane
