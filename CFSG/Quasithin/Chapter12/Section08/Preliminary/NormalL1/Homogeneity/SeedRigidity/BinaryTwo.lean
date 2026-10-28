module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Coordinates
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.BinaryTwo
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Rank-three natural seed rigidity

For n=3 the marking identifies the literal quotient L₁/O₂(L₁) with
GL₂(2)′. Its natural binary plane is simple because this derived actor
is transitive on nonzero vectors. Every automorphism of the derived
actor is implemented on that plane, including inversion by the coordinate
swap. Conjugation by an element normalizing L₁ descends through its
characteristic two-core; transporting through the marking and back through
the seed coordinates gives the required left-conjugation intertwiner.

These two theorems discharge exactly the simple-seed and conjugation-twist
premises of `homogeneous_coordinates_of_seed_intertwiners` in rank three.
The natural marking is the supplied earlier-source input. The actor remains
the derived subgroup throughout, and no action on the whole span is assumed.
The higher-rank cases and final source assembly belong to `SeedRigidity`;
this module imports `Coordinates` directly to preserve that dependency order.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.5(1), printed p.850 (PDF p.867).
-/

public section

open Subgroup
open scoped IsMulCommutative MonoidAlgebra
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}
variable {F : InvariantFlag T V 3} {L : Subgroup G}
variable {hLV : L ≤ normalizer (V : Set G)} [IsElementaryAbelian 2 (F.tilde V)]

namespace NaturalSeedMarking
variable (D : F.NaturalSeedMarking L hLV)
include D

/-- At rank three the actual marked C₃ actor acts simply on the binary seed. -/
theorem seed_simple_rank_three :
    IsSimpleModule (ZMod 2)[F.Li L 1] (F.localSeedRepresentation L hLV).asModule := by
  let σ := F.localSeedRepresentation L hLV
  let e := σ.asModuleEquiv.trans D.coordinates
  let : Nontrivial σ.asModule := e.toEquiv.nontrivial
  rw [isSimpleModule_iff, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  apply top_unique
  intro w _
  by_cases hw : w = 0
  · simpa only [hw] using S.zero_mem
  have hev : e v ≠ 0 := fun h => hv0 (e.injective (h.trans e.map_zero.symm))
  have hew : e w ≠ 0 := fun h => hw (e.injective (h.trans e.map_zero.symm))
  obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_transitive_nonzero hev hew
  obtain ⟨q, hq⟩ := D.quotientEquiv.surjective g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective _ q
  have hk : (MonoidAlgebra.of (ZMod 2) (F.Li L 1) k) • v = w := by
    apply e.injective
    change D.coordinates (σ.asModuleEquiv (_ • v)) = _
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
    rw [D.equivariant, hq]
    exact hg
  exact hk ▸ S.smul_mem _ hv

/-- Characteristic-quotient transport and the binary C₃ calculation give
intertwiners for literal left conjugation by every element normalizing L₁. -/
theorem seed_intertwiners_rank_three (J : Subgroup G)
    (hJK : J ≤ normalizer (F.Li L 1 : Set G)) :
    ∀ j : J, ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Additive (F.tilde V),
      ∀ k v, c (F.localSeedRepresentation L hLV k v) =
        F.localSeedRepresentation L hLV (F.localConjugation L J hJK j k) (c v) := by
  intro j
  let a : MulAut (commutator (BinaryLinear.OuterCyclic.LinearGroup 2)) :=
    MulAut.congr D.quotientEquiv
      (quotientAut (pCore 2 (F.Li L 1)) (F.localConjugation L J hJK j))
  have ha (k : F.Li L 1) :
      a (D.quotientEquiv (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k)) =
        D.quotientEquiv (QuotientGroup.mk' (pCore 2 (F.Li L 1))
          (F.localConjugation L J hJK j k)) := by
    change D.quotientEquiv (quotientAut (pCore 2 (F.Li L 1))
      (F.localConjugation L J hJK j)
      (D.quotientEquiv.symm (D.quotientEquiv
        (QuotientGroup.mk' (pCore 2 (F.Li L 1)) k)))) = _
    rw [MulEquiv.symm_apply_apply, quotientAut_apply_mk]
  obtain ⟨c, hc⟩ := BinaryLinear.OuterCyclic.BinaryTwo.derived_automorphism_intertwiner a
  refine ⟨D.coordinates.trans (c.trans D.coordinates.symm), ?_⟩
  intro k v
  apply D.coordinates.injective
  change D.coordinates (D.coordinates.symm (c (D.coordinates
    (F.localSeedRepresentation L hLV k v)))) = _
  rw [D.coordinates.apply_symm_apply, D.equivariant, hc, ha, D.equivariant]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

end NaturalSeedMarking
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
