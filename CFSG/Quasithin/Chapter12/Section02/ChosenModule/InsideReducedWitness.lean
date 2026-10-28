module
public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Homogeneous selection inside a specified reduced witness

A reduced normal subgroup of BT lies in the literal R₂(BT). If B moves
it, a minimal noncentral invariant subspace is an Irr⁺ member. Embedding
this member into R₂(BT) and applying A.1.42 keeps the homogeneous selection
inside the same normal witness. The conclusion retains the actual ambient
inclusion, which is needed when the witness lies in a specified commutator.

Source: Aschbacher–Smith A.1.40–42 and the chosen-module convention of
12.2.2, printed pp.31–32 and 794–795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {B : Subgroup G}

/-- A moved reduced witness contains a member of the original homogeneous family. -/
theorem exists_chosen_le_reduced_witness [Group.IsPerfect B]
    (hn : (T : Subgroup G) ≤ normalizer (B : Set G))
    (R : Subgroup (B ⊔ (T : Subgroup G) : Subgroup G)) (hR : IsPReduced 2 R)
    (hm : ⁅R, B.subgroupOf (B ⊔ (T : Subgroup G))⁆ ≠ ⊥) :
    ∃ U : Subgroup G, Nonempty (ChosenModule T B U) ∧
      U ≤ R.map (B ⊔ (T : Subgroup G) : Subgroup G).subtype := by
  let H := B ⊔ (T : Subgroup G)
  let A := B.subgroupOf H
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
  let e : A ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  let : R.Normal := hR.normal
  let ρ := reducedRepresentation H
  let P : Submodule (ZMod 2) (Additive (ReducedModule H)) :=
    AddSubgroup.toZModSubmodule 2 ((R.comap (ReducedModule H).subtype).toAddSubgroup)
  let S : Subrepresentation ρ := {
    toSubmodule := P
    apply_mem_toSubmodule := by
      intro h v hv
      exact (inferInstance : R.Normal).conj_mem v.toMul.val hv h }
  let σ : Representation (ZMod 2) H P := S.toRepresentation
  have hnfix : ¬ (⊤ : Submodule (ZMod 2) P) ≤ fixedSpace σ A := by
    intro hc
    apply hm
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro r hr b hb
    let v : ReducedModule H := ⟨r,hR.le_reducedPSubgroup hr⟩
    let w : P := ⟨Additive.ofMul v,hr⟩
    have hh := congrArg (fun a : P => a.val.toMul.val) (hc (show w ∈ ⊤ from trivial) ⟨b,hb⟩)
    change b*r*b⁻¹=r at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_not_fixed σ A hnfix
  have hi : IsIrrPlus ρ A (I.map P.subtype) := by
    apply IsIrrPlus.map_embedding ρ σ (MonoidHom.id H) P.subtype
      Subtype.val_injective (by intros; rfl)
    simpa only [Subgroup.map_id] using hI
  have hT : (T : Subgroup G).subgroupOf H ≤ normalizer (A : Set H) := le_normalizer_of_normal
  obtain ⟨J,hJ,hjir⟩ := exists_isIrrPlusWith_le_orbitSpan ρ hT T.isPGroup'.comap_subtype hi
  have hJP : J ≤ P := hJ.trans (orbitSpan_le ρ (Submodule.map_subtype_le P I)
    (by
      apply le_subspaceStabilizer
      intro t ht v hv
      exact S.apply_mem_toSubmodule t hv))
  refine ⟨subspaceImage H J,⟨⟨J,hjir,rfl⟩⟩,?_⟩
  rintro x ⟨r,⟨v,hv,rfl⟩,rfl⟩
  exact mem_map_of_mem H.subtype (hJP hv)
end CFSG.Quasithin.Chapter12.Section02

