module
public import Theory.Representation.BinaryOffender.SubgroupMovedDimension
public import Theory.Representation.BinaryOffender.PerfectMoved
public import Theory.Representation.BinaryPrimeDegree

/-!
# A small commutator has only one noncentral simple section

Let a simple perfect group K act faithfully on a binary space. If an odd
prime p divides |K|, every nontrivial section has dimension at least the
order of 2 modulo p. A commutator of dimension less than twice that bound
therefore cannot have both a noncentral invariant subspace and a noncentral
quotient. Perfectness makes its own commutators fill it, so its quotient by
the full fixed subspace is irreducible: the literal Irr⁺ conclusion.
Source application: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A small commutator for a simple perfect actor has an irreducible central quotient. -/
theorem isIrrPlus_moved_of_prime_degree
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    [IsSimpleGroup K] [Group.IsPerfect K] (hf : Function.Injective (ρ.comp K.subtype))
    {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (hdiv : p ∣ Nat.card K)
    (hsmall : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) <
      2 * orderOf (2 : ZMod p)) :
    IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) := by
  let I := subspaceCommutator ρ ⊤ K
  have hI : K ≤ subspaceStabilizer ρ I := subspaceCommutator_invariant ρ ⊤ K
  have hcomm : subspaceCommutator ρ I K = I := subspaceCommutator_idempotent_of_perfect ρ K
  apply isIrrPlus_of_minimal ρ hI hcomm
  · intro hc
    have ht := le_fixedSpace_of_commutator_le_fixedSpace ρ K ⊤
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hc
    have hone (k : K) : k = 1 := by
      apply hf
      ext v
      exact (ht Submodule.mem_top k).trans (by simp)
    obtain ⟨k,hk⟩ := exists_ne (1 : K)
    exact hk (hone k)
  · intro J hJ hJI
    by_cases hj : J ≤ fixedSpace ρ K
    · exact Or.inr hj
    left
    let σ : Representation (ZMod 2) K I := Representation.subrepresentation
      (ρ.comp K.subtype) I (fun k v hv => (hI k.property v).2 hv)
    let N : Subrepresentation σ := {
      toSubmodule := J.comap I.subtype
      apply_mem_toSubmodule k v hv := (hJ k.property v.val).2 hv }
    have hN : Function.Injective N.toRepresentation := by
      rcases N.toRepresentation.normal_ker.eq_bot_or_eq_top with h | h
      · exact N.toRepresentation.ker_eq_bot_iff.mp h
      · exfalso
        apply hj
        have ht : N.toRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp h
        intro v hv k
        have hh := DFunLike.congr_fun (congrArg (fun τ => τ k) ht)
          (⟨⟨v,hJI hv⟩,hv⟩ : N.toSubmodule)
        exact congrArg (fun x : N.toSubmodule => x.val.val) hh
    have hdN := Representation.BinaryPrimeDegree.orderOf_le_finrank N.toRepresentation hN hp hp2 hdiv
    have hq : N.quotientRepresentation = 1 := by
      rcases N.quotientRepresentation.normal_ker.eq_bot_or_eq_top with h | h
      · have hdQ := Representation.BinaryPrimeDegree.orderOf_le_finrank
          N.quotientRepresentation (N.quotientRepresentation.ker_eq_bot_iff.mp h) hp hp2 hdiv
        have hd := N.toSubmodule.finrank_quotient_add_finrank
        change Module.finrank (ZMod 2) I < 2 * orderOf (2 : ZMod p) at hsmall
        change Module.finrank (ZMod 2) (I ⧸ N.toSubmodule) +
          Module.finrank (ZMod 2) N.toSubmodule = Module.finrank (ZMod 2) I at hd
        omega
      · exact MonoidHom.ker_eq_top_iff.mp h
    have hle : subspaceCommutator ρ I K ≤ J := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k,hk,v,hv,rfl⟩
      let vI : I := ⟨v,hv⟩
      have hh := DFunLike.congr_fun (congrArg (fun τ => τ (⟨k,hk⟩ : K)) hq)
        (N.toSubmodule.mkQ vI)
      have hh' : N.toSubmodule.mkQ (σ ⟨k,hk⟩ vI - vI) = 0 := by
        rw [map_sub]
        change N.quotientRepresentation ⟨k,hk⟩ (N.toSubmodule.mkQ vI) -
          N.toSubmodule.mkQ vI = 0
        rw [hh]
        exact sub_self _
      exact (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hh'
    exact le_antisymm hJI (hcomm ▸ hle)
end Representation.BinaryOffender
