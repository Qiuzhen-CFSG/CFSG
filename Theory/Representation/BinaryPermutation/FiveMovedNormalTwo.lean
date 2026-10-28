module
public import Theory.Representation.BinaryPermutation.SevenPointChiefFactor
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.TwoDimensionalOddOrder

/-!
# Extending the five-point moved module across a normal two-subgroup

The moved space of a normal subgroup is invariant under the ambient action.
If it is the marked irreducible binary five-point core, a normal two-subgroup
has a nonzero fixed vector there. Its fixed space is invariant under the
five-point actor, so irreducibility makes the entire moved space fixed.
Consequently the prescribed five-point marking extends across the normal
two-subgroup, even when that subgroup moves the rest of the ambient module.

Source application: Aschbacher–Smith 12.2.19, printed pp.801–802. This supplies
the original two-core action on the deleted-five summand of a deleted-seven
module; the modular fixed-vector argument is general.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W]
  [Module (ZMod 2) W]

/-- A normal two-subgroup fixes a marked irreducible five-point moved space. -/
theorem five_moved_fixed_by_normal_two
    (τ : Representation (ZMod 2) A W) (K Q : Subgroup A) [K.Normal] [Q.Normal]
    (hQ : IsPGroup 2 Q) (f : K →* alternatingGroup (Fin 5))
    (hf : Function.Surjective f)
    (j : core (Fin 5) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ k v, j (alternatingCoreRepresentation (Fin 5) (f k) v) = τ k (j v))
    (hr : j.range = subspaceCommutator τ ⊤ K) :
    ∀ (q : Q) v, τ q (j v) = j v := by
  let M := j.range
  have hM : (⊤ : Subgroup A) ≤ subspaceStabilizer τ M := by
    rw [show M = subspaceCommutator τ ⊤ K from hr]
    exact subspaceCommutator_invariant_normalizer τ
      (le_subspaceStabilizer τ ⊤ (by intros; trivial)) le_normalizer_of_normal
  let σ : Subrepresentation τ := ⟨M,fun a v hv => (hM (mem_top a) v).2 hv⟩
  let : Nontrivial (core (Fin 5)) := Module.nontrivial_of_finrank_pos (by
    rw [finrank_core]; decide)
  let : Nontrivial M := (LinearEquiv.ofInjective j hj).injective.nontrivial
  obtain ⟨w,hw,hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (by simp [ZMod.ringChar_zmod_n] : ringChar (ZMod 2) ≠ 0)
    (show IsPGroup (ringChar (ZMod 2)) Q by simpa [ZMod.ringChar_zmod_n] using hQ)
    (σ.toRepresentation.comp Q.subtype)
  let F := (fixedSpace τ Q).comap j
  have hF (a : alternatingGroup (Fin 5)) (v : core (Fin 5)) (hv : v ∈ F) :
      coreRepresentation (Fin 5) a.val v ∈ F := by
    obtain ⟨k,rfl⟩ := hf a
    change j (alternatingCoreRepresentation (Fin 5) (f k) v) ∈ fixedSpace τ Q
    rw [he]
    exact (fixedSpace_stable_of_normal τ Q (mem_top k.val) (j v)).2 hv
  have hFt : F = ⊤ := by
    rcases SevenPointChiefFactor.fiveCore_simple F hF with hb | ht
    · obtain ⟨v,hv⟩ := w.property
      have hvF : v ∈ F := by
        intro q
        change τ q (j v) = j v
        rw [hv]
        exact congrArg Subtype.val (hfix q)
      have hv0 : v = 0 := by simpa only [hb,Submodule.mem_bot] using hvF
      apply False.elim
      apply hw
      apply Subtype.ext
      change (w : W) = 0
      rw [←hv,hv0,map_zero]
    · exact ht
  intro q v
  have hv : v ∈ F := hFt ▸ Submodule.mem_top
  exact hv q

end BinaryPermutation

namespace BinaryPermutation
open Subgroup Representation Representation.BinaryOffender
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W]
  [Module (ZMod 2) W]

/-- The original marking on the moved space extends across the normal
two-subgroup, with the prescribed quotient map. -/
theorem five_moved_embedding_extends
    (τ : Representation (ZMod 2) A W) (K Q : Subgroup A) [K.Normal] [Q.Normal]
    (hQ : IsPGroup 2 Q) (hgen : K ⊔ Q = ⊤)
    (f : A →* alternatingGroup (Fin 5)) (hf : Function.Surjective (f.comp K.subtype))
    (hk : Q ≤ f.ker)
    (j : core (Fin 5) →ₗ[ZMod 2] W) (hj : Function.Injective j)
    (he : ∀ k : K, ∀ v, j (alternatingCoreRepresentation (Fin 5) (f k) v) = τ k (j v))
    (hr : j.range = subspaceCommutator τ ⊤ K) :
    ∀ a v, j (alternatingCoreRepresentation (Fin 5) (f a) v) = τ a (j v) := by
  have hfix := five_moved_fixed_by_normal_two τ K Q hQ (f.comp K.subtype) hf j hj he hr
  intro a v
  obtain ⟨k,hk',q,hq,rfl⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top a)
  rw [f.map_mul,hk hq,mul_one,τ.map_mul,Module.End.mul_apply,hfix ⟨q,hq⟩]
  exact he ⟨k,hk'⟩ v
end BinaryPermutation
