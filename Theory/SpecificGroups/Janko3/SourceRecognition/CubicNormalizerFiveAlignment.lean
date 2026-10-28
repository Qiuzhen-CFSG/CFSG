module
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerKernelInversion
public import Theory.SpecificGroups.AlternatingSix.PGLNineFivePairs

/-!
# Align the third overlap while fixing the whole cubic pair

For two actual A₅ subgroups containing the same order-ten subgroup B,
the native projective calculation leaves only conjugation by the supplied
outer element t centralizing B. Cubic-kernel inversion cancels the action
of that conjugation on the full preimage of B⟨t⟩. The resulting correction
fixes every element of the full pair, fixes the cubic kernel pointwise,
and retains the literal projective complement.
-/

public noncomputable section
namespace Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
open Subgroup

/-- Align the literal A₅ overlaps without changing any element of the full
pair or the cubic kernel. The accompanying projective automorphism records
the exact action on the same complement. -/
theorem exists_pair_fixing_five_alignment (B H J : Subgroup P) (t : P)
    (hB : Nat.card B = 10)
    (hH : Nonempty (H ≃* alternatingGroup (Fin 5)))
    (hJ : Nonempty (J ≃* alternatingGroup (Fin 5)))
    (hBH : B ≤ H) (hBJ : B ≤ J)
    (ht : t ∉ derived) (htB : t ∈ centralizer (B : Set P)) :
    ∃ (τ : MulAut Model) (σ : MulAut P),
      (σ = 1 ∨ σ = MulAut.conj t) ∧
      (∀ x ∈ (B ⊔ zpowers t).comap projection, τ x = x) ∧
      (∀ z : Z, τ (SemidirectProduct.inl z) = SemidirectProduct.inl z) ∧
      (∀ p : P, τ (SemidirectProduct.inr p) = SemidirectProduct.inr (σ p)) ∧
      H.map σ.toMonoidHom = J ∧
      (H.map (SemidirectProduct.inr : P →* Model)).map τ.toMonoidHom =
        J.map (SemidirectProduct.inr : P →* Model) := by
  rcases AlternatingSix.PGLNineFivePairs.five_overgroups_eq_or_conjugate
    B H J t hB hH hJ hBH hBJ ht htB with he | he
  · subst J
    refine ⟨1,1,Or.inl rfl,fun _ _ => rfl,fun _ => rfl,fun _ => rfl,?_,?_⟩
    all_goals exact map_id _
  · have htQ : t ∈ centralizer ((B ⊔ zpowers t : Subgroup P) : Set P) := by
      have hB' : B ≤ centralizer (zpowers t : Set P) :=
        le_centralizer_iff.mpr (zpowers_le.mpr htB)
      have ht' : zpowers t ≤ centralizer (zpowers t : Set P) :=
        le_centralizer_iff_isMulCommutative.mpr inferInstance
      exact (le_centralizer_iff.mp (sup_le hB' ht')) (mem_zpowers t)
    obtain ⟨τ,hfix,hr,hl⟩ := exists_pair_fixing_complement_correction
      (B ⊔ zpowers t) t ht htQ
    refine ⟨τ,MulAut.conj t,Or.inr rfl,hfix,hl,hr,he.symm,?_⟩
    rw [map_map]
    have hcomp : τ.toMonoidHom.comp (SemidirectProduct.inr : P →* Model) =
        (SemidirectProduct.inr : P →* Model).comp (MulAut.conj t).toMonoidHom := by
      apply MonoidHom.ext
      intro p
      exact hr p
    rw [hcomp,←map_map,←he]
end Sporadic.Janko3.SourceRecognition.CubicNormalizerModel
