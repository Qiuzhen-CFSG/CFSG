module
public import Theory.Representation.BinaryAlternatingFiveExtension.OverlapFactorization

/-!
# Affine overlap corrections that extend across the symmetric plane

The ordinary overlap correction is a lifted four-letter permutation followed
by conjugation by a translation. Retaining those two witnesses realizes the
plane correction as conjugation in the full affine S₅ group. Its permutation
fixes the fifth letter, so it fixes the marked root as well. The final theorem
keeps both ordinary amalgam squares and the commuting affine A₅-to-S₅ square.

This is the extension-compatible correction used to assemble the doubled
normal A₅ amalgam in Aschbacher--Smith 13.5.17, printed p.922.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.OverlapFactorizationExtension
open AlternatingFiveBorel OverlapFactorization
open Theory.GroupTheory RankTwoAmalgam
abbrev SymmetricModel := V ⋊[coreAction] Equiv.Perm (Fin 5)

def symmetricEmbedding : AlternatingModel →* SymmetricModel :=
  SemidirectProduct.map (MonoidHom.id V) (alternatingGroup (Fin 5)).subtype
    (fun _ => rfl)

@[simp] theorem symmetricEmbedding_left (x : AlternatingModel) :
    (symmetricEmbedding x).left=x.left := by rfl
@[simp] theorem symmetricEmbedding_right (x : AlternatingModel) :
    (symmetricEmbedding x).right=x.right.val := by rfl
@[simp] theorem symmetricEmbedding_inl (v : V) :
    symmetricEmbedding (SemidirectProduct.inl v)=SemidirectProduct.inl v := by rfl

theorem symmetricEmbedding_injective : Function.Injective symmetricEmbedding := by
  intro x y h
  apply SemidirectProduct.ext
  · exact congrArg (fun t : SymmetricModel => t.left) h
  · exact Subtype.ext (congrArg (fun t : SymmetricModel => t.right) h)

/-- Fixing the distinguished letter is exactly the needed affine root marking. -/
theorem conj_marked_root (a : SymmetricModel) (ha : a.right 4=4) :
    MulAut.conj a
      (SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)) =
        SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z) := by
  have hz : coreAction a.right (Multiplicative.ofAdd FiveCentralizerGeometry.z) =
      Multiplicative.ofAdd FiveCentralizerGeometry.z :=
    congrArg Multiplicative.ofAdd (AlternatingFiveFlag.fixes_z_iff a.right |>.mpr ha)
  have hc : a*SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z) =
      SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)*a := by
    apply SemidirectProduct.ext
    · change a.left * coreAction a.right (Multiplicative.ofAdd FiveCentralizerGeometry.z) =
        Multiplicative.ofAdd FiveCentralizerGeometry.z * coreAction 1 a.left
      rw [hz,map_one,MulAut.one_apply,mul_comm]
    · simp
  change a*SemidirectProduct.inl (Multiplicative.ofAdd FiveCentralizerGeometry.z)*a⁻¹ = _
  rw [hc,mul_assoc,mul_inv_cancel,mul_one]

theorem symmetricEmbedding_standardAction (σ : Equiv.Perm (Fin 5))
    (x : AlternatingModel) :
    symmetricEmbedding (standardAction σ x) =
      MulAut.conj (SemidirectProduct.inr σ) (symmetricEmbedding x) := by
  apply SemidirectProduct.ext
  · simp [MulAut.conj_apply]
  · rfl

theorem quotient_fixed_inner_factor (γ : MulAut BorelModel)
    (hq : ∀ x : BorelModel, (γ x).right=x.right) :
    ∃ l : MulAut BorelModel, (l=1 ∨ l=Overlap.borelTwist) ∧
      Function.Involutive l ∧ ∃ n : V, ∀ x : BorelModel,
        (γ*l) x=SemidirectProduct.inl n*x*(SemidirectProduct.inl n)⁻¹ := by
  obtain ⟨f,hf⟩ := exists_kernel_action γ (fun x hx => (hq x).trans hx)
  have finish (l : MulAut BorelModel) (hl : l=1 ∨ l=Overlap.borelTwist)
      (hi : Function.Involutive l)
      (hV : ∀ n : V, (γ*l) (SemidirectProduct.inl n)=SemidirectProduct.inl n)
      (hlq : ∀ x : BorelModel, (l x).right=x.right) :
      ∃ l : MulAut BorelModel, (l=1 ∨ l=Overlap.borelTwist) ∧
        Function.Involutive l ∧ ∃ n : V, ∀ x : BorelModel,
          (γ*l) x=SemidirectProduct.inl n*x*(SemidirectProduct.inl n)⁻¹ := by
    obtain ⟨n,hn⟩ := BorelCohomology.automorphism_translation_correction (γ*l) hV
      (fun x => (hq (l x)).trans (hlq x))
    exact ⟨l,hl,hi,n,hn⟩
  rcases Overlap.quotient_fixed_module_cases γ f hf hq with h|h
  · apply finish 1 (Or.inl rfl) (fun _ => rfl)
    · intro n
      simpa [h n.toAdd] using hf n.toAdd
    · exact fun _ => rfl
  · apply finish Overlap.borelTwist (Or.inr rfl) borelTwist_involutive
    · intro n
      have hn : n=Multiplicative.ofAdd n.toAdd := by simp
      rw [hn]
      change γ (Overlap.borelTwist (SemidirectProduct.inl (Multiplicative.ofAdd n.toAdd)))=_
      rw [borelTwist_inl,hf,h,Overlap.twist_involutive]
    · exact Overlap.borelTwist_right

/-- Correcting the ordinary overlap retains an inner extension to the full
symmetric affine plane. The conjugating actor fixes the marked fifth letter. -/
theorem iso_with_inner_extension {P : Type*} [Group P]
    (i : BorelModel →* P) (ht : ExtendsAcross i Overlap.borelTwist)
    (α : MulAut BorelModel)
    (hN : ∀ x : BorelModel, x.right=1 → (α x).right=1) :
    ∃ e : Iso
      (twistRight (⟨i,borelEmbedding⟩ : RankTwoAmalgam P BorelModel AlternatingModel) α)
      (⟨i,borelEmbedding⟩ : RankTwoAmalgam P BorelModel AlternatingModel),
      ∃ a : SymmetricModel, a.right 4=4 ∧
        ∀ x : AlternatingModel, symmetricEmbedding (e.right x) =
          MulAut.conj a (symmetricEmbedding x) := by
  obtain ⟨β,hβ⟩ := exists_quotient_action α hN
  obtain ⟨σ,hσ⟩ := actorPerm_surjective β
  let θ := borelPermutation σ
  have hθ (x : BorelModel) : (θ x).right=β x.right := by
    rw [borelPermutation_right,hσ]
  let γ : MulAut BorelModel := θ⁻¹*α
  have hγ (x : BorelModel) : (γ x).right=x.right := by
    apply β.injective
    calc
      β ((γ x).right) = (θ (γ x)).right := (hθ (γ x)).symm
      _ = (α x).right := by simp [γ]
      _ = β x.right := hβ x
  obtain ⟨l,hl,hli,n,hn⟩ := quotient_fixed_inner_factor γ hγ
  let r : MulAut AlternatingModel :=
    standardAction (liftPerm σ) * MulAut.conj (SemidirectProduct.inl n)
  have hr (x : BorelModel) : r (borelEmbedding x)=borelEmbedding ((α*l) x) := by
    change standardAction (liftPerm σ)
      (borelEmbedding (SemidirectProduct.inl n)*borelEmbedding x*
        (borelEmbedding (SemidirectProduct.inl n))⁻¹) = _
    rw [←map_inv,←map_mul,←map_mul,←hn,borelPermutation_plane]
    congr 1
    change θ ((γ*l) x)=(α*l) x
    simp [γ]
  let c : SymmetricModel := SemidirectProduct.inr (liftPerm σ)*SemidirectProduct.inl n
  have hc (x : AlternatingModel) :
      symmetricEmbedding (r x)=MulAut.conj c (symmetricEmbedding x) := by
    change symmetricEmbedding (standardAction (liftPerm σ)
      (MulAut.conj (SemidirectProduct.inl n) x)) = _
    rw [symmetricEmbedding_standardAction]
    simp only [MulAut.conj_apply,map_mul,map_inv,symmetricEmbedding_inl]
    dsimp only [c]
    group
  have hlp : ExtendsAcross i l := by
    rcases hl with rfl|rfl
    · exact ⟨1,fun _ => rfl⟩
    · exact ht
  obtain ⟨lp,hlp⟩ := hlp
  let e : Iso
      (twistRight (⟨i,borelEmbedding⟩ : RankTwoAmalgam P BorelModel AlternatingModel) α)
      (⟨i,borelEmbedding⟩ : RankTwoAmalgam P BorelModel AlternatingModel) := {
    left := lp
    middle := l
    right := r.symm
    left_commutes := hlp
    right_commutes x := by
      change r.symm (borelEmbedding (α x))=borelEmbedding (l x)
      apply r.injective
      rw [r.apply_symm_apply,hr]
      change borelEmbedding (α x)=borelEmbedding (α (l (l x)))
      rw [hli] }
  refine ⟨e,c⁻¹,?_,?_⟩
  · change ((liftPerm σ)⁻¹) 4=4
    have hh := congrArg (liftPerm σ).symm (liftPerm_last σ)
    simpa using hh.symm
  · intro x
    change symmetricEmbedding (r.symm x)=MulAut.conj c⁻¹ (symmetricEmbedding x)
    apply (MulAut.conj c).injective
    rw [←hc,r.apply_symm_apply]
    simp [MulAut.conj_apply, mul_assoc]

end BinaryPermutation.AlternatingFiveExtension.OverlapFactorizationExtension
