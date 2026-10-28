module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki
public import Theory.SpecificGroups.Suzuki.RootOmega
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Inner lifts of elementary Suzuki actors

An exponent-two action on a nondegenerate Suzuki group lifts uniquely to a
homomorphism into that group: the odd outer group gives pointwise innerness,
and centerlessness proves the homomorphism laws. Sylow conjugacy places the
whole image in the literal root subgroup, where square-one elements are
central. The original actor and its action kernel are retained throughout.

Source: GLS IV, Chapter 4, Lemma 3.4(b,c); Huppert--Blackburn III, XI.3.1.
This is the inner-action coordinate input to the Suzuki Steinberg actor
argument in Aschbacher--Smith, 13.6.26, printed pp.934--935.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

private theorem suzuki_conj_injective (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)) := by
  have hmodel : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  let := hmodel.isSimple
  apply MulAut.conj_injective_of_center_eq_bot
  rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact False.elim (hmodel.not_commutative (fun x y => by
      have hx : x ∈ center (SuzukiMatrixGroup m) := by rw [h]; trivial
      exact (mem_center_iff.mp hx y).symm))

variable {A : Type*} [Group A] (m : ℕ)

/-- A square-one Suzuki action has a homomorphic inner lift with the same kernel. -/
theorem suzuki_exists_innerHom (hm : 1 ≤ m) (α : A →* MulAut (SuzukiMatrixGroup m))
    (hA : ∀ a : A, a ^ 2 = 1) :
    ∃ φ : A →* SuzukiMatrixGroup m, MulAut.conj.comp φ = α ∧ φ.ker = α.ker := by
  have hex (a : A) : ∃ b : SuzukiMatrixGroup m, MulAut.conj b = α a := by
    obtain ⟨b, hb, _⟩ := ZD.suzuki_involutoryAut_inner_and_twoRank m hm (α a)
      (by rw [← map_pow, hA, map_one])
    exact ⟨b, hb.symm⟩
  choose f hf using hex
  have hi := suzuki_conj_injective m hm
  let φ : A →* SuzukiMatrixGroup m :=
    { toFun := f
      map_one' := hi (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hi (by simp only [map_mul, hf]) }
  have he : MulAut.conj.comp φ = α := MonoidHom.ext hf
  refine ⟨φ, he, ?_⟩
  ext a
  change φ a = 1 ↔ α a = 1
  rw [← hf a, ← map_one MulAut.conj]
  exact hi.eq_iff.symm

/-- A single conjugation places the full elementary actor in the literal root center,
without assuming the action faithful or replacing the actor by its image. -/
theorem suzuki_exists_rootHom (hm : 1 ≤ m) (α : A →* MulAut (SuzukiMatrixGroup m))
    (hA : ∀ a : A, a ^ 2 = 1) :
    ∃ (g : SuzukiMatrixGroup m) (φ : A →* SuzukiRootSubgroup m),
      (∀ a, α a = MulAut.conj (MulAut.conj g⁻¹ (φ a : SuzukiMatrixGroup m))) ∧
      φ.ker = α.ker ∧
      ∀ a, φ a ∈ center (SuzukiRootSubgroup m) := by
  obtain ⟨f, hf, hk⟩ := suzuki_exists_innerHom m hm α hA
  have hp : IsPGroup 2 f.range := by
    rintro ⟨x, a, rfl⟩
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (f a) ^ (2 ^ 1) = 1
    rw [pow_one, ← map_pow, hA, map_one]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m (by omega)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Q P
  have hroot (a : A) : MulAut.conj g (f a) ∈ SuzukiRootSubgroup m := by
    rw [← hP, ← hg]
    exact ⟨f a, hQ ⟨a, rfl⟩, rfl⟩
  let φ : A →* SuzukiRootSubgroup m :=
    ((MulAut.conj g).toMonoidHom.comp f).codRestrict _ hroot
  have hφ (a : A) : (φ a : SuzukiMatrixGroup m) = MulAut.conj g (f a) := rfl
  refine ⟨g, φ, ?_, ?_, ?_⟩
  · intro a
    have ha : α a = MulAut.conj (f a) := (DFunLike.congr_fun hf a).symm
    rw [ha, hφ]
    congr 1
    simp only [MulAut.conj_apply, inv_inv]
    group
  · rw [← hk]
    ext a
    change φ a = 1 ↔ f a = 1
    constructor
    · intro ha
      apply (MulAut.conj g).injective
      simpa only [← hφ a, map_one, Subgroup.coe_one] using congrArg Subtype.val ha
    · intro ha
      apply Subtype.ext
      change MulAut.conj g (f a) = 1
      rw [ha, map_one]
  · intro a
    apply (suzukiRootSubgroup_square_iff_center m (by omega) _).mp
    rw [← map_pow, hA, map_one]

/-- Coordinates for any original group marking and elementary actor, with the
same kernel and a literal central-root homomorphism. -/
theorem suzuki_root_coordinates
    {K A : Type*} [Group K] [Group A]
    (m : ℕ) (hm : 1 ≤ m) (e : K ≃* SuzukiMatrixGroup m)
    (β : A →* MulAut K) (hA : ∀ a : A, a ^ 2 = 1) :
    ∃ (e' : K ≃* SuzukiMatrixGroup m) (φ : A →* SuzukiRootSubgroup m),
      (∀ (a : A) (z : K), e' (β a z) =
          (φ a : SuzukiMatrixGroup m) * e' z * (φ a : SuzukiMatrixGroup m)⁻¹) ∧
      φ.ker = β.ker ∧ ∀ a, φ a ∈ center (SuzukiRootSubgroup m) := by
  let α := (MulAut.congr e).toMonoidHom.comp β
  obtain ⟨g, φ, hφ, hk, hc⟩ := suzuki_exists_rootHom m hm α hA
  refine ⟨e.trans (MulAut.conj g), φ, ?_, ?_, hc⟩
  · intro a z
    have he := DFunLike.congr_fun (hφ a) (e z)
    have he' : e (β a z) =
        (MulAut.conj g⁻¹ (φ a : SuzukiMatrixGroup m)) * e z *
          (MulAut.conj g⁻¹ (φ a : SuzukiMatrixGroup m))⁻¹ := by
      simpa only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
        MulAut.conj_apply] using he
    change MulAut.conj g (e (β a z)) = _
    rw [he']
    simp only [MulAut.conj_apply, MulEquiv.trans_apply, mul_inv_rev, inv_inv]
    group
  · rw [hk]
    ext a
    change (MulAut.congr e) (β a) = 1 ↔ β a = 1
    rw [← (MulAut.congr e).map_one]
    exact (MulAut.congr e).injective.eq_iff

end BenderSuzuki.MatrixGroups
