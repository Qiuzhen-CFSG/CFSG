module
public import Theory.SpecificGroups.AlternatingSeven.SevenFixer
public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Pointwise fixers through a perfect central cover of A₇

Every automorphism descends through the actual central covering map. A
nonsolvable seven-divisible subgroup has trivial pointwise fixer downstairs;
uniqueness of homomorphisms from a perfect group lifts that identity upstairs.
The ambient version retains both subgroup embeddings and the covering map.

The consumer is the A₇ row of original 12.2.25 in
LocalConfigurationRigidityHigherSevenCovers. Source: GLS III, Theorem 5.2.1,
and Aschbacher–Smith, original 12.2.25, printed p.805.
-/

public noncomputable section
open Subgroup
namespace AlternatingSeven.SevenFixer

/-- The pointwise fixer calculation lifts through the actual perfect central cover. -/
theorem central_cover_automorphism_eq_one
    {E : Type*} [Group E]
    (f : PerfectCentralCovering.Cover E (alternatingGroup (Fin 7)))
    (B : Subgroup E)
    (hns : ¬ Group.IsSolvable (B.map f.toMonoidHom))
    (hseven : 7 ∣ Nat.card (B.map f.toMonoidHom))
    (a : MulAut E) (ha : ∀ b : B, a b.val = b.val) : a = 1 := by
  let := f.isPerfect
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 7)) := Group.IsPerfect.ofSurjective f.surjective
  have hz : center (alternatingGroup (Fin 7)) = ⊥ := by
    rcases (inferInstance : (center (alternatingGroup (Fin 7))).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  have hk : f.toMonoidHom.ker = center E := by
    rw [← f.comap_center,hz]
    rfl
  obtain ⟨b,hb⟩ := f.exists_descended_aut hk a
  have he : b = 1 := automorphism_eq_one (B.map f.toMonoidHom) hns hseven b (by
    rintro ⟨_,x,hx,rfl⟩
    exact (hb x).trans (congrArg f.toMonoidHom (ha ⟨x,hx⟩)))
  apply MulEquiv.toMonoidHom_injective
  apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    f.toMonoidHom f.ker_le_center
  apply MonoidHom.ext
  intro x
  exact (hb x).symm.trans (DFunLike.congr_fun he (f.toMonoidHom x))

/-- Ambient centralization retains the original subgroup and covering map. -/
theorem central_cover_centralizes_of_centralizes_subgroup
    {X : Type*} [Group X] (K B : Subgroup X) (_hBK : B ≤ K)
    (f : PerfectCentralCovering.Cover K (alternatingGroup (Fin 7)))
    (hns : ¬ Group.IsSolvable ((B.subgroupOf K).map f.toMonoidHom))
    (hseven : 7 ∣ Nat.card ((B.subgroupOf K).map f.toMonoidHom))
    (x : X) (hxK : x ∈ normalizer (K : Set X))
    (hxB : x ∈ centralizer (B : Set X)) : x ∈ centralizer (K : Set X) := by
  let a := K.normalizerMonoidHom ⟨x,hxK⟩
  have he : a = 1 := central_cover_automorphism_eq_one f (B.subgroupOf K) hns hseven a (by
    intro b
    apply Subtype.ext
    change x * (b.val : X) * x⁻¹ = (b.val : X)
    rw [← hxB b.val b.property,mul_inv_cancel_right])
  intro k hk
  have hh := congrArg (fun z : MulAut K => (z ⟨k,hk⟩ : X)) he
  change x*k*x⁻¹ = k at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm
end AlternatingSeven.SevenFixer
