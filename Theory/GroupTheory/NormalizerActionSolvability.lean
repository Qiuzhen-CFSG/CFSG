module

public import Theory.GroupTheory.SylowNormalizerOuterAction

/-!
# Solvability of relative normalizer actions

An ambient isomorphism transports the entire relative normalizer action,
including its centralizer kernel. A quotient whose kernel contains that
centralizer is a quotient of the action image. Together these facts rule out
a nonsolvable action on a conjugate subgroup when its original normalizer
is controlled by a group with solvable action.

Application: Aschbacher--Smith, 6.1.14(5), printed pp.671--672.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G H A : Type*} [Group G] [Group H] [Group A]

/-- Increasing the actor increases the literal action image. -/
theorem normalizerAction_range_mono {K M Z : Subgroup G} (h : K ≤ M) :
    (normalizerAction K Z).range ≤ (normalizerAction M Z).range := by
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨k, h k.property.1, k.property.2⟩, rfl⟩

/-- Transport the full relative action, not just the acting abstract group. -/
theorem normalizerAction_range_equiv_map (K Z : Subgroup G) (e : G ≃* H) :
    Nonempty ((normalizerAction K Z).range ≃*
      (normalizerAction (K.map e.toMonoidHom) (Z.map e.toMonoidHom)).range) := by
  let eZ := e.subgroupMap Z
  have hn : (K ⊓ normalizer (Z : Set G)).map e.toMonoidHom =
      K.map e.toMonoidHom ⊓ normalizer (Z.map e.toMonoidHom : Set H) := by
    rw [map_inf _ _ _ e.injective, map_equiv_normalizer_eq]
  let eN := (e.subgroupMap (K ⊓ normalizer (Z : Set G))).trans
    (MulEquiv.subgroupCongr hn)
  let eA := MulAut.congr eZ
  let a := normalizerAction K Z
  let b := normalizerAction (K.map e.toMonoidHom) (Z.map e.toMonoidHom)
  have hc (k : (K ⊓ normalizer (Z : Set G) : Subgroup G)) : eA (a k) = b (eN k) := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := eZ.surjective y
    apply Subtype.ext
    change (eZ (a k (eZ.symm (eZ x))) : H) = _
    rw [eZ.symm_apply_apply]
    change e ((k : G) * (x : G) * (k : G)⁻¹) =
      e (k : G) * e (x : G) * (e (k : G))⁻¹
    simp only [map_mul, map_inv]
  have he : a.range.map eA.toMonoidHom = b.range := by
    ext x
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨eN k, (hc k).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨j, rfl⟩ := eN.surjective k
      exact ⟨a j, ⟨j, rfl⟩, hc j⟩
  exact ⟨(eA.subgroupMap a.range).trans (MulEquiv.subgroupCongr he)⟩

/-- A nonsolvable quotient detected by the action obstructs solvability. -/
theorem normalizerAction_not_solvable_of_quotient
    (K Z : Subgroup G) (hKN : K ≤ normalizer (Z : Set G))
    (q : K →* A) (hq : Function.Surjective q)
    (hk : K ⊓ centralizer (Z : Set G) ≤ q.ker.map K.subtype)
    (hA : ¬ Group.IsSolvable A) :
    ¬ Group.IsSolvable (normalizerAction K Z).range := by
  intro hs
  let := hs
  let a := normalizerAction K Z
  let b : (K ⊓ normalizer (Z : Set G) : Subgroup G) →* A := q.comp (inclusion inf_le_left)
  have hb : Function.Surjective b := by
    intro x
    obtain ⟨k, rfl⟩ := hq x
    exact ⟨⟨k, k.property, hKN k.property⟩, rfl⟩
  have hker : a.ker ≤ b.ker := by
    intro k hka
    have hc : (k : G) ∈ centralizer (Z : Set G) := by
      have he : inclusion (show K ⊓ normalizer (Z : Set G) ≤ normalizer (Z : Set G)
          from inf_le_right) k ∈ Z.normalizerMonoidHom.ker := hka
      rw [normalizerMonoidHom_ker] at he
      exact he
    obtain ⟨j, hj, hjk⟩ := hk ⟨k.property.1, hc⟩
    have he : j = inclusion (show K ⊓ normalizer (Z : Set G) ≤ K from inf_le_left) k :=
      Subtype.ext hjk
    change inclusion (show K ⊓ normalizer (Z : Set G) ≤ K from inf_le_left) k ∈ q.ker
    exact he ▸ hj
  let f := QuotientGroup.lift a.ker b hker
  let e := QuotientGroup.quotientKerEquivRange a
  have hf : Function.Surjective (f.comp e.symm.toMonoidHom) :=
    (QuotientGroup.lift_surjective_of_surjective a.ker b hb hker).comp e.symm.surjective
  exact hA (Group.isSolvable_of_surjective hf)

/-- Normalizer control and solvable action contradict a nonsolvable action
on a literal conjugate subgroup. -/
theorem centralizer_not_le_of_nonsolvable_conjugate_action
    (M Z K : Subgroup G) (g : G)
    (hN : centralizer (Z : Set G) ≤ M → normalizer (Z : Set G) ≤ M)
    (hs : Group.IsSolvable (normalizerAction M Z).range)
    (hK : K ≤ normalizer (Z.map (MulAut.conj g).toMonoidHom : Set G))
    (hns : ¬ Group.IsSolvable
      (normalizerAction K (Z.map (MulAut.conj g).toMonoidHom)).range) :
    ¬ centralizer (Z : Set G) ≤ M := by
  intro hC
  let e := MulAut.conj g
  obtain ⟨eA⟩ := normalizerAction_range_equiv_map M Z e
  let := hs
  let : Group.IsSolvable (normalizerAction (M.map e.toMonoidHom)
      (Z.map e.toMonoidHom)).range :=
    Group.isSolvable_of_surjective (f := eA.toMonoidHom) eA.surjective
  have hKM : K ≤ M.map e.toMonoidHom := by
    apply hK.trans
    rw [← map_equiv_normalizer_eq Z e]
    exact map_mono (hN hC)
  exact hns (Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (normalizerAction_range_mono
      (Z := Z.map e.toMonoidHom) hKM)))
end Theory.GroupTheory
