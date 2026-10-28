module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Extending a homomorphism across an involution

An injective copy of a group and a normalizing involution outside it have two
cosets. Compatible images of the group and involution extend uniquely to their
join. We construct the graph of this extension as a subgroup of the product;
its first projection is bijective. The second projection is injective when its
two cosets are distinct and the original group map is injective.

The concrete consumer is the Peirce SL₃-with-graph subgroup in
`Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup`.
Source application: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, p.283.
-/

public section
namespace InvolutoryExtension
variable {A G H : Type*} [Group A] [Group G] [Group H]
variable (f : A →* G) (j : A →* H) (t : G) (s : H) (σ : A → A)
  (ht : t * t = 1) (hs : s * s = 1)
  (hf : ∀ a, t * f a = f (σ a) * t)
  (hj : ∀ a, s * j a = j (σ a) * s)

include hf in
private theorem mul10 (a b : A) :
    (f a * t) * f b = f (a * σ b) * t := by
  rw [map_mul, mul_assoc, hf, ← mul_assoc]
include ht hf in
private theorem mul11 (a b : A) :
    (f a * t) * (f b * t) = f (a * σ b) := by
  rw [← mul_assoc, mul10 f t σ hf, mul_assoc, ht, mul_one]
include ht hf in
private theorem inv1 (a : A) : (f a * t)⁻¹ = f (σ a⁻¹) * t := by
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht, ← map_inv, hf]

private def relation : Subgroup (G × H) where
  carrier := {x | ∃ a, x = (f a, j a) ∨ x = (f a * t, j a * s)}
  one_mem' := ⟨1, Or.inl (by simp; rfl)⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl | rfl⟩ ⟨b, rfl | rfl⟩
    · exact ⟨a * b, Or.inl (by simp)⟩
    · exact ⟨a * b, Or.inr (by simp [mul_assoc])⟩
    · exact ⟨a * σ b, Or.inr (Prod.ext (mul10 f t σ hf a b) (mul10 j s σ hj a b))⟩
    · exact ⟨a * σ b, Or.inl
        (Prod.ext (mul11 f t σ ht hf a b) (mul11 j s σ hs hj a b))⟩
  inv_mem' := by
    rintro _ ⟨a, rfl | rfl⟩
    · exact ⟨a⁻¹, Or.inl (by simp)⟩
    · exact ⟨σ a⁻¹, Or.inr (Prod.ext (inv1 f t σ ht hf a) (inv1 j s σ hs hj a))⟩

private def first : relation f j t s σ ht hs hf hj →* G :=
  (MonoidHom.fst G H).comp (relation f j t s σ ht hs hf hj).subtype
private def second : relation f j t s σ ht hs hf hj →* H :=
  (MonoidHom.snd G H).comp (relation f j t s σ ht hs hf hj).subtype

private theorem first_range :
    (first f j t s σ ht hs hf hj).range = f.range ⊔ Subgroup.zpowers t := by
  apply le_antisymm
  · rintro _ ⟨⟨_, ⟨a, rfl | rfl⟩⟩, rfl⟩
    · exact Subgroup.mem_sup_left ⟨a, rfl⟩
    · exact Subgroup.mul_mem_sup ⟨a, rfl⟩ (Subgroup.mem_zpowers _)
  · apply sup_le
    · rintro _ ⟨a, rfl⟩
      exact ⟨⟨(f a, j a), a, Or.inl rfl⟩, rfl⟩
    · apply Subgroup.zpowers_le.mpr
      exact ⟨⟨(t, s), 1, Or.inr (by simp)⟩, rfl⟩

private theorem first_injective (hfi : Function.Injective f) (htf : t ∉ f.range) :
    Function.Injective (first f j t s σ ht hs hf hj) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  rintro ⟨_, ⟨a, rfl | rfl⟩⟩ he
  · have ha : a = 1 := hfi ((show f a = 1 from he).trans (map_one f).symm)
    subst a
    apply Subtype.ext
    simp
  · have ha : f a * t = 1 := he
    exfalso
    exact htf ⟨a⁻¹, by rw [map_inv]; exact inv_eq_of_mul_eq_one_right ha⟩

/-- Extend compatible maps across an involution outside the first subgroup. -/
noncomputable def lift (hfi : Function.Injective f) (htf : t ∉ f.range) :
    (f.range ⊔ Subgroup.zpowers t : Subgroup G) →* H :=
  (second f j t s σ ht hs hf hj).comp
    (((MonoidHom.ofInjective (first_injective f j t s σ ht hs hf hj hfi htf)).trans
      (MulEquiv.subgroupCongr (first_range f j t s σ ht hs hf hj))).symm.toMonoidHom)

private theorem lift_pair (hfi : Function.Injective f) (htf : t ∉ f.range)
    (x : relation f j t s σ ht hs hf hj) :
    lift f j t s σ ht hs hf hj hfi htf
      ⟨x.val.1, (first_range f j t s σ ht hs hf hj) ▸
        (show first f j t s σ ht hs hf hj x ∈
          (first f j t s σ ht hs hf hj).range from ⟨x, rfl⟩)⟩ = x.val.2 := by
  exact congrArg (second f j t s σ ht hs hf hj)
    (((MonoidHom.ofInjective (first_injective f j t s σ ht hs hf hj hfi htf)).trans
      (MulEquiv.subgroupCongr (first_range f j t s σ ht hs hf hj))).symm_apply_apply x)

/-- The extension agrees with the prescribed map on the original subgroup. -/
theorem lift_block (hfi : Function.Injective f) (htf : t ∉ f.range) (a : A) :
    lift f j t s σ ht hs hf hj hfi htf
      ⟨f a, Subgroup.mem_sup_left ⟨a, rfl⟩⟩ = j a :=
  lift_pair f j t s σ ht hs hf hj hfi htf ⟨(f a, j a), a, Or.inl rfl⟩

/-- The adjoined involution has its prescribed image. -/
theorem lift_graph (hfi : Function.Injective f) (htf : t ∉ f.range) :
    lift f j t s σ ht hs hf hj hfi htf
      ⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩ = s :=
  lift_pair f j t s σ ht hs hf hj hfi htf ⟨(t, s), 1, Or.inr (by simp)⟩

/-- Distinct cosets and injectivity on the original subgroup imply faithfulness. -/
theorem lift_injective (hfi : Function.Injective f) (htf : t ∉ f.range)
    (hji : Function.Injective j) (hsj : s ∉ j.range) :
    Function.Injective (lift f j t s σ ht hs hf hj hfi htf) := by
  have hsec : Function.Injective (second f j t s σ ht hs hf hj) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro ⟨_, ⟨a, rfl | rfl⟩⟩ he
    · have ha : a = 1 := hji ((show j a = 1 from he).trans (map_one j).symm)
      subst a
      apply Subtype.ext
      simp
    · have ha : j a * s = 1 := he
      exfalso
      exact hsj ⟨a⁻¹, by rw [map_inv]; exact inv_eq_of_mul_eq_one_right ha⟩
  exact hsec.comp (((MonoidHom.ofInjective
    (first_injective f j t s σ ht hs hf hj hfi htf)).trans
      (MulEquiv.subgroupCongr (first_range f j t s σ ht hs hf hj))).symm.injective)

/-- A subgroup containing the two prescribed images contains the whole extension. -/
theorem lift_mem (hfi : Function.Injective f) (htf : t ∉ f.range)
    (L : Subgroup H) (hjL : ∀ a, j a ∈ L) (hsL : s ∈ L)
    (x : (f.range ⊔ Subgroup.zpowers t : Subgroup G)) :
    lift f j t s σ ht hs hf hj hfi htf x ∈ L := by
  let e := (MonoidHom.ofInjective (first_injective f j t s σ ht hs hf hj hfi htf)).trans
      (MulEquiv.subgroupCongr (first_range f j t s σ ht hs hf hj))
  obtain ⟨z, rfl⟩ := e.surjective x
  change (e.symm (e z)).val.2 ∈ L
  rw [e.symm_apply_apply]
  obtain ⟨a, ha | ha⟩ := z.property
  · rw [ha]
    exact hjL a
  · rw [ha]
    exact L.mul_mem (hjL a) hsL
end InvolutoryExtension
