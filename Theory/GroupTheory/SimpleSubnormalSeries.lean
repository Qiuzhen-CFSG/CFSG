module

public import Theory.GroupTheory.SimpleSectionNormalAlternative
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Simple subnormal quotients along a relative normal series

A simple quotient of a subnormal subgroup is detected in a factor of any
finite relative normal series. At each step, intersect with the lower term
and map to the simple quotient. This normal image is either the whole group,
allowing descent to the lower term, or trivial, allowing descent to the
actual quotient factor. Subnormality survives both operations.

The one-step proof refines `Subgroup.simple_section_normal_or_quotient` by
retaining subnormality. Induction over the actual subgroup series gives an
exclusion theorem with no finiteness or composition-series assumption.

Source: the elementary normal-series argument used in Aschbacher–Smith,
2.3.9(7), printed p.526, for the local sporadic block calculation.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G T : Type*} [Group G] [Group T] [IsSimpleGroup T]

/-- A simple subnormal section comes from the normal subgroup or its quotient,
with subnormality retained in the chosen ambient group. -/
theorem simple_subnormal_section_normal_or_quotient
    (N : Subgroup G) [N.Normal] (U : Subgroup G) (hU : U.IsSubnormal)
    (f : U →* T) (hf : Function.Surjective f) :
    (∃ W : Subgroup N, W.IsSubnormal ∧ ∃ g : W →* T, Function.Surjective g) ∨
      ∃ W : Subgroup (G ⧸ N), W.IsSubnormal ∧ ∃ g : W →* T,
        Function.Surjective g := by
  let P := N.subgroupOf U
  have hnormal : (P.map f).Normal := Subgroup.Normal.map inferInstance f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P.map f) hnormal with hbot | htop
  · right
    let q := QuotientGroup.mk' N
    let W := U.map q
    let qU : U →* W := q.subgroupMap U
    have hqU : Function.Surjective qU := q.subgroupMap_surjective U
    have hker : qU.ker ≤ f.ker := by
      intro x hx
      have hxN : (x : G) ∈ N := by
        have hqx : q (x : G) = 1 := congrArg Subtype.val hx
        exact (QuotientGroup.eq_one_iff _).mp hqx
      have hfx : f x ∈ P.map f := Subgroup.mem_map_of_mem f hxN
      exact Subgroup.mem_bot.mp (hbot ▸ hfx)
    let g : W →* T := qU.liftOfSurjective hqU ⟨f, hker⟩
    refine ⟨W, hU.quotient, g, ?_⟩
    intro t
    obtain ⟨x, rfl⟩ := hf t
    exact ⟨qU x, by simp [g]⟩
  · left
    let W := U.subgroupOf N
    let g : W →* T := {
      toFun := fun x => f ⟨x.1.1, x.2⟩
      map_one' := f.map_one
      map_mul' := fun x y => by
        change f ((⟨x.1.1, x.2⟩ : U) * ⟨y.1.1, y.2⟩) = _
        exact f.map_mul _ _ }
    refine ⟨W, hU.subgroupOf, g, ?_⟩
    intro t
    have ht : t ∈ P.map f := htop ▸ mem_top t
    obtain ⟨x, hx, hfx⟩ := ht
    exact ⟨⟨⟨x.1, hx⟩, x.2⟩, hfx⟩

/-- If no factor of a relative normal series has the given simple group as a
quotient of a subnormal subgroup, neither does the ambient group. -/
theorem no_simple_subnormal_quotient_of_series
    {n : ℕ} (term : Fin (n + 1) → Subgroup G)
    (first : term 0 = ⊥) (last : term (Fin.last n) = ⊤)
    (ascending : ∀ i : Fin n, term i.castSucc ≤ term i.succ)
    (normal : ∀ i : Fin n, ((term i.castSucc).subgroupOf (term i.succ)).Normal)
    (exclude : ∀ i : Fin n, let := normal i
      ∀ U : Subgroup (term i.succ ⧸ (term i.castSucc).subgroupOf (term i.succ)),
        U.IsSubnormal → ∀ f : U →* T, ¬ Function.Surjective f)
    (B : Subgroup G) (hB : B.IsSubnormal) (f : B →* T) : ¬ Function.Surjective f := by
  have hterm : ∀ i : Fin (n + 1), ∀ U : Subgroup (term i),
      U.IsSubnormal → ∀ g : U →* T, ¬ Function.Surjective g := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro U _ g hg
      have : Subsingleton (term 0) := by rw [first]; infer_instance
      have : Subsingleton T := hg.subsingleton
      exact not_subsingleton T inferInstance
    | succ i ih =>
      intro U hU g hg
      let := normal i
      rcases simple_subnormal_section_normal_or_quotient
          ((term i.castSucc).subgroupOf (term i.succ)) U hU g hg with
        ⟨W, hW, k, hk⟩ | ⟨W, hW, k, hk⟩
      · let e := subgroupOfEquivOfLe (ascending i)
        exact ih (W.map e.toMonoidHom) (hW.map e.surjective)
          (k.comp (e.subgroupMap W).symm.toMonoidHom)
          (hk.comp (e.subgroupMap W).symm.surjective)
      · exact exclude i W hW k hk
  have hend := hterm (Fin.last n)
  rw [last] at hend
  let e : G ≃* (⊤ : Subgroup G) := Subgroup.topEquiv.symm
  intro hf
  exact hend (B.map e.toMonoidHom) (hB.map e.surjective)
    (f.comp (e.subgroupMap B).symm.toMonoidHom)
    (hf.comp (e.subgroupMap B).symm.surjective)
end Theory.GroupTheory

end
