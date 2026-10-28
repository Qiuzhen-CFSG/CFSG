module

public import Theory.GroupAction.SylowPointwiseInner
public import Mathlib.GroupTheory.Solvable

/-!
# Solvable fixed groups under Sylow and central-quotient transport

Sylow conjugacy transports a calculation for one pointwise fixed Sylow subgroup
without changing the automorphism's nontriviality. For a perfect central cover,
the induced quotient automorphism has the same order. The fixed subgroup maps
into the quotient fixed subgroup with central kernel, so solvability lifts.
No surjectivity assertion about fixed points is needed.

Source: the elementary transport used in Aschbacher--Smith, E.6.22,
printed p.254 (PDF p.265), for the central covers in E.6.8(1).
-/

public section
open Subgroup
namespace MulAut
variable {G H : Type*} [Group G] [Group H]

/-- An equivariant homomorphism with central kernel lifts fixed-group solvability. -/
theorem fixed_solvable_of_central_kernel (f : G →* H)
    (hk : f.ker ≤ center G) (a : MulAut G) (b : MulAut H)
    (hab : ∀ x, f (a x) = b (f x)) [Group.IsSolvable b.fixedSubgroup] :
    Group.IsSolvable a.fixedSubgroup := by
  let φ : a.fixedSubgroup →* b.fixedSubgroup :=
    (f.comp a.fixedSubgroup.subtype).codRestrict b.fixedSubgroup (by
      intro x
      rw [mem_fixedSubgroup]
      change b (f x) = f x
      rw [← hab, (mem_fixedSubgroup a x).mp x.property])
  have hc (x : φ.ker) : (x.val.val : G) ∈ center G := by
    apply hk
    have hx := congrArg Subtype.val x.property
    exact hx
  let : Group.IsSolvable φ.ker := Group.isSolvable_of_comm (fun x y => by
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_center_iff.mp (hc x) y.val.val).symm)
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by simp)

/-- A fixed-group calculation for one Sylow subgroup applies to every Sylow subgroup. -/
theorem fixed_solvable_of_sylow [Finite G] (P Q : Sylow 2 G)
    (hP : ∀ a : MulAut G, a ≠ 1 → (∀ x ∈ P, a x = x) →
      Group.IsSolvable a.fixedSubgroup)
    (a : MulAut G) (ha : a ≠ 1) (hQ : ∀ x ∈ Q, a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  let e := conj g
  have hm : (P : Subgroup G).map e.toMonoidHom = Q :=
    congrArg Sylow.toSubgroup hg
  let b := congr e.symm a
  have hb : b ≠ 1 := by
    intro h
    exact ha ((congr e.symm).injective (h.trans (map_one _).symm))
  have hfix : ∀ x ∈ P, b x = x := by
    intro x hx
    change e.symm (a (e x)) = x
    have hxQ : e x ∈ Q := by
      change e x ∈ (Q : Subgroup G)
      rw [← hm]
      exact mem_map_of_mem e.toMonoidHom hx
    rw [hQ _ hxQ, e.symm_apply_apply]
  let : Group.IsSolvable b.fixedSubgroup := hP b hb hfix
  exact Group.isSolvable_of_isSolvable_injective
    (f := (fixedSubgroupCongr e.symm a).toMonoidHom)
    (fixedSubgroupCongr e.symm a).injective

/-- For a perfect central cover, solvable Sylow-central involution fixed groups
downstairs give solvable fixed groups upstairs. -/
theorem fixed_solvable_of_centralQuotient [Finite G] [Group.IsPerfect G]
    (e : G ⧸ center G ≃* H)
    (hH : ∀ (S : Sylow 2 H) (b : MulAut H), orderOf b = 2 →
      (∀ x ∈ S, b x = x) → Group.IsSolvable b.fixedSubgroup)
    (S : Sylow 2 G) (a : MulAut G) (ha : orderOf a = 2)
    (hfix : ∀ x ∈ S, a x = x) : Group.IsSolvable a.fixedSubgroup := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center G))
  have hf : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (center G))
  let Q := S.mapSurjective (f := f) hf
  let b := centralQuotientAction e a
  have hb : orderOf b = 2 := (orderOf_centralQuotientAction e a).trans ha
  have hQ : ∀ x ∈ Q, b x = x := by
    rintro x ⟨y, hy, rfl⟩
    change centralQuotientAction e a (e (QuotientGroup.mk' (center G) y)) = _
    rw [centralQuotientAction_apply, hfix y hy]
    rfl
  let : Group.IsSolvable b.fixedSubgroup := hH Q b hb hQ
  refine fixed_solvable_of_central_kernel f ?_ a b ?_
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply e.injective
    exact (show f x = 1 from hx).trans (map_one e).symm
  · intro x
    exact (centralQuotientAction_apply e a x).symm
end MulAut
