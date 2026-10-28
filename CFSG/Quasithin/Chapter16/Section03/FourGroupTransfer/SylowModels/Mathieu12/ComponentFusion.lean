module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.M12Consequences
public import Theory.Mathieu.M12.Properties.AutCover
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Fusion of the perfect component's involutions in M₁₂

The earlier exact automorphism-centralizer table is an explicit input.
Its solvable quaternion branch cannot contain an injected nontrivial perfect
group. Each product branch supplies an inner involution centralizing that
group. Apply the table again to this inner involution: its centralizer must
be C₂ × S₅. Perfectness kills both the C₂ projection and the sign, so every
involution of the supplied group is a square in that centralizer.

Together with `Theory.Mathieu.M12.SylowCenterSquares`, this proves the
component fusion required in Aschbacher–Smith 16.3.4, printed p.1178, from
the exact earlier 16.1.5(4) table. No fusion or Sylow-center premise is assumed.
The exhaustive table remains with its separate source owner.
-/

public section
open Subgroup Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels.Mathieu12
open OtherPreliminaries.Mathieu
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

private theorem perfect_hom_eq_one {H C : Type*} [Group H] [Group C]
    [Group.IsPerfect H] [IsMulCommutative C] (f : H →* C) (x : H) : f x = 1 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact congrArg Subtype.val (Subsingleton.elim (⟨f x, x, rfl⟩ : f.range) 1)

private theorem symmetric_square_check : ∀ x : S5,
    Equiv.Perm.sign x = 1 → x ^ 2 = 1 → ∃ y : S5, y ^ 2 = x := by
  decide +kernel

private theorem product_square {H : Type*} [Group H] [Group.IsPerfect H]
    (f : H →* C2 × S5) (x : H) (hx : x ^ 2 = 1) :
    ∃ y : C2 × S5, y ^ 2 = f x := by
  have hfirst : (f x).1 = 1 := perfect_hom_eq_one ((MonoidHom.fst _ _).comp f) x
  have hsign : Equiv.Perm.sign (f x).2 = 1 := by
    simpa using perfect_hom_eq_one (Equiv.Perm.sign.comp ((MonoidHom.snd C2 S5).comp f)) x
  obtain ⟨y, hy⟩ := symmetric_square_check (f x).2 hsign (by
    simpa using congrArg Prod.snd (congrArg f hx))
  refine ⟨(1, y), ?_⟩
  apply Prod.ext
  · simpa using hfirst.symm
  · exact hy

private theorem product_central_involution {D : Type*} [Group D]
    (r : MulAut M12) (e : r.fixedSubgroup ≃* C2 × D) :
    ∃ c : M12, orderOf c = 2 ∧ ∀ x : r.fixedSubgroup, x.val * c = c * x.val := by
  let a : C2 × D := (Multiplicative.ofAdd 1, 1)
  have ha : orderOf a = 2 := by
    apply orderOf_eq_prime
    · apply Prod.ext
      · change (Multiplicative.ofAdd (1 : ZMod 2)) ^ 2 = 1
        decide +kernel
      · simp [a]
    · intro h
      have h' := congrArg Prod.fst h
      have hn : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide +kernel
      exact hn h'
  refine ⟨e.symm a, (orderOf_coe _).trans ((e.symm.orderOf_eq a).trans ha), ?_⟩
  intro x
  have hc : x * e.symm a = e.symm a * x := by
    apply e.injective
    simp only [map_mul, e.apply_symm_apply]
    apply Prod.ext
    · exact mul_comm _ _
    · simp [a]
  exact congrArg Subtype.val hc

private theorem no_quaternion_embedding {H : Type*} [Group H] [Nontrivial H]
    [Group.IsPerfect H] (r : MulAut M12) (f : H →* r.fixedSubgroup)
    (hf : Function.Injective f) (hq : IsM12QuaternionExtension r.fixedSubgroup) : False := by
  let : Group.IsSolvable r.fixedSubgroup := quaternionExtension_solvable hq
  exact Group.IsPerfect.not_isSolvable H (Group.isSolvable_of_isSolvable_injective hf)

/-- Under the earlier exact table, involutions in any nontrivial perfect
subgroup of an involutory fixed subgroup are squares in the full M₁₂. -/
theorem fixed_perfect_involution_square
    (table : ∀ r : MulAut M12, orderOf r = 2 → M12InvolutionAlternative r)
    {H : Type*} [Group H] [Nontrivial H] [Group.IsPerfect H]
    (r : MulAut M12) (hr : orderOf r = 2)
    (f : H →* r.fixedSubgroup) (hf : Function.Injective f)
    (x : H) (hx : orderOf x = 2) : ∃ y : M12, y ^ 2 = (f x : M12) := by
  have hprod : Nonempty (r.fixedSubgroup ≃* C2 × S5) ∨
      Nonempty (r.fixedSubgroup ≃* C2 × A5) := by
    rcases table r hr with ⟨_, hq | hp⟩ | ⟨_, hp⟩
    · exact (no_quaternion_embedding r f hf hq).elim
    · exact Or.inl hp
    · exact Or.inr hp
  obtain ⟨c, hc, hcomm⟩ : ∃ c : M12, orderOf c = 2 ∧
      ∀ x : r.fixedSubgroup, x.val * c = c * x.val := by
    rcases hprod with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ <;> exact product_central_involution r e
  let b := MulAut.conj c
  have hb : orderOf b = 2 :=
    (orderOf_injective MulAut.conj
      (Theory.GroupTheory.conj_injective_of_center_eq_bot m12_center_eq_bot) c).trans hc
  let g : H →* b.fixedSubgroup :=
    (r.fixedSubgroup.subtype.comp f).codRestrict b.fixedSubgroup (by
      intro a
      rw [MulAut.mem_fixedSubgroup]
      change c * (f a : M12) * c⁻¹ = (f a : M12)
      rw [← hcomm (f a), mul_inv_cancel_right])
  have hg : Function.Injective g := by
    intro a d h
    exact hf (Subtype.ext (congrArg (fun t : b.fixedSubgroup => (t : M12)) h))
  have he : Nonempty (b.fixedSubgroup ≃* C2 × S5) := by
    rcases table b hb with ⟨_, hq | hp⟩ | ⟨hn, _⟩
    · exact (no_quaternion_embedding b g hg hq).elim
    · exact hp
    · exact (hn ⟨c, rfl⟩).elim
  obtain ⟨e⟩ := he
  obtain ⟨y, hy⟩ := product_square (e.toMonoidHom.comp g) x
    (by simpa only [hx] using pow_orderOf_eq_one x)
  refine ⟨e.symm y, ?_⟩
  have heq : (e.symm y) ^ 2 = g x := by
    apply e.injective
    simpa using hy
  exact congrArg Subtype.val heq
end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels.Mathieu12
