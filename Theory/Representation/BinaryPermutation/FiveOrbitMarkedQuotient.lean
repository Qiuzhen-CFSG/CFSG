module

public import Theory.Representation.BinaryPermutation.FiveOrbitMarking
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.GroupAction.FaithfulSixteen
public import Theory.GroupTheory.AlternatingFiveActionAlignment

/-!
# A five-orbit marked by the original alternating quotient

The supplied action on an elementary sixteen has image order divisible by
five, hence is irreducible. Its actual five-element orbit gives five-point
core coordinates. Exact kernel equality aligns their permutation action
with the original surjection onto A₅ by one coordinate permutation. The
resulting multiplicative marking is equivariant for that same original map.
No arbitrary degree-four module classification is used.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace BinaryPermutation
variable {L U : Type*} [Group L] [Group U] [Finite U] [IsElementaryAbelian 2 U]

/-- An actual five-orbit on an elementary sixteen gives core coordinates
equivariant for the prescribed A₅ quotient, with no change of quotient map. -/
theorem core_marking_of_five_orbit_and_prescribed_quotient
    (ρ : L →* MulAut U) (π : L →* alternatingGroup (Fin 5))
    (hπ : Function.Surjective π) (hker : ρ.ker = π.ker)
    (hU : Nat.card U = 16) (hfive : 5 ∣ Nat.card ρ.range)
    (u : U) (hu : u ≠ 1) (horbit : (Set.range (fun l : L => ρ l u)).ncard = 5) :
    ∃ c : Multiplicative (core (Fin 5)) ≃* U, ∀ l v,
      c (Multiplicative.ofAdd (coreRepresentation (Fin 5) (π l).val v.toAdd)) =
        ρ l (c v) := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let τ := elementaryRepresentation (p := 2) ρ
  have hτker : τ.ker = ρ.ker := by
    ext l
    change τ l = 1 ↔ ρ l = 1
    constructor
    · intro hl
      apply MulEquiv.ext
      intro x
      exact congrArg Additive.toMul
        (congrArg (fun f : Module.End (ZMod 2) (Additive U) => f (Additive.ofMul x)) hl)
    · intro hl
      apply LinearMap.ext
      intro x
      change Additive.ofMul (ρ l x.toMul) = x
      rw [hl]
      rfl
  let : τ.IsIrreducible := by
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨⟨⟨⊥, ⊤, ?_⟩⟩, ?_⟩
    · intro h
      have hx : Additive.ofMul u ∈ (⊥ : Subrepresentation τ) :=
        h ▸ (show Additive.ofMul u ∈ (⊤ : Subrepresentation τ) from trivial)
      exact hu (congrArg Additive.toMul hx)
    intro N
    let D : Subgroup U := N.toSubmodule.toAddSubgroup.toSubgroup'
    have hD (l : L) (x : U) : x ∈ D ↔ ρ l x ∈ D := by
      constructor
      · intro hx
        exact N.apply_mem_toSubmodule l hx
      · intro hx
        have hh := N.apply_mem_toSubmodule l⁻¹ hx
        change ρ l⁻¹ (ρ l x) ∈ D at hh
        simpa only [map_inv,MulAut.inv_apply,MulEquiv.symm_apply_apply] using hh
    rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five ρ hfive hU D hD with hb | ht
    · left
      apply bot_unique
      intro x hx
      have hh : x.toMul ∈ D := hx
      rw [hb,mem_bot] at hh
      exact hh
    · right
      apply top_unique
      intro x _
      have hx : x.toMul ∈ D := ht ▸ mem_top _
      exact hx
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U)
    change Nat.card U = _ at hh
    have hp : 2 ^ Module.finrank (ZMod 2) (Additive U) = 2^4 := by
      simpa only [Nat.card_zmod,hU,show (2:ℕ)^4 = 16 from rfl] using hh.symm
    exact Nat.pow_right_injective (by decide : 1 < 2) hp
  have hτorbit : (Set.range (fun l : L => τ l (Additive.ofMul u))).ncard = 5 := by
    have he : Set.range (fun l : L => τ l (Additive.ofMul u)) =
        Additive.ofMul '' Set.range (fun l : L => ρ l u) := by
      ext x
      constructor
      · rintro ⟨l,rfl⟩
        exact ⟨ρ l u,⟨l,rfl⟩,rfl⟩
      · rintro ⟨x,⟨l,rfl⟩,rfl⟩
        exact ⟨l,rfl⟩
    rw [he,Set.ncard_image_of_injective _ Additive.ofMul.injective]
    exact horbit
  have hune : Additive.ofMul u ≠ 0 := fun hz => hu (congrArg Additive.toMul hz)
  obtain ⟨α,c,hα,_,hc⟩ :=
    core_marking_of_irreducible_five_orbit τ hd (Additive.ofMul u) hune hτorbit
  obtain ⟨p,hp⟩ := Theory.GroupTheory.exists_conjugating_perm_of_same_alternating_five_kernel
    α π hπ (hα.trans (hτker.trans hker))
  let P : core (Fin 5) ≃ₗ[ZMod 2] core (Fin 5) :=
    LinearEquiv.ofBijective (coreRepresentation (Fin 5) p)
      ((coreRepresentation (Fin 5)).apply_bijective p)
  let c' := P.trans c
  have he (l : L) (v : core (Fin 5)) :
      c' (coreRepresentation (Fin 5) (π l).val v) = τ l (c' v) := by
    change c (coreRepresentation (Fin 5) p (coreRepresentation (Fin 5) (π l).val v)) =
      τ l (c (coreRepresentation (Fin 5) p v))
    rw [←hc,hp]
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right]
  refine ⟨c'.toAddEquiv.toMultiplicativeLeft,?_⟩
  intro l v
  exact congrArg Additive.toMul (he l v.toAdd)

end BinaryPermutation
