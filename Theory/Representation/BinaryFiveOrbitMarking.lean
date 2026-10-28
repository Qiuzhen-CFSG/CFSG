module
public import Theory.Representation.BinaryFiveOrbitBounds

/-!
# Marked binary modules from a five-point spanning orbit

An index-five Sylow-fixed spanning vector gives a surjective map from the
binary permutation space on five points. If the target has dimension at
least four, the kernel has dimension at most one. Rotation fixes such a
binary kernel pointwise, so a nonzero kernel is exactly the constant line.
The resulting full or deleted permutation marking preserves the original
order-five generator and each of its five orbit vectors.

Source application: the actual quintic local quotient in Aschbacher--Smith
14.2.20--21 and 14.6.12(2), printed pp.988--989 and1031.
-/

public section
namespace BinaryPentagon
open Submodule
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The constant line in the binary permutation space on five points. -/
@[expose] def constantLine : Submodule (ZMod 2) Space where
  carrier := {v | ∀ i, v i = v 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i; simp only [Pi.add_apply,hx i,hy i]
  smul_mem' := by intro a x hx i; simp only [Pi.smul_apply,hx i]

private theorem rotate_injective : Function.Injective rotate := by
  intro x y h
  have h0 := congrFun h 1
  have h1 := congrFun h 2
  have h2 := congrFun h 3
  have h3 := congrFun h 4
  have h4 := congrFun h 0
  ext i
  fin_cases i <;> assumption

private theorem rotate_fixed_iff (v : Space) : rotate v = v ↔ v ∈ constantLine := by
  change rotate v = v ↔ ∀ i, v i = v 0
  constructor
  · intro h
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    have h4 := congrFun h 4
    change v 0 = v 1 at h1
    change v 1 = v 2 at h2
    change v 2 = v 3 at h3
    change v 3 = v 4 at h4
    intro i
    fin_cases i <;> grind
  · intro h
    ext i
    fin_cases i <;> simp [rotate,h]

private theorem constant_nonzero_unique : ∀ v w : Space,
    v ∈ constantLine → w ∈ constantLine → v ≠ 0 → w ≠ 0 → v = w := by
  change ∀ v w : Space, (∀ i, v i = v 0) → (∀ i, w i = w 0) →
    v ≠ 0 → w ≠ 0 → v = w
  decide +kernel

/-- A rotation-invariant kernel of codimension at least four is zero or
the constant line. -/
theorem orbit_kernel_cases [FiniteDimensional (ZMod 2) W]
    (f : Space →ₗ[ZMod 2] W) (hf : Function.Surjective f)
    (hr : ∀ v ∈ f.ker, rotate v ∈ f.ker)
    (hd : 4 ≤ Module.finrank (ZMod 2) W) :
    f.ker = ⊥ ∨ f.ker = constantLine := by
  have hn := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top] at hn
  have hfive : Module.finrank (ZMod 2) Space = 5 := by
    simp [Space]
  rw [hfive] at hn
  have hk : Module.finrank (ZMod 2) f.ker ≤ 1 := by omega
  by_cases hb : f.ker = ⊥
  · exact Or.inl hb
  · right
    have hdim : Module.finrank (ZMod 2) f.ker = 1 := by
      have hnz : Module.finrank (ZMod 2) f.ker ≠ 0 :=
        fun hh => hb (Submodule.finrank_eq_zero.mp hh)
      omega
    have hcard : Nat.card f.ker = 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim,pow_one]
    obtain ⟨u,hu,huniq⟩ := (Nat.card_eq_two_iff' (0 : f.ker)).mp hcard
    have hle : f.ker ≤ constantLine := by
      intro v hv
      by_cases hz : v = 0
      · simpa only [hz] using constantLine.zero_mem
      · have hrz : rotate v ≠ 0 := by
          intro he
          have h0 : rotate (0 : Space) = 0 := by ext i; fin_cases i <;> rfl
          exact hz (rotate_injective (he.trans h0.symm))
        apply (rotate_fixed_iff v).mp
        exact congrArg Subtype.val ((huniq ⟨rotate v,hr v hv⟩
          (fun he => hrz (congrArg Subtype.val he))).trans
            (huniq ⟨v,hv⟩ (fun he => hz (congrArg Subtype.val he))).symm)
    apply le_antisymm hle
    intro v hv
    by_cases hz : v = 0
    · simpa only [hz] using f.ker.zero_mem
    · have hu0 : (u : Space) ≠ 0 := fun he => hu (Subtype.ext he)
      exact constant_nonzero_unique u v (hle u.property) hv hu0 hz ▸ u.property

/-- The actual five-element orbit, with its exact kernel. -/
theorem exists_marked_five_orbit
    {H : Type*} [Group H] [Finite H] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (S : Sylow 2 H) (hi : S.index = 5)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤)
    (hd : 4 ≤ Module.finrank (ZMod 2) W) :
    ∃ (a : H) (f : Space →ₗ[ZMod 2] W), orderOf a = 5 ∧ Function.Surjective f ∧
      (∀ i : Fin 5, f (vertex i) = ρ (a ^ i.val) w) ∧
      (∀ v, f (rotate v) = ρ a (f v)) ∧ (f.ker = ⊥ ∨ f.ker = constantLine) := by
  obtain ⟨a,ha,hcomp⟩ := exists_five_complement S hi
  obtain ⟨f,hf,hv,hr⟩ := exists_five_orbit_map ρ S a ha hcomp w hw hspan
  refine ⟨a,f,ha,hf,hv,hr,orbit_kernel_cases f hf ?_ hd⟩
  intro v hv
  change f (rotate v) = 0
  rw [hr,show f v = 0 from hv,map_zero]

/-- The same orbit vectors mark either the full permutation space or its
quotient by the constant line. Both identifications retain the cyclic action. -/
theorem marked_orbit_equivalence
    {H : Type*} [Group H] [Finite H] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) (S : Sylow 2 H) (hi : S.index = 5)
    (w : W) (hw : ∀ s : S, ρ s w = w)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun h : H => ρ h w)) = ⊤)
    (hd : 4 ≤ Module.finrank (ZMod 2) W) :
    ∃ a : H, orderOf a = 5 ∧
      ((∃ e : Space ≃ₗ[ZMod 2] W,
        (∀ i : Fin 5, e (vertex i) = ρ (a ^ i.val) w) ∧
        (∀ v, e (rotate v) = ρ a (e v))) ∨
      (∃ e : (Space ⧸ constantLine) ≃ₗ[ZMod 2] W,
        (∀ i : Fin 5, e (Submodule.Quotient.mk (vertex i)) = ρ (a ^ i.val) w) ∧
        (∀ v, e (Submodule.Quotient.mk (rotate v)) =
          ρ a (e (Submodule.Quotient.mk v))))) := by
  obtain ⟨a,f,ha,hf,hv,hr,hk⟩ := exists_marked_five_orbit ρ S hi w hw hspan hd
  refine ⟨a,ha,?_⟩
  rcases hk with hk | hk
  · exact Or.inl ⟨LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hk,hf⟩,hv,hr⟩
  · let e : (Space ⧸ constantLine) ≃ₗ[ZMod 2] W :=
      (Submodule.quotEquivOfEq constantLine f.ker hk.symm).trans
        (f.quotKerEquivOfSurjective hf)
    have he (v : Space) : e (Submodule.Quotient.mk v) = f v := rfl
    exact Or.inr ⟨e,fun i => (he _).trans (hv i),fun v => by rw [he,he,hr]⟩

end BinaryPentagon
