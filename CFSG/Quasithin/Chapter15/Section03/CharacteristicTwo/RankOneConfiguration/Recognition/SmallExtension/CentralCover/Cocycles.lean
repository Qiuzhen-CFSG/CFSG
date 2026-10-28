module

public import Theory.Representation.FirstCohomologyDuality

/-!
# Detecting central automorphisms in the universal dual cover

The centralizing branch of 15.3.31 reduces to restriction of crossed
homomorphisms to the marked subgroup. We retain cocycles, rather than only
cohomology classes: principal cocycles encode inner central automorphisms too.
The restriction criterion is equivalent to absence of marked fixed vectors in
the universal dual cover when the coefficient module has no global fixed vector.
We also descend cocycles through the actual actor quotient and preserve the
criterion for two summands with the same actor and marking.

Source: Aschbacher--Smith, I.1.5 and 15.3.31, printed pp.408 and 1132.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover

open Representation Representation.OneCohomology

variable {k A H V W : Type*} [Field k] [Group A] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Restriction to the specified subgroup detects the actual cocycle,
including its principal part. -/
def DetectedOn (ρ : Representation k A V) (B : Subgroup A) : Prop :=
  ∀ f : cocycles ρ, (∀ b ∈ B, f.val b = 0) → f = 0

/-- The restriction criterion is exactly the fixed-vector condition on the
universal *dual* cover. It is not a statement about a covering of V itself. -/
theorem detectedOn_iff_universal_fixed (ρ : Representation k A V) (B : Subgroup A)
    (hfixed : fixed ρ = ⊥) :
    DetectedOn ρ B ↔
      ∀ f : cocycles ρ, (∀ b ∈ B, universalAction ρ b f = f) → f = 0 := by
  have hinj := principal_injective hfixed
  constructor
  · intro h f hf
    apply h f
    intro b hb
    have he := hf b hb
    change f + principal ρ (f.val b) = f at he
    apply hinj
    simpa only [map_zero] using add_eq_left.mp he
  · intro h f hf
    apply h f
    intro b hb
    change f + principal ρ (f.val b) = f
    rw [hf b hb, map_zero, add_zero]

private theorem cocycle_one (ρ : Representation k A V) (f : cocycles ρ) :
    f.val 1 = 0 := by
  simpa using (f.property 1 1).symm

/-- A cocycle vanishing on the kernel is constant on the fibres of the
actor map. This is the step needed before forming a quotient action. -/
theorem cocycle_eq_of_quotient_eq (q : H →* A) (ρ : Representation k A V)
    (f : cocycles (ρ.comp q)) (hker : ∀ x ∈ q.ker, f.val x = 0)
    {x y : H} (hxy : q x = q y) : f.val x = f.val y := by
  have hk : x * y⁻¹ ∈ q.ker := by
    simp [MonoidHom.mem_ker, map_mul, map_inv, hxy]
  have he := f.property (x * y⁻¹) y
  simpa only [inv_mul_cancel_right, MonoidHom.comp_apply,
    show q (x * y⁻¹) = 1 from hk, map_one, Module.End.one_apply,
    hker _ hk, add_zero] using he

/-- Descent of a cocycle through a surjective actor map, with the exact
pullback equation retained. -/
theorem exists_descended_cocycle (q : H →* A) (hq : Function.Surjective q)
    (ρ : Representation k A V) (f : cocycles (ρ.comp q))
    (hker : ∀ x ∈ q.ker, f.val x = 0) :
    ∃ g : cocycles ρ, ∀ x, g.val (q x) = f.val x := by
  classical
  let s : A → H := Function.surjInv hq
  have hs : ∀ a, q (s a) = a := Function.rightInverse_surjInv hq
  have hf : ∀ x y, q x = q y → f.val x = f.val y :=
    fun _ _ => cocycle_eq_of_quotient_eq q ρ f hker
  refine ⟨⟨fun a => f.val (s a), ?_⟩, ?_⟩
  · intro a b
    change f.val (s (a * b)) = ρ a (f.val (s b)) + f.val (s a)
    rw [hf (s (a * b)) (s a * s b) (by rw [hs, map_mul, hs, hs])]
    simpa only [MonoidHom.comp_apply, hs] using f.property (s a) (s b)
  · intro x
    exact hf (s (q x)) x (hs _)

/-- The marked image detects every cocycle on the original actor that kills
the actor-map kernel. No assertion of inflation injectivity is assumed. -/
theorem cocycle_eq_zero_of_detected_image (q : H →* A) (hq : Function.Surjective q)
    (ρ : Representation k A V) (B : Subgroup H)
    (hdet : DetectedOn ρ (B.map q)) (f : cocycles (ρ.comp q))
    (hker : ∀ x ∈ q.ker, f.val x = 0) (hB : ∀ b ∈ B, f.val b = 0) : f = 0 := by
  obtain ⟨g, hg⟩ := exists_descended_cocycle q hq ρ f hker
  have hg0 : g = 0 := hdet g (by
    rintro _ ⟨b, hb, rfl⟩
    rw [hg, hB b hb])
  apply Subtype.ext
  funext x
  rw [← hg, hg0]
  rfl

/-- The same marked actor detects a pair of coefficient modules when it
detects each coordinate. This includes the two isomorphic natural summands
in C.1.34(2), without confusing their common marking. -/
theorem detectedOn_prod (ρ : Representation k A V) (σ : Representation k A W)
    (B : Subgroup A) (hρ : DetectedOn ρ B) (hσ : DetectedOn σ B) :
    DetectedOn (ρ.prod σ) B := by
  intro f hf
  let f₁ : cocycles ρ := ⟨fun a => (f.val a).1, fun a b =>
    congrArg Prod.fst (f.property a b)⟩
  let f₂ : cocycles σ := ⟨fun a => (f.val a).2, fun a b =>
    congrArg Prod.snd (f.property a b)⟩
  have h₁ : f₁ = 0 := hρ f₁ (fun b hb => congrArg Prod.fst (hf b hb))
  have h₂ : f₂ = 0 := hσ f₂ (fun b hb => congrArg Prod.snd (hf b hb))
  apply Subtype.ext
  funext a
  exact Prod.ext (congrArg (fun c : cocycles ρ => c.val a) h₁)
    (congrArg (fun c : cocycles σ => c.val a) h₂)

/-- Restriction detection transports through actual equivariant actor and
coefficient isomorphisms; the subgroup marking travels through the same map. -/
theorem detectedOn_transport (ρ : Representation k H V) (σ : Representation k A W)
    (eA : H ≃* A) (eV : V ≃ₗ[k] W)
    (he : ∀ a v, eV (ρ a v) = σ (eA a) (eV v)) (B : Subgroup H)
    (hdet : DetectedOn σ (B.map eA.toMonoidHom)) : DetectedOn ρ B := by
  intro f hf
  let e := cocyclesCongr ρ σ eA eV he
  have hz : e f = 0 := hdet (e f) (by
    rintro _ ⟨b,hb,rfl⟩
    change eV (f.val (eA.symm (eA b))) = 0
    rw [eA.symm_apply_apply,hf b hb,map_zero])
  exact e.injective (hz.trans e.map_zero.symm)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.CentralCover
