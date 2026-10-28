module

public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Projection between two literal binary sections

For U≤E≤P, coordinate maps on P/U and P/E induce a surjective binary
linear projection. Compatible actor maps make it intertwining; its kernel
is precisely the original image of E in P/U. The construction uses the
given quotient maps, without a separate module-projection witness.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.73–75, printed pp.1076–1078. The consumer constructs the natural
projection of the canonical H/P action on P/U before recognizing Ru2.
-/

public section

open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G D F W V : Type*} [Group G] [Group D] [Group F]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup V] [Module (ZMod 2) V]

/-- Descend the original coordinates, retaining the actor marking and exact kernel image. -/
theorem exists_projection
    (H K P U E : Subgroup G) (hKH : K ≤ H) (hUE : U ≤ E)
    (qH : H →* D) (qK : K →* F) (hqK : Function.Surjective qK) (r : F →* D)
    (hmark : ∀ k : K, qH ⟨k, hKH k.property⟩ = r (qK k))
    (σ : Representation (ZMod 2) D W) (ρ : Representation (ZMod 2) F V)
    (d : BinaryConjugationSection H P U (σ.comp qH))
    (n : BinaryConjugationSection K P E (ρ.comp qK)) :
    ∃ p : Representation.IntertwiningMap (σ.comp r) ρ,
      Function.Surjective p ∧
      (∀ x : P, p (d.coordinates x).toAdd = (n.coordinates x).toAdd) ∧
      p.toLinearMap.ker = d.imageSpace E := by
  have hker : d.coordinates.ker ≤ n.coordinates.ker := by
    rw [d.kernel_eq, n.kernel_eq]
    exact fun _ hx => hUE hx
  let f : Multiplicative W →* Multiplicative V :=
    d.coordinates.liftOfSurjective d.onto ⟨n.coordinates, hker⟩
  have hf (x : P) : f (d.coordinates x) = n.coordinates x :=
    d.coordinates.liftOfRightInverse_comp_apply _ _ _ x
  let p₀ : W →ₗ[ZMod 2] V := (AddMonoidHom.toMultiplicative.symm f).toZModLinearMap 2
  have hp₀ (x : P) : p₀ (d.coordinates x).toAdd = (n.coordinates x).toAdd := hf x
  have heq (a : F) (w : W) : p₀ (σ (r a) w) = ρ a (p₀ w) := by
    obtain ⟨k, rfl⟩ := hqK a
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd w)
    have hx' : (d.coordinates x).toAdd = w := congrArg Multiplicative.toAdd hx
    rw [← hx', ← hmark]
    change p₀ ((σ.comp qH) ⟨k, hKH k.property⟩ _) = _
    rw [← d.equivariant ⟨k, hKH k.property⟩ x, hp₀, hp₀]
    exact n.equivariant k x
  let p : Representation.IntertwiningMap (σ.comp r) ρ :=
    p₀.intertwiningMap_of_isIntertwiningMap _ _ heq
  refine ⟨p, ?_, hp₀, ?_⟩
  · intro v
    obtain ⟨x, hx⟩ := n.onto (Multiplicative.ofAdd v)
    exact ⟨(d.coordinates x).toAdd, (hp₀ x).trans (congrArg Multiplicative.toAdd hx)⟩
  · ext w
    obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd w)
    have hx' : (d.coordinates x).toAdd = w := congrArg Multiplicative.toAdd hx
    rw [← hx', LinearMap.mem_ker]
    change p₀ (d.coordinates x).toAdd = 0 ↔ _
    rw [hp₀]
    constructor
    · intro hn
      exact (d.mem_imageSpace_iff E _).mpr
        ⟨x, (n.coordinates_eq_one_iff x).mp hn, rfl⟩
    · intro hd
      obtain ⟨y, hy, he⟩ := (d.mem_imageSpace_iff E _).mp hd
      have he' := congrArg p he
      change p (d.coordinates y).toAdd = p (d.coordinates x).toAdd at he'
      rw [show p (d.coordinates y).toAdd = (n.coordinates y).toAdd from hp₀ y,
        show p (d.coordinates x).toAdd = (n.coordinates x).toAdd from hp₀ x] at he'
      exact he'.symm.trans ((n.coordinates_eq_one_iff y).mpr hy)
end Representation.BinaryConjugationSection
