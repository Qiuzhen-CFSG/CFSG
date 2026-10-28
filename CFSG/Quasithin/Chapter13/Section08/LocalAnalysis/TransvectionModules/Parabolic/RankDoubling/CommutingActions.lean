module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import Theory.Representation.InvertedCubicTensor
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Two orbit copies from a cubic and an inverting involution

The map `(a,b) ↦ a + r(b)` identifies the module with two copies of the
actual orbit span. The cubic polynomial is checked only on the seed and
propagated through the commuting orbit. Applying the inverting involution
separates the two coordinates; the two seed directions generate the module.
No dimension, tensor decomposition, or direct-sum identity is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the
abbreviated doubling step of 13.8.6, printed p.948. This is its linear
algebra step; applicability to the literal source quotient is separate.
-/

public section

open Module
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
abbrev F := ZMod 2
variable {A X : Type*} [Group A] [AddCommGroup X] [Module F X]

@[expose] def orbitSpan (ρ : Representation F A X) (v : X) : Submodule F X :=
  Submodule.span F (Set.range fun a => ρ a v)

private lemma twice (x : X) : x + x = 0 := by
  simpa only [show (1 : F) + 1 = 0 by decide, zero_smul, one_smul] using
    (add_smul (1 : F) 1 x).symm

variable (ρ : Representation F A X) (σ : Representation F InvertedCubicTensor.S₃ X)
  (v : X)

private def pairMap : (orbitSpan ρ v × orbitSpan ρ v) →ₗ[F] X where
  toFun x := x.1.val + σ InvertedCubicTensor.cubic x.2.val
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' c x := by simp

private theorem polynomial_on_orbit
    (hcomm : ∀ a x, σ InvertedCubicTensor.cubic (ρ a x) =
      ρ a (σ InvertedCubicTensor.cubic x))
    (hseed : σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.cubic v) =
      v + σ InvertedCubicTensor.cubic v) :
    ∀ x ∈ orbitSpan ρ v, σ InvertedCubicTensor.cubic
      (σ InvertedCubicTensor.cubic x) = x + σ InvertedCubicTensor.cubic x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [hcomm, hcomm, hseed, map_add]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]; abel
  | smul c x _ hx => simp only [map_smul, hx, smul_add]

private theorem pairMap_injective
    (hcomm : ∀ a x, σ InvertedCubicTensor.cubic (ρ a x) =
      ρ a (σ InvertedCubicTensor.cubic x))
    (hseed : σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.cubic v) =
      v + σ InvertedCubicTensor.cubic v)
    (hfix : ∀ a, σ InvertedCubicTensor.inverter (ρ a v) = ρ a v) :
    Function.Injective (pairMap ρ σ v) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  rintro ⟨x, y⟩ hxy
  have hfixed : ∀ w ∈ orbitSpan ρ v, σ InvertedCubicTensor.inverter w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨a, rfl⟩ := hw; exact hfix a
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have he : x.val + σ InvertedCubicTensor.cubic y.val = 0 := hxy
  have ht := congrArg (σ InvertedCubicTensor.inverter) he
  rw [map_add, map_zero, hfixed x.val x.property] at ht
  have hinv : σ InvertedCubicTensor.inverter (σ InvertedCubicTensor.cubic y.val) =
      σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.cubic y.val) := by
    calc
      _ = (σ (InvertedCubicTensor.inverter * InvertedCubicTensor.cubic)) y.val := by
        rw [map_mul]; rfl
      _ = σ InvertedCubicTensor.cubic
          (σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.inverter y.val)) := by
        rw [InvertedCubicTensor.inverts_cubic, map_mul, map_mul]; rfl
      _ = _ := by rw [hfixed y.val y.property]
  rw [hinv, polynomial_on_orbit ρ σ v hcomm hseed y.val y.property] at ht
  have hy : y.val = 0 := by
    have : (x.val + σ InvertedCubicTensor.cubic y.val) + y.val = 0 := by
      convert ht using 1
      abel
    rwa [he, zero_add] at this
  have hx : x.val = 0 := by simpa only [hy, map_zero, add_zero] using he
  exact show (x, y) = 0 from Prod.ext (Subtype.ext hx) (Subtype.ext hy)

private theorem pairMap_surjective
    (hcomm : ∀ a x, σ InvertedCubicTensor.cubic (ρ a x) =
      ρ a (σ InvertedCubicTensor.cubic x))
    (hgen : Submodule.span F {x | ∃ a, x = ρ a v ∨
      x = ρ a (σ InvertedCubicTensor.cubic v)} = ⊤) :
    Function.Surjective (pairMap ρ σ v) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro x ⟨a, rfl | rfl⟩
  · exact ⟨(⟨ρ a v, Submodule.subset_span ⟨a, rfl⟩⟩, 0), by
      change ρ a v + σ InvertedCubicTensor.cubic 0 = ρ a v; simp⟩
  · exact ⟨(0, ⟨ρ a v, Submodule.subset_span ⟨a, rfl⟩⟩), by
      change 0 + σ InvertedCubicTensor.cubic (ρ a v) = _; rw [zero_add, hcomm]⟩

/-- The two copies of the actual orbit are separated by the inverting involution.
Only the cubic polynomial on the seed and generation by its two directions are inputs. -/
noncomputable def orbitPairEquiv
    (hcomm : ∀ a x, σ InvertedCubicTensor.cubic (ρ a x) =
      ρ a (σ InvertedCubicTensor.cubic x))
    (hseed : σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.cubic v) =
      v + σ InvertedCubicTensor.cubic v)
    (hfix : ∀ a, σ InvertedCubicTensor.inverter (ρ a v) = ρ a v)
    (hgen : Submodule.span F {x | ∃ a, x = ρ a v ∨
      x = ρ a (σ InvertedCubicTensor.cubic v)} = ⊤) :
    (orbitSpan ρ v × orbitSpan ρ v) ≃ₗ[F] X :=
  LinearEquiv.ofBijective (pairMap ρ σ v)
    ⟨pairMap_injective ρ σ v hcomm hseed hfix, pairMap_surjective ρ σ v hcomm hgen⟩

@[simp] theorem orbitPairEquiv_apply
    (hcomm : ∀ a x, σ InvertedCubicTensor.cubic (ρ a x) =
      ρ a (σ InvertedCubicTensor.cubic x))
    (hseed : σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.cubic v) =
      v + σ InvertedCubicTensor.cubic v)
    (hfix : ∀ a, σ InvertedCubicTensor.inverter (ρ a v) = ρ a v)
    (hgen : Submodule.span F {x | ∃ a, x = ρ a v ∨
      x = ρ a (σ InvertedCubicTensor.cubic v)} = ⊤)
    (a b : orbitSpan ρ v) :
    orbitPairEquiv ρ σ v hcomm hseed hfix hgen (a,b) =
      a.val + σ InvertedCubicTensor.cubic b.val := by rfl

theorem finrank_eq_twice_orbit [FiniteDimensional F X]
    (hcomm : ∀ a x, σ InvertedCubicTensor.cubic (ρ a x) =
      ρ a (σ InvertedCubicTensor.cubic x))
    (hseed : σ InvertedCubicTensor.cubic (σ InvertedCubicTensor.cubic v) =
      v + σ InvertedCubicTensor.cubic v)
    (hfix : ∀ a, σ InvertedCubicTensor.inverter (ρ a v) = ρ a v)
    (hgen : Submodule.span F {x | ∃ a, x = ρ a v ∨
      x = ρ a (σ InvertedCubicTensor.cubic v)} = ⊤) :
    finrank F X = 2 * finrank F (orbitSpan ρ v) := by
  have h := (orbitPairEquiv ρ σ v hcomm hseed hfix hgen).finrank_eq
  rw [Module.finrank_prod] at h
  omega
end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling
