module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.SourceSigned

/-!
# Finite equations for global Ree word reduction

The alphabet consists of the sixteen signed root groups, the full Cartan and
D16. Only angular root-pair, torus/root, Weyl/root and two rank-one Gauss
relations are required. The descent equation is derived by conjugating the
literal negative-root Gauss identity. Neither a global model map nor a kernel
hypothesis is part of the data. All parameters include m = 0.
Source: GLS3 2.3.5--8, Table 2.4, and Steinberg, section 11, Lemmas 62--64.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.Global
open Subgroup Theory.GroupTheory OrderedRootPresentation
open SignedGeometry WeylPresentation
open LocalBlockInput.PairRigidity.LocalIndices.SuzukiGaussData
open CentralCovers.OddPrimary.Order

structure Data (m : ℕ) (G : Type*) [Group G] where
  x : ∀ _p : Bool, ∀ i, AngularPresentation.Parameter m i →* G
  h : Parabolics.fixedTorus m →* G
  n : Weyl →* G

namespace Data
variable {m : ℕ} {G : Type*} [Group G] (d : Data m G)

def pair (r : Index) (a : CoefficientField m) : G :=
  d.x r.1 (.inl r.2) (PositiveTables.rootChartEquiv m (.inl r.2) a)
def quartet (r : Index) (a b : CoefficientField m) : G :=
  d.x r.1 (.inr r.2) (PositiveTables.rootChartEquiv m (.inr r.2) (a,b))
def torus (t : TorusParameter m) : G := d.h (fixedTorusEquiv m t)
abbrev reflection (s : Bool) : G := d.n (simple s)
abbrev simpleRoot (s : Bool) := d.x true (SignedCharts.simpleIndex s)

structure Relations : Prop where
  positive : Equations (AngularPresentation.table m) (d.x true)
  torus_root : ∀ t i a, d.h t * d.x true i a * (d.h t)⁻¹ =
    d.x true i (SourceBorel.rootAction t i a)
  weyl_torus : ∀ s t, d.reflection s * d.h t * (d.reflection s)⁻¹ =
    d.h (NormalizerPresentation.action m (simple s) t)
  pair : ∀ s r a, d.reflection s * d.pair r a * (d.reflection s)⁻¹ =
    d.pair (step false s r) a
  quartet : ∀ s r a b, d.reflection s * d.quartet r a b * (d.reflection s)⁻¹ =
    d.quartet (step true s r) a b
  linear_gauss : ∀ a : (CoefficientField m)ˣ,
    d.reflection false * d.pair (false,0) a =
      d.pair (false,0) (a⁻¹ : (CoefficientField m)ˣ) * d.torus (linearTau a) *
        d.pair (true,0) (a⁻¹ : (CoefficientField m)ˣ)
  suzuki_gauss : ∀ a b : CoefficientField m, ∀ hn : norm a b ≠ 0,
    d.reflection true * d.quartet (false,0) a b =
      d.quartet (false,0) (negativeFirst a b) (negativeSecond a b) *
        d.torus (suzukiTau (Units.mk0 (norm a b) hn)) *
          d.quartet (true,0) (positiveFirst a b) (positiveSecond a b)

variable (R : d.Relations)

theorem reflection_sq (s : Bool) : d.reflection s * d.reflection s = 1 := by
  rw [← map_mul]
  have hs : simple s * simple s = 1 := by cases s <;> decide
  rw [hs, map_one]

@[simp] theorem reflection_inv (s : Bool) : (d.reflection s)⁻¹ = d.reflection s :=
  inv_eq_of_mul_eq_one_right (d.reflection_sq s)

include R in
/-- Conjugating Gauss changes its Cartan by the actual simple Weyl action. -/
theorem conjugate_gauss (s : Bool) (u a v c e : G) (t : Parabolics.fixedTorus m)
    (hu : d.reflection s * u * (d.reflection s)⁻¹ = v)
    (ha : d.reflection s * a * (d.reflection s)⁻¹ = c)
    (he : d.reflection s * u = a * d.h t * e) :
    d.reflection s * v * d.reflection s =
      c * d.h (NormalizerPresentation.action m (simple s) t) * d.reflection s * e := by
  have ht := R.weyl_torus s t
  rw [← ht, ← hu, ← ha]
  have hn := d.reflection_sq s
  have h := congrArg (fun z => d.reflection s * z) he
  rw [← mul_assoc, hn, one_mul] at h
  calc
    _ = u := by
      calc
        _ = (d.reflection s * d.reflection s) * u := by group
        _ = u := by rw [hn,one_mul]
    _ = d.reflection s * (a * d.h t * e) := h
    _ = _ := by group

include R in
/-- The nontrivial simple descent has two possibly different root parameters.
In particular the Suzuki coordinates are never treated as an additive pair. -/
theorem simple_exchange (s : Bool) (a : AngularPresentation.Parameter m (SignedCharts.simpleIndex s))
    (ha : a ≠ 1) :
    ∃ b c : AngularPresentation.Parameter m (SignedCharts.simpleIndex s),
    ∃ t : Parabolics.fixedTorus m,
      d.reflection s * d.simpleRoot s a * d.reflection s =
        d.simpleRoot s b * d.h t * d.reflection s * d.simpleRoot s c := by
  obtain ⟨v,rfl⟩ := (PositiveTables.rootChartEquiv m (SignedCharts.simpleIndex s)).surjective a
  cases s
  · change CoefficientField m at v
    have hv : v ≠ 0 := by
      intro hv
      apply ha
      subst v
      apply Subtype.ext
      change (PositiveTables.pair m 0 0 : Model m) = 1
      rw [PositiveTables.pair_zero,coe_one]
    let u : (CoefficientField m)ˣ := Units.mk0 v hv
    refine ⟨PositiveTables.rootChartEquiv m (.inl 0) (u⁻¹ : (CoefficientField m)ˣ),
      PositiveTables.rootChartEquiv m (.inl 0) (u⁻¹ : (CoefficientField m)ˣ),
      NormalizerPresentation.action m (simple false) (fixedTorusEquiv m (linearTau u)), ?_⟩
    exact d.conjugate_gauss R false _ _ _ _ _ _
      (R.pair false (false,0) v) (R.pair false (false,0) (u⁻¹ : (CoefficientField m)ˣ))
      (R.linear_gauss u)
  · change CoefficientField m × CoefficientField m at v
    have hv : v.1 ≠ 0 ∨ v.2 ≠ 0 := by
      by_contra! hv
      apply ha
      apply Subtype.ext
      change (PositiveTables.quartet m 0 v.1 v.2 : Model m) = 1
      rw [hv.1,hv.2,PositiveTables.quartet_zero,coe_one]
    have hn := norm_ne_zero v.1 v.2 hv
    refine ⟨PositiveTables.rootChartEquiv m (.inr 0) (negativeFirst v.1 v.2,negativeSecond v.1 v.2),
      PositiveTables.rootChartEquiv m (.inr 0) (positiveFirst v.1 v.2,positiveSecond v.1 v.2),
      NormalizerPresentation.action m (simple true)
        (fixedTorusEquiv m (suzukiTau (Units.mk0 (norm v.1 v.2) hn))), ?_⟩
    exact d.conjugate_gauss R true _ _ _ _ _ _
      (R.quartet true (false,0) v.1 v.2)
      (R.quartet true (false,0) (negativeFirst v.1 v.2) (negativeSecond v.1 v.2))
      (R.suzuki_gauss v.1 v.2 hn)

end Data
end ReeF4.RootPresentationRecognition.Global
