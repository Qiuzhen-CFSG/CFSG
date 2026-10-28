module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.SignedApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialitySource.CoefficientPolarization

/-!
# Triality coefficients forced by the source module equations

The three scalar-line calculations (9.27), in the basis 1, θ, θ² of the
same cubic field, determine the entire trace pairing. The source long
Weyl element gives the other trace pairing. Applying that element to the
short-short commutator, reversing the commutator and separating the two
disjoint long roots determines its unknown highest coefficient (9.30).
Similarly the short Weyl element eliminates the residual field automorphism
in the long-long pairing (9.35).

ModuleStage retains the earlier matrix calculations with unknown f and g;
it does not assume either coefficient normalization or polarization. Its
constructor feeds the existing polarization proof and the fifteen positive
exchanges, including q=2. Constructing the compatible module pinnings, the
three basis calculations, and the torus covariance from 6E(b) remains
necessary; this module does not assert that source reconstruction.

Source: Fong--Seitz, Groups with a (B,N)-Pair of Rank 2, II, printed
pp.219–220, equations (9.27)–(9.35). Right commutators are x⁻¹y⁻¹xy.
-/

@[expose] public noncomputable section
open Triality.Standard Triality.Standard.RootPresentationRecognition
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.PinnedApplication
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
variable (p : RankOnePair σ Y) {n : ℕ} {hn : 0 < n}
  (e : ScalarMarking (binaryParameters n hn) σ)

private theorem comm_aut (φ : MulAut Y) (x y : Y) :
    φ (rightCommutator x y) = rightCommutator (φ x) (φ y) := by
  simp only [rightCommutator, map_mul, map_inv]
private theorem comm_reverse (x y : Y) :
    rightCommutator x y = (rightCommutator y x)⁻¹ := by
  simp only [rightCommutator, mul_inv_rev, inv_inv, mul_assoc]
private theorem long_inv (i : Fin 3) (t : K) : (p.l i t)⁻¹ = p.l i t := by
  change ((p.longOrbit i) (.ofAdd t))⁻¹ = _
  rw [← map_inv, ← ofAdd_neg, CharTwo.neg_eq]
private theorem short_inv (i : Fin 3) (t : F) : (p.s i t)⁻¹ = p.s i t := by
  change ((p.shortOrbit i) (.ofAdd t))⁻¹ = _
  rw [← map_inv, ← ofAdd_neg, CharTwo.neg_eq]
private theorem B_s_two (x : F) : p.dihedral.B (p.s 2 x) = p.s 2 x :=
  p.orthogonalShort x
private theorem A_l_two (x : K) : p.dihedral.A (p.l 2 x) = p.l 2 x :=
  p.orthogonalLong x

private theorem B_l_one (x : K) : p.dihedral.B (p.l 1 x) = p.l 2 x := rfl
private theorem B_l_two (x : K) : p.dihedral.B (p.l 2 x) = p.l 1 x := p.dihedral.B_B _

/-- Weyl symmetry removes the residual field automorphism in (9.35). -/
theorem long_twist_eq_one (τ : K ≃+* K)
    (hinj : Function.Injective (p.longOrbit 2))
    (h : ∀ a b : K, rightCommutator (p.l 1 b) (p.l 0 a) = p.l 2 (b * τ a)) :
    τ = RingEquiv.refl K := by
  have he (a b : K) : b * τ a = a * τ b := by
    have ht := congrArg p.dihedral.A (h a b)
    rw [comm_aut, p.l_one, p.dihedral.A_A, ← p.l_one, A_l_two,
      comm_reverse, h b a, long_inv] at ht
    exact Multiplicative.ofAdd.injective (hinj ht.symm)
  ext a
  simpa using he a 1

/-- The arbitrary highest coefficient in (9.29)(i) is fixed by the same
source Weyl element, using disjointness of the two long roots. -/
theorem short_coefficient (f : F → F → K)
    (hinj : Function.Injective (p.longOrbit 2))
    (hdis : Disjoint (p.longOrbit 1).range (p.longOrbit 2).range)
    (hDE : ∀ a b, Commute (p.s 2 a) (p.l 1 b))
    (hDF : ∀ a b, Commute (p.s 2 a) (p.l 2 b))
    (hEF : ∀ a b, Commute (p.l 1 a) (p.l 2 b))
    (h : ∀ a b, rightCommutator (p.s 1 b) (p.s 0 a) =
      p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) *
        p.l 1 (e.trace (σ a * σ (σ a) * b)) * p.l 2 (f a b))
    (a b : F) : f a b = e.trace (a * σ b * σ (σ b)) := by
  have ht := congrArg p.dihedral.B (h a b)
  rw [comm_aut, p.s_one, p.dihedral.B_B, ← p.s_one, map_mul, map_mul,
    B_s_two, B_l_one, B_l_two,
    comm_reverse, h b a] at ht
  simp only [mul_inv_rev, long_inv, short_inv] at ht
  have hδ : σ b * σ (σ a) + σ (σ b) * σ a =
      σ a * σ (σ b) + σ (σ a) * σ b := by ring
  rw [hδ] at ht
  have he : p.l 1 (f a b) * p.l 2 (e.trace (σ a * σ (σ a) * b)) =
      p.l 1 (e.trace (σ b * σ (σ b) * a)) * p.l 2 (f b a) := by
    apply mul_left_cancel (a := p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b))
    calc
      _ = p.s 2 _ * p.l 2 (e.trace (σ a * σ (σ a) * b)) * p.l 1 (f a b) := by
        rw [(hEF _ _).eq]; group
      _ = _ := ht.symm
      _ = (p.l 2 (f b a) * p.l 1 (e.trace (σ b * σ (σ b) * a))) *
          p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) := by group
      _ = (p.l 1 (e.trace (σ b * σ (σ b) * a)) * p.l 2 (f b a)) *
          p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) := by rw [← (hEF _ _).eq]
      _ = _ := ((hDE _ _).mul_right (hDF _ _)).eq.symm
  have hi1 : Function.Injective (p.longOrbit 1) := by
    intro x y heq
    apply hinj
    exact congrArg p.dihedral.B heq
  let u : (p.longOrbit 1).range × (p.longOrbit 2).range :=
    (⟨p.l 1 (f a b), ⟨_,rfl⟩⟩, ⟨p.l 2 (e.trace (σ a * σ (σ a) * b)), ⟨_,rfl⟩⟩)
  let v : (p.longOrbit 1).range × (p.longOrbit 2).range :=
    (⟨p.l 1 (e.trace (σ b * σ (σ b) * a)), ⟨_,rfl⟩⟩, ⟨p.l 2 (f b a), ⟨_,rfl⟩⟩)
  have hp : u = v := Subgroup.mul_injective_of_disjoint hdis he
  have hc := Multiplicative.ofAdd.injective (hi1 (congrArg (fun z => (z.1 : Y)) hp))
  exact hc.trans (congrArg e.trace (by ring))


omit [CharP F 2] in
private theorem trace_add (x y : F) : e.trace (x+y) = e.trace x + e.trace y := by
  apply Subtype.ext
  simp only [ScalarMarking.trace, map_add, Subfield.coe_add]
  abel

/-- The three scalar lines in (9.27) determine the whole trace pairing (9.28)(i).
The spanning condition is on the actual cubic field over its actual fixed field. -/
theorem lower_from_basis (θ : F)
    (hspan : ∀ x : F, ∃ b₀ b₁ b₂ : K, x = b₀.val + b₁.val*θ + b₂.val*θ^2)
    (hcomm : ∀ a b, Commute (p.s 2 a) (p.l 1 b))
    (hbasis : ∀ (a : F) (b : K) (i : Fin 3),
      rightCommutator (p.s 2 (b.val*θ^i.val)) (p.s 0 a) =
        p.l 1 (e.trace (a*(b.val*θ^i.val)))) :
    ∀ a b, rightCommutator (p.s 2 b) (p.s 0 a) = p.l 1 (e.trace (a*b)) := by
  intro a b
  have hstep (x y : F)
      (hx : rightCommutator (p.s 2 x) (p.s 0 a) = p.l 1 (e.trace (a*x)))
      (hy : rightCommutator (p.s 2 y) (p.s 0 a) = p.l 1 (e.trace (a*y))) :
      rightCommutator (p.s 2 (x+y)) (p.s 0 a) = p.l 1 (e.trace (a*(x+y))) := by
    have hadd : p.s 2 (x+y) = p.s 2 x * p.s 2 y :=
      (p.shortOrbit 2).map_mul (.ofAdd x) (.ofAdd y)
    have hcommutator (u v w : Y) : rightCommutator (u*v) w =
        (v⁻¹*rightCommutator u w*v)*rightCommutator v w := by
      simp only [rightCommutator, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    rw [hadd, hcommutator, hx, hy]
    rw [(hcomm y _).inv_left.eq]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
    rw [mul_add, trace_add]
    exact ((p.longOrbit 1).map_mul _ _).symm
  obtain ⟨b₀,b₁,b₂,rfl⟩ := hspan b
  apply hstep
  · apply hstep
    · simpa using hbasis a b₀ 0
    · simpa using hbasis a b₁ 1
  · simpa using hbasis a b₂ 2

/-- The second trace pairing is the first one transported through the original
long simple Weyl element, without any new root or field marking. -/
theorem upper_from_lower
    (h : ∀ a b, rightCommutator (p.s 2 b) (p.s 0 a) = p.l 1 (e.trace (a*b))) :
    ∀ a b, rightCommutator (p.s 2 b) (p.s 1 a) = p.l 2 (e.trace (a*b)) := by
  intro a b
  have ht := congrArg p.dihedral.B (h a b)
  rw [comm_aut, B_s_two, ← p.s_one, B_l_one] at ht
  exact ht

/-- The earlier module calculations: the three basis pairings (9.27), the
unknown coefficients of (9.29), the possibly twisted natural action before
(9.35), and the torus covariance (9.31). The subsequent coefficient
normalizations and polarization are not fields of this structure. -/
structure ModuleStage where
  θ : F
  spans : ∀ x : F, ∃ b₀ b₁ b₂ : K, x = b₀.val + b₁.val*θ + b₂.val*θ^2
  f : F → F → K
  g : F → K → K
  τ : K ≃+* K
  highest_injective : Function.Injective (p.longOrbit 2)
  short0_long1 : ∀ a b, Commute (p.s 0 a) (p.l 1 b)
  short0_long2 : ∀ a b, Commute (p.s 0 a) (p.l 2 b)
  long0_short1 : ∀ a b, Commute (p.l 0 a) (p.s 1 b)
  long0_short2 : ∀ a b, Commute (p.l 0 a) (p.s 2 b)
  long0_long2 : ∀ a b, Commute (p.l 0 a) (p.l 2 b)
  short1_long1 : ∀ a b, Commute (p.s 1 a) (p.l 1 b)
  short1_long2 : ∀ a b, Commute (p.s 1 a) (p.l 2 b)
  short2_long1 : ∀ a b, Commute (p.s 2 a) (p.l 1 b)
  short2_long2 : ∀ a b, Commute (p.s 2 a) (p.l 2 b)
  long1_long2 : ∀ a b, Commute (p.l 1 a) (p.l 2 b)
  basis_pairing : ∀ (a : F) (b : K) (i : Fin 3),
    rightCommutator (p.s 2 (b.val*θ^i.val)) (p.s 0 a) =
      p.l 1 (e.trace (a*(b.val*θ^i.val)))
  short_short : ∀ a b, rightCommutator (p.s 1 b) (p.s 0 a) =
    p.s 2 (σ a * σ (σ b) + σ (σ a) * σ b) *
      p.l 1 (e.trace (σ a * σ (σ a) * b)) * p.l 2 (f a b)
  mixed : ∀ a b, rightCommutator (p.l 0 b) (p.s 0 a) =
    p.s 1 (a*b.val) * p.s 2 (σ a * σ (σ a) * b.val) *
      p.l 1 (e.norm a * b) * p.l 2 (g a b)
  long_twisted : ∀ a b, rightCommutator (p.l 1 b) (p.l 0 a) = p.l 2 (b * τ a)
  covariance : CoefficientCovariance e g

namespace ModuleStage
variable {p e} (d : ModuleStage p e)
include d

theorem lower : ∀ a b, rightCommutator (p.s 2 b) (p.s 0 a) = p.l 1 (e.trace (a*b)) :=
  lower_from_basis p e d.θ d.spans d.short2_long1 d.basis_pairing

theorem upper : ∀ a b, rightCommutator (p.s 2 b) (p.s 1 a) = p.l 2 (e.trace (a*b)) :=
  upper_from_lower p e d.lower

theorem twist_eq_one : d.τ = RingEquiv.refl K :=
  long_twist_eq_one p d.τ d.highest_injective d.long_twisted

theorem long_long (a b : K) : rightCommutator (p.l 1 b) (p.l 0 a) = p.l 2 (a*b) := by
  rw [d.long_twisted, d.twist_eq_one]
  simp only [RingEquiv.refl_apply, mul_comm]

theorem coefficient (hdis : Disjoint (p.longOrbit 1).range (p.longOrbit 2).range) (a b : F) :
    d.f a b = e.trace (a * σ b * σ (σ b)) :=
  short_coefficient p e d.f d.highest_injective hdis d.short2_long1 d.short2_long2
    d.long1_long2 d.short_short a b

/-- Construct the existing stage with both trace pairings, the f coefficient,
and the untwisted long-long equation proved. -/
def toUnnormalizedStage (hdis : Disjoint (p.longOrbit 1).range (p.longOrbit 2).range) :
    (rawRoots p).UnnormalizedStage e where
  g := d.g
  highest_injective := d.highest_injective
  short0_long1 := d.short0_long1
  short0_long2 := d.short0_long2
  long0_short1 := d.long0_short1
  long0_short2 := d.long0_short2
  long0_long2 := d.long0_long2
  short1_long1 := d.short1_long1
  short1_long2 := d.short1_long2
  short2_long1 := d.short2_long1
  short2_long2 := d.short2_long2
  long1_long2 := d.long1_long2
  lower := d.lower
  upper := d.upper
  short_short a b := by
    change rightCommutator (p.s 1 b) (p.s 0 a) = _
    rw [d.short_short, d.coefficient hdis]
    rfl
  mixed := d.mixed
  long_long := d.long_long
  covariance := d.covariance

variable [Finite F]

/-- All the positive source exchanges follow from the earlier module stage,
uniformly including q=2. -/
theorem relations (hdis : Disjoint (p.longOrbit 1).range (p.longOrbit 2).range) :
    e.SourceRelations (rawRoots p).markedShort p.longOrbit :=
  (d.toUnnormalizedStage hdis).relations

end ModuleStage
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialitySource.PinnedApplication
