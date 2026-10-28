module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus.Marked
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.DualNatural

/-!
# The fixed-centralizer bound for the original cubic torus

DualNatural places C_U(Q_H) inside U₀ using the source commutator identity.
The central point V₁ lies in C_U(Q_H), so U₀=V₁ identifies the actual
U-centralizer quotient with the original natural quotient. The diagonal
cubic has no nonzero fixed vector there. Its displacement is surjective,
and contragredience transports this property through the source pairing
to Q_H/C_{Q_H}(U). Hence a Q_H-element centralizing the actual torus
centralizes U.

The section-centralizer input is earlier 14.5.15(4); SourceDuality and the
commutator identity are 14.5.21(1–2), owned by qt-14-05-terminal-duality.
U₀=V₁ is supplied by the preceding 14.7.72 generation branch. The enclosing
source assembly retains their discharge.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.5.21, printed pp.1019–1020, and 14.7.72, printed p.1076.
-/

public section
noncomputable section
open Subgroup Representation Matrix.SpecialLinearGroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
open Chapter12.Section08 CriticalFusion.Source
open CriticalFusion.Source.Rechoice.LocalGeometry.Preparation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

private theorem diag_no_fixed (a : SL2FourNatural.F) (ha : a ≠ 0) (ha1 : a ≠ 1)
    (v : SL2FourNatural.V) (hv : SL2FourNatural.action (diag2 a ha) v = v) : v = 0 := by
  have h0 : a * v 0 = v 0 := by
    simpa [SL2FourNatural.action_apply, diag2_coe', Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using congrFun hv 0
  have h1 : a⁻¹ * v 1 = v 1 := by
    simpa [SL2FourNatural.action_apply, diag2_coe', Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] using congrFun hv 1
  have hz0 : v 0 = 0 := by
    have h : (a - 1) * v 0 = 0 := by rw [sub_mul, one_mul, h0, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr ha1)
  have hz1 : v 1 = 0 := by
    have h : (a⁻¹ - 1) * v 1 = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (inv_ne_one.mpr ha1))
  funext i
  fin_cases i <;> assumption

include d in
private theorem point_le_uKernel :
    F.Vi 1 ≤ F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) := by
  refine le_inf d.conjugationSection.kernel_le ?_
  rw [d.point]
  apply zpowers_le.mpr
  intro q hq
  exact ((show q ∈ centralizer ({d.z} : Set G) from
    d.centralizer_eq ▸ pCoreIn_le 2 F.H hq) d.z (Set.mem_singleton d.z)).symm

open scoped commutatorElement
variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

private theorem exists_natural_iso (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (hU0 : d.U₀ = F.Vi 1) :
    ∃ p : s.uAction.IntertwiningMap (d.naturalQuotient.action.comp d.qH),
      Function.Bijective p := by
  obtain ⟨p, hp, hcoord⟩ :=
    Rechoice.Goldschmidt.LeftChiefFactors.exists_natural_projection d hc s hcomm
  refine ⟨p, ?_, hp⟩
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  obtain ⟨v, hv⟩ := s.uSection.onto (Multiplicative.ofAdd x)
  have hpv : p (s.uSection.coordinates v).toAdd = 0 := by rw [hv]; exact hx
  rw [hcoord] at hpv
  have hmem : (v : G) ∈ F.Vi 1 := hU0 ▸ (d.mem_U₀ v).mpr hpv
  have hz := (s.uSection.coordinates_eq_one_iff v).mpr (point_le_uKernel d hmem)
  rw [hv] at hz
  exact congrArg Multiplicative.toAdd hz

private theorem dual_fixed_zero
    {D A B : Type*} [Group D] [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    [AddCommGroup B] [Module (ZMod 2) B]
    (r : Representation (ZMod 2) D A) (q : Representation (ZMod 2) D B)
    (e : q.Equiv r.dual) (g : D)
    (hg : ∀ x, r g x = x → x = 0) (y : B) (hy : q g y = y) : y = 0 := by
  have hi : Function.Injective ((r g - LinearMap.id) : A →ₗ[ZMod 2] A) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    exact hg x (sub_eq_zero.mp hx)
  have hs : Function.Surjective ((r g - LinearMap.id) : A →ₗ[ZMod 2] A) := Finite.surjective_of_injective hi
  have he : r.dual g (e y) = e y := by
    exact (LinearMap.congr_fun (e.isIntertwining' g) y).symm.trans (congrArg e hy)
  have he0 : e y = 0 := by
    ext x
    obtain ⟨v, rfl⟩ := hs x
    change e y (r g v - v) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    have hh := congrArg (fun f : Module.Dual (ZMod 2) A => f (r g v)) he
    change e y (r g⁻¹ (r g v)) = e y (r g v) at hh
    have hc : r g⁻¹ (r g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hc] at hh
    exact hh.symm
  exact e.toLinearEquiv.injective (he0.trans e.toLinearEquiv.map_zero.symm)

/-- The cubic fixes only C_H(U) in the original Q_H. The supplied duality
uses the actual centralizer quotients and their original H-actions. -/
theorem MarkedTorus.fixed_le (t : MarkedTorus d) (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (hU0 : d.U₀ = F.Vi 1) :
    F.H.pCoreIn 2 ⊓ centralizer (t.torus : Set G) ≤
      F.H ⊓ centralizer (F.U : Set G) := by
  let : Finite X := Finite.of_surjective
    (fun v : F.U => (s.uSection.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.uSection.onto)
  obtain ⟨p, hp⟩ := exists_natural_iso d hc s hcomm hU0
  have hfix : ∀ x, s.uAction t.generator x = x → x = 0 := by
    intro x hx
    have he : SL2FourNatural.action (diag2 t.scalar t.scalar_ne_zero) (p x) = p x := by
      have hh := LinearMap.congr_fun (p.isIntertwining' t.generator) x
      change p (s.uAction t.generator x) = d.naturalQuotient.action (d.qH t.generator) (p x) at hh
      rw [hx] at hh
      rw [t.image] at hh
      exact (d.naturalQuotient.restriction _ _).symm.trans hh.symm
    have hz := diag_no_fixed t.scalar t.scalar_ne_zero t.scalar_ne_one (p x) he
    exact hp.1 (hz.trans p.toLinearMap.map_zero.symm)
  intro q hq
  let x : F.H.pCoreIn 2 := ⟨q, hq.1⟩
  have hcommute : (t.generator : G) * q = q * (t.generator : G) :=
    hq.2 t.generator (mem_zpowers _)
  have hxfix : s.qAction t.generator (s.qSection.coordinates x).toAdd =
      (s.qSection.coordinates x).toAdd := by
    rw [← s.qSection.equivariant]
    congr 2
    apply Subtype.ext
    change (t.generator : G) * q * (t.generator : G)⁻¹ = q
    rw [hcommute, mul_inv_cancel_right]
  have hx0 := dual_fixed_zero s.uAction s.qAction s.duality t.generator hfix
    (s.qSection.coordinates x).toAdd hxfix
  have hx1 : s.qSection.coordinates x = 1 := Multiplicative.toAdd.injective hx0
  exact ⟨pCoreIn_le 2 F.H hq.1, ((s.qSection.coordinates_eq_one_iff x).mp hx1).2⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SteinbergRecognition.CoreIdentification.SourceInvolution.CubicTorus
