module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter

/-!
# The standard derived Sylow on binary planes

A two-group acts on a binary plane through a group of order at most two,
since GL₂(2) has order six. Its squares therefore fix the plane. For the
actual derived positive-root Sylow, the squares of C(1)D(1), D(1)F(1), and
E(1)D(1)F(1) force coordinates 2, 5, 6, and 7 to vanish. This puts the
Weyl plane in the span of e₀, e₁, and the scalar identity. The octonion norm
on this space is the linear diagonal coordinate. Norm preservation and
P = [P,X] kill that coordinate, so every octonion product on P is zero.
In the natural quotient, the same square calculation immediately puts the
plane in the image of span(e₀,e₁); its order four gives equality.

These are the standard-coordinate calculations behind Aschbacher–Smith
14.7.55(1), printed p.1066, PDF p.1083, combined manuscript of 1 March 2004.
`SylowTransport` supplies the application to every actual derived Sylow.
Root coordinates use the existing ATLAS port (LICENSES/ATLAS.txt); the
proof uses four symbolic coordinate equalities, not a plane enumeration.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Atlas.G2.Natural
open Atlas.G2.BinaryParabolicPair
open Representation.BinaryOffender
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

private theorem square_fixes_plane {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (P : Submodule (ZMod 2) W) (hcard : Nat.card P = 4)
    (A : Subgroup G) (hA : IsPGroup 2 A)
    (hPA : A ≤ subspaceStabilizer ρ P) (a : A) (v : P) :
    ρ ((a : G) ^ 2) v = v := by
  classical
  let : Finite P := Nat.finite_of_card_ne_zero (by omega)
  have hd : Module.finrank (ZMod 2) P = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
    simpa [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] using hcard
  let b := Module.finBasisOfFinrankEq (ZMod 2) P hd
  let τ : Representation (ZMod 2) A P := (stabilizerRepresentation ρ P).comp (Subgroup.inclusion hPA)
  let φ := (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp τ.asGroupHom
  have h6 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hdiv : orderOf (φ a) ∣ 6 := h6 ▸ orderOf_dvd_natCard (φ a)
  have himg : IsPGroup 2 φ.range := hA.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := himg.exists_orderOf_eq_pow (φ.rangeRestrict a)
  have hn' : orderOf (φ a) = 2 ^ n :=
    (Subgroup.orderOf_coe (φ.rangeRestrict a)).trans hn
  have hnle : n ≤ 1 := by
    by_contra hh
    have hh' : 4 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n)).trans (hn' ▸ hdiv)
    omega
  have hsq : φ a ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by
    rw [hn']
    exact Nat.pow_dvd_pow 2 hnle)
  have hu : τ.asGroupHom (a ^ 2) = 1 := by
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective
    simpa only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_pow, map_one] using hsq
  have ht : τ (a ^ 2) = 1 := congrArg (fun z : (Module.End (ZMod 2) P)ˣ => z.val) hu
  exact congrArg (fun w : P => (w : W)) (LinearMap.congr_fun ht v)

private def s : Model (ZMod 2) := rootC 1 * rootD 1
private def t : Model (ZMod 2) := rootD 1 * rootF 1
private def u : Model (ZMod 2) := rootE 1 * t

private theorem s_mem : s ∈ derivedSylowAmbient := by
  constructor
  · simpa [s, unipotentProduct] using
      unipotentProduct_mem (![0,0,1,1,0,0] : Fin 6 → ZMod 2)
  · rw [commutator_eq_longRootClosure]
    change s ∈ BinaryException.H
    rw [← QuotientGroup.eq_one_iff]
    change BinaryException.projection s = 1
    simp only [s, map_mul, BinaryException.project_C_eq_D,
      BinaryException.project_D_eq_F]
    rw [← map_mul, Atlas.G2.rootF_add]
    rw [show (1 + 1 : ZMod 2) = 0 from rfl, rootF_zero, map_one]

private theorem t_mem : t ∈ derivedSylowAmbient := by
  constructor
  · simpa [t, unipotentProduct] using
      unipotentProduct_mem (![0,0,0,1,0,1] : Fin 6 → ZMod 2)
  · rw [commutator_eq_longRootClosure]
    change t ∈ BinaryException.H
    rw [← QuotientGroup.eq_one_iff]
    change BinaryException.projection t = 1
    simp only [t, map_mul, BinaryException.project_D_eq_F]
    rw [← map_mul, Atlas.G2.rootF_add]
    rw [show (1 + 1 : ZMod 2) = 0 from rfl, rootF_zero, map_one]

private theorem u_mem : u ∈ derivedSylowAmbient := by
  apply derivedSylowAmbient.mul_mem _ t_mem
  constructor
  · simpa [unipotentProduct] using
      unipotentProduct_mem (![0,0,0,0,1,0] : Fin 6 → ZMod 2)
  · rw [commutator_eq_longRootClosure]
    change rootE 1 ∈ BinaryException.H
    rw [← QuotientGroup.eq_one_iff]
    exact BinaryException.project_E 1

private theorem s_square_0 (x : Carrier (ZMod 2)) :
    (s ^ 2).val x 0 = x 0 + x 6 := by
  simp [s, pow_two, rootC, rootD, rootCEquiv, rootDEquiv,
    rootCLinear, rootDLinear, rootCApply, rootDApply, CharTwo.neg_eq]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl, show (5 : ZMod 2) = 1 from rfl,
    sub_eq_add_neg, CharTwo.neg_eq]

private theorem s_square_1 (x : Carrier (ZMod 2)) :
    (s ^ 2).val x 1 = x 1 + x 7 := by
  simp [s, pow_two, rootC, rootD, rootCEquiv, rootDEquiv,
    rootCLinear, rootDLinear, rootCApply, rootDApply, CharTwo.neg_eq]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from rfl, show (4 : ZMod 2) = 0 from rfl,
    sub_eq_add_neg, CharTwo.neg_eq]

private theorem t_square_0 (x : Carrier (ZMod 2)) :
    (t ^ 2).val x 0 = x 0 + x 5 + x 6 := by
  simp [t, pow_two, rootD, rootF, rootDEquiv, rootFEquiv,
    rootDLinear, rootFLinear, rootDApply, rootFApply, CharTwo.neg_eq]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from rfl, show (3 : ZMod 2) = 1 from rfl,
    sub_eq_add_neg, CharTwo.neg_eq]

private theorem u_square_0 (x : Carrier (ZMod 2)) :
    (u ^ 2).val x 0 = x 0 + x 2 + x 3 + x 4 + x 7 := by
  simp [u, t, pow_two, rootE, rootD, rootF, rootEEquiv, rootDEquiv, rootFEquiv,
    rootELinear, rootDLinear, rootFLinear, rootEApply, rootDApply, rootFApply,
    CharTwo.neg_eq]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from rfl,
    sub_eq_add_neg, CharTwo.neg_eq]

private theorem constraints (x : TraceZero (ZMod 2))
    (hs0 : (s ^ 2).val x.val 0 = x.val 0)
    (hs1 : (s ^ 2).val x.val 1 = x.val 1)
    (ht0 : (t ^ 2).val x.val 0 = x.val 0)
    (hu0 : (u ^ 2).val x.val 0 = x.val 0) :
    x.val 2 = 0 ∧ x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0 := by
  rw [s_square_0, add_eq_left] at hs0
  rw [s_square_1, add_eq_left] at hs1
  rw [t_square_0, hs0, add_zero, add_eq_left] at ht0
  have htrace : x.val 3 + x.val 4 = 0 := x.property
  rw [u_square_0, hs1, add_zero] at hu0
  have h2 : x.val 2 = 0 := by
    have he : x.val 0 + x.val 2 = x.val 0 := by
      calc
        _ = x.val 0 + x.val 2 + x.val 3 + x.val 4 := by rw [add_assoc, htrace, add_zero]
        _ = x.val 0 := hu0
    exact add_eq_left.mp he
  exact ⟨h2, ht0, hs0, hs1⟩

open Atlas.G2.LieParabolicSetup
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

private theorem canonical_two : IsPGroup 2 derivedSylowAmbient :=
  unipotent_isTwoGroup.of_injective
    (Subgroup.inclusion (show derivedSylowAmbient ≤ unipotent from inf_le_left))
    (Subgroup.inclusion_injective _)

private theorem weyl_constraints (P : Submodule (ZMod 2) (TraceZero (ZMod 2)))
    (hc : Nat.card P = 4)
    (hP : derivedSylowAmbient ≤ subspaceStabilizer (traceZeroAction (ZMod 2)) P)
    (x : TraceZero (ZMod 2)) (hx : x ∈ P) :
    x.val 2 = 0 ∧ x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0 := by
  have hs := square_fixes_plane _ P hc _ canonical_two hP ⟨s, s_mem⟩ ⟨x, hx⟩
  have ht := square_fixes_plane _ P hc _ canonical_two hP ⟨t, t_mem⟩ ⟨x, hx⟩
  have hu := square_fixes_plane _ P hc _ canonical_two hP ⟨u, u_mem⟩ ⟨x, hx⟩
  exact constraints x (congrArg (fun y => y.val 0) hs)
    (congrArg (fun y => y.val 1) hs) (congrArg (fun y => y.val 0) ht)
    (congrArg (fun y => y.val 0) hu)

private theorem fourth_eq_third (x : TraceZero (ZMod 2)) : x.val 4 = x.val 3 :=
  (by decide : ∀ a b : ZMod 2, a + b = 0 → b = a) _ _ x.property

private theorem norm_eq_third (x : TraceZero (ZMod 2))
    (hx : x.val 2 = 0 ∧ x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0) :
    Atlas.SplitOctonion.norm x.val = x.val 3 := by
  simp only [Atlas.SplitOctonion.norm, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2,
    mul_zero, zero_add, fourth_eq_third]
  exact (by decide : ∀ a : ZMod 2, a * a = a) _

theorem weyl_canonical_zeroProduct
    (P : Submodule (ZMod 2) (TraceZero (ZMod 2))) (hc : Nat.card P = 4)
    (hP : derivedSylowAmbient ≤ subspaceStabilizer (traceZeroAction (ZMod 2)) P)
    (X : Subgroup (Model (ZMod 2)))
    (hcomm : subspaceCommutator (traceZeroAction (ZMod 2)) P X = P) :
    ∀ x ∈ P, ∀ y ∈ P, Atlas.SplitOctonion.mul x.val y.val = 0 := by
  let d : TraceZero (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    (LinearMap.proj 3).comp (TraceZero (ZMod 2)).subtype
  have hd : P ≤ d.ker := by
    rw [← hcomm]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, x, hx, rfl⟩
    have hfx : traceZeroAction (ZMod 2) g x ∈ P := by
      have hm : traceZeroAction (ZMod 2) g x - x ∈ P := by
        rw [← hcomm]
        exact Submodule.subset_span ⟨g, hg, x, hx, rfl⟩
      simpa only [sub_add_cancel] using P.add_mem hm hx
    change (traceZeroAction (ZMod 2) g x).val 3 - x.val 3 = 0
    apply sub_eq_zero.mpr
    rw [← norm_eq_third _ (weyl_constraints P hc hP _ hfx),
      ← norm_eq_third _ (weyl_constraints P hc hP x hx)]
    exact automorphism_norm g x.val
  intro x hx y hy
  have hx3 : x.val 3 = 0 := hd hx
  have hy3 : y.val 3 = 0 := hd hy
  obtain ⟨hx2, hx5, hx6, hx7⟩ := weyl_constraints P hc hP x hx
  obtain ⟨hy2, hy5, hy6, hy7⟩ := weyl_constraints P hc hP y hy
  ext i
  fin_cases i <;> simp [Atlas.SplitOctonion.mul, hx2, hx3, hx5, hx6, hx7,
    hy2, hy3, hy5, hy6, hy7, fourth_eq_third]

private theorem natural_constraints (P : Submodule (ZMod 2) (Space (ZMod 2)))
    (hc : Nat.card P = 4)
    (hP : derivedSylowAmbient ≤ subspaceStabilizer (action (ZMod 2)) P)
    (x : TraceZero (ZMod 2)) (hx : mk (ZMod 2) x ∈ P) :
    x.val 2 = 0 ∧ x.val 5 = 0 ∧ x.val 6 = 0 ∧ x.val 7 = 0 := by
  have hsq (g : derivedSylowAmbient) (i : Fin 8) (hi : i = 0 ∨ i = 1) :
      ((g.val ^ 2).val x.val) i = x.val i := by
    have h := square_fixes_plane _ P hc _ canonical_two hP g ⟨mk (ZMod 2) x, hx⟩
    rw [action_mk] at h
    obtain ⟨r, hr⟩ := (mk_eq_mk_iff (ZMod 2) _ _).mp h
    apply sub_eq_zero.mp
    have he := congrFun hr i
    have hz : (r • (unit : Carrier (ZMod 2))) i = 0 := by
      rcases hi with rfl | rfl <;> simp [unit]
    rw [hz] at he
    exact he.symm
  exact constraints x (hsq ⟨s, s_mem⟩ 0 (Or.inl rfl))
    (hsq ⟨s, s_mem⟩ 1 (Or.inr rfl)) (hsq ⟨t, t_mem⟩ 0 (Or.inl rfl))
    (hsq ⟨u, u_mem⟩ 0 (Or.inl rfl))

theorem natural_canonical_line (P : Submodule (ZMod 2) (Space (ZMod 2)))
    (hc : Nat.card P = 4)
    (hP : derivedSylowAmbient ≤ subspaceStabilizer (action (ZMod 2)) P) :
    naturalMap.line standardLine = P := by
  have hle : P ≤ naturalMap.line standardLine := by
    intro v hv
    obtain ⟨x, rfl⟩ := mk_surjective (ZMod 2) v
    obtain ⟨h2, h5, h6, h7⟩ := natural_constraints P hc hP x hv
    let y := x - x.val 3 • identity (ZMod 2)
    have hy : y.val ∈ standardPlane := by
      rw [mem_standardPlane_iff_coordinates]
      simp [y, identity, unit, h2, h5, h6, h7, fourth_eq_third]
    refine ⟨y, hy, ?_⟩
    change mk (ZMod 2) y = mk (ZMod 2) x
    simp [y]
  have hline : Nat.card (naturalMap.line standardLine).toAddSubgroup = 4 :=
    naturalMap.line_card standardLine
  let : Finite (naturalMap.line standardLine).toAddSubgroup :=
    Nat.finite_of_card_ne_zero (by rw [hline]; decide)
  apply Submodule.toAddSubgroup_injective
  symm
  apply AddSubgroup.eq_of_le_of_card_ge hle
  change Nat.card (naturalMap.line standardLine) ≤ Nat.card P
  rw [naturalMap.line_card, hc]

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.LineMarking
