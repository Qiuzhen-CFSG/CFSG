module
public import Theory.Representation.BinaryPermutation.SevenParabolic
public import CFSG.Quasithin.Chapter12.Section08.Terminal.Quotients
public import CFSG.Quasithin.Chapter12.Section08.Terminal.ThreeRank
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Intersection
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Normality
public import Theory.Representation.ElementaryPerfectSplit
import Mathlib.Tactic

/-!
# The natural A₇ branch of Lemma 12.8.13(6)

The dotted actor is the literal quotient of H by the kernel of its
conjugation action on U/Z(U). Its faithful action and a normal marked A₇
natural module give an equivariant embedding in S₇. Uniqueness of the
invariant nondegenerate bilinear form identifies the source form with the
restricted coordinate dot product; no extra isometry is assumed.

The consumer retains the actual dotted X and conjugate center, the hat
spaces of E, W and V₂, and the relative quotient X-dot/Z-dot. It transports
[W,X] ≤ E through the defining quotient maps, then applies the single
transvection displacement, complementary-plane and rank calculation.

The inputs htrans and hfixed are precisely the action and fixed-space
identities of 12.8.11(3–4); hiso and hrank are 12.8.11(2,5). The source
orthogonal-space identity and invariant form are kept explicit, as are
the marked model and the independent terminal implication hforce from
point-centralizer three-rank to nontriviality of the dotted conjugate
center. The existing producers are qt-12-08-preliminary (12.8.4–8),
qt-12-08-parabolic (12.8.9–10) and qt-12-08-symplectic (12.8.11–12).
The assembly task qt-12-08-terminal retains hforce and the final application,
with qt-12-08 discharging the preceding section inputs. This is a conditional
model calculation, not an unconditional claim of 12.8.13.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma
12.8.11 and the final A₇ argument of 12.8.13(6), printed pp.854–857;
§B.3 and G.11.2(4).
-/

@[expose] public section
open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open BinaryPermutation.SevenParabolic Representation.BinaryOffender
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The faithful binary action of the literal dotted quotient on U/Z(U). -/
noncomputable def terminalRepresentation (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] :
    Representation (ZMod 2) F.TerminalHdot (Additive F.Uhat) :=
  Representation.elementaryRepresentation (p := 2) (QuotientGroup.kerLift F.terminalHatAction)

theorem terminalRepresentation_injective (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] : Function.Injective F.terminalRepresentation := by
  intro a b h
  apply QuotientGroup.kerLift_injective F.terminalHatAction
  ext v
  exact congrArg Additive.toMul (LinearMap.congr_fun h (Additive.ofMul v))

/-- The action on a quotient representative is the original conjugation action. -/
theorem terminalRepresentation_apply_mk (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (h : F.H) (v : Additive F.Uhat) :
    (F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker h) v).toMul =
      F.terminalHatAction h v.toMul := rfl


/-- Source 12.8.11(1) on the literal quotient: a displacement of a vector in
W-hat by X-dot lies in E-hat. Both quotient maps are the defining ones. -/
theorem terminal_displacement_mem_hatE (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    (hWX : ⁅F.W, F.X g⁆ ≤ F.E g)
    (x : F.TerminalHdot) (hx : x ∈ F.terminalDot (F.X g))
    (w : Additive F.Uhat) (hw : w ∈ Symplectic.hatSpace F F.W) :
    F.terminalRepresentation x w - w ∈ Symplectic.hatSpace F (F.E g) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨u, hu, he⟩ := (show w.toMul ∈ Symplectic.hatImage F F.W from hw)
  have hw' : w = Additive.ofMul (QuotientGroup.mk' (center F.U) u) :=
    (congrArg Additive.ofMul he).symm
  subst w
  let au := F.U.normalizerMonoidHom
    ⟨a, le_normalizer_conjugateSpanBy V F.H a.property⟩
  let y : F.U := au u * u⁻¹
  have hy : (y : G) ∈ F.E g := by
    have hh : ⁅F.X g, F.W⁆ ≤ F.E g := by rwa [commutator_comm]
    exact hh (commutator_mem_commutator ha hu)
  change (F.terminalRepresentation _ _ - _).toMul ∈ Symplectic.hatImage F (F.E g)
  refine ⟨y, hy, ?_⟩
  rw [toMul_sub, F.terminalRepresentation_apply_mk]
  change QuotientGroup.mk' (center F.U) y =
    F.terminalHatAction a (QuotientGroup.mk' (center F.U) u) /
      QuotientGroup.mk' (center F.U) u
  rw [F.terminalHatAction_apply_mk]
  simp only [y, au, map_mul, map_inv, div_eq_mul_inv]

/-- The literal point centralizer in the dotted action. -/
def terminalPointCentralizer (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) : Subgroup F.TerminalHdot where
  carrier := {a | F.terminalRepresentation a v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change F.terminalRepresentation (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    change F.terminalRepresentation a⁻¹ v = v
    have h := congrArg (F.terminalRepresentation a⁻¹) ha
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- The A₇ natural-module branch is incompatible with the actual 12.8.11
identities. The only terminal input is the parent's independent implication
from point-centralizer three-rank to nontriviality of the dotted conjugate
center. In particular neither the A₇ exclusion nor an isometry is assumed. -/
theorem sevenModel_excluded [Finite G] (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (K : Subgroup F.TerminalHdot) [K.Normal]
    (eK : K ≃* alternatingGroup (Fin 7))
    (eV : Additive F.Uhat ≃ₗ[ZMod 2] Space)
    (he : ∀ k : K, ∀ w, eV (F.terminalRepresentation k w) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) (eK k) (eV w))
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (hB : B.Nondegenerate)
    (hBinv : ∀ a, ∀ u w, B (F.terminalRepresentation a u)
      (F.terminalRepresentation a w) = B u w)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : Symplectic.hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hXT : F.X g ≤ (T : Subgroup G))
    (hT : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hiso : ∀ e ∈ Symplectic.hatSpace F (F.E g),
      ∀ w ∈ Symplectic.hatSpace F (F.E g), B e w = 0)
    (htrans : ∀ x ∈ F.terminalDot (F.X g), ∀ e ∈ Symplectic.hatSpace F (F.E g),
      F.terminalRepresentation x e - e ∈ Symplectic.hatSpace F (F.Vi 2))
    (hfixed : Symplectic.hatSpace F (F.E g) ⊓
      fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
        Symplectic.hatSpace F (F.Vi 2))
    (hWX : ⁅F.W, F.X g⁆ ≤ F.E g)
    (hperp : Symplectic.hatSpace F F.W = (B v).ker)
    (hrank : finrank (ZMod 2) (Symplectic.hatSpace F (F.E g)) +
      finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) =
      finrank (ZMod 2) (Additive F.Uhat) - 1)
    (hforce : 1 < primeRank 3 (F.terminalPointCentralizer v) →
      F.terminalDot (conjugate F.ZU g) ≠ ⊥) : False := by
  let E := Symplectic.hatSpace F (F.E g)
  let X := F.terminalDot (F.X g)
  let Z := F.terminalDot (conjugate F.ZU g)
  obtain ⟨f, hf, hfK, hact⟩ := faithful_extension K F.terminalRepresentation
    F.terminalRepresentation_injective eK eV he
  have hAlt : alternatingGroup (Fin 7) ≤ f.range := by
    intro a ha
    obtain ⟨k, hk⟩ := eK.surjective ⟨a, ha⟩
    exact ⟨k, by rw [hfK, hk]⟩
  have hform (u w : Additive F.Uhat) : B u w = pairing (eV u) (eV w) :=
    marked_form_eq K F.terminalRepresentation eK eV he B hB (fun k => hBinv k) u w
  have hv' : eV v ≠ 0 := by intro h; exact hv (eV.injective (h.trans eV.map_zero.symm))
  have hmapFix : (fixedSpace F.terminalRepresentation X).map eV.toLinearMap =
      fixedSpace (action.comp f) X := by
    ext w
    obtain ⟨u, rfl⟩ := eV.surjective w
    rw [Submodule.mem_map_equiv, eV.symm_apply_apply]
    constructor
    · intro hu x
      change action (f x) (eV u) = eV u
      rw [← hact]
      exact congrArg eV (hu x)
    · intro hu x
      apply eV.injective
      change eV (F.terminalRepresentation x u) = eV u
      rw [hact]
      exact hu x
  have hfixed' : E.map eV.toLinearMap ⊓ fixedSpace (action.comp f) X =
      Submodule.span (ZMod 2) {eV v} := by
    have hh := congrArg (fun P : Submodule (ZMod 2) (Additive F.Uhat) => P.map eV.toLinearMap) hfixed
    rw [Submodule.map_inf _ eV.injective, hmapFix, hline, Submodule.map_span,
      Set.image_singleton] at hh
    exact hh
  have hdim := eV.finrank_eq.trans finrank_space
  apply exclude f hf hAlt (F.terminalDot (T : Subgroup G)) X Z
    (map_mono (comap_mono hXT)) (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
    (E.map eV.toLinearMap) (eV v) hv'
  · intro t ht
    rw [← hact, hT t ht]
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
    exact (hform u w).symm.trans (hiso u hu w hw)
  · rintro x hx _ ⟨u, hu, rfl⟩
    change action (f x) (eV u) - eV u ∈ Submodule.span (ZMod 2) {eV v}
    rw [← hact, ← map_sub]
    have h := htrans x hx u hu
    rw [hline] at h
    have hm : eV (F.terminalRepresentation x u - u) ∈
        (Submodule.span (ZMod 2) {v}).map eV.toLinearMap := Submodule.mem_map_of_mem h
    rw [Submodule.map_span, Set.image_singleton] at hm
    exact hm
  · exact hfixed'
  · intro x hx w hw
    obtain ⟨u, rfl⟩ := eV.surjective w
    rw [← hact, ← map_sub]
    apply Submodule.mem_map_of_mem
    apply F.terminal_displacement_mem_hatE g hWX x hx u
    rw [hperp, LinearMap.mem_ker, hform]
    exact hw
  · rw [eV.finrank_map_eq]
    simpa only [hdim] using hrank
  · intro hr
    apply hforce
    have hc : (pointStabilizer (eV v)).comap f = F.terminalPointCentralizer v := by
      ext a
      change action (f a) (eV v) = eV v ↔ F.terminalRepresentation a v = v
      rw [← hact]
      exact eV.injective.eq_iff
    rwa [hc] at hr
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
