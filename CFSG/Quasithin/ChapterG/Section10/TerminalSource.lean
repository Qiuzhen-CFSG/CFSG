module
public import CFSG.Quasithin.ChapterG.Section10.TwoCore
public import CFSG.Quasithin.Chapter12.Section08.Terminal.SevenModel
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.Assembly
public import Theory.GroupAction.BinaryTransvectionImage
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# G.10 on the literal central quotient of Chapter 12

This is the source substitution Hdot, Uhat, V₂hat, Ehat, Xdot, Z(U)^g-dot
in 12.8.12(1) and 14.3.11. The marked action is terminalRepresentation,
and the smaller actor is the subgroupOf of the actual conjugate-center image.
The source stabilizer product from 12.8.9(6), together with the kernel E,
proves the fixed-space bound. The commutator inclusion proves displacement;
the fixed-space and centered-displacement identities prove full transvections.

Earlier inputs are 12.8.8's form and orbit generation, 12.8.9's action kernel
and outside-W stabilizer, and 12.8.11's isotropic, fixed-space and rank identities.
Their existing producers are Preliminary, Parabolic.Actions.Assembly,
and Symplectic.Transvections. The original section assembly retains their
final discharge. No G.10 conclusion occurs among these inputs.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem elementary_rank_eq_finrank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hcard : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hcard]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))

omit [Finite G] in
/-- Source 12.8.9(6) supplies G.10.1(d) through the original quotient map. -/
theorem terminal_fixed_bound (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    (hker : ∀ e ∈ F.E g, ∀ he : e ∈ F.H, (⟨e, he⟩ : F.H) ∈ F.terminalHatAction.ker)
    (hstab : ∀ u : F.U, (u : G) ∉ F.W →
      (F.xHatStabilizer g hg (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
        (conjugate F.ZU g : Set G) * (F.E g : Set G))
    (x : F.terminalDot (F.X g))
    (hx : x ∉ (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))
    (u : Additive F.Uhat) (hfix : F.terminalRepresentation x u = u) :
    u ∈ hatSpace F F.W := by
  obtain ⟨a, ha, he⟩ := x.property
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (center F.U) u.toMul
  by_contra hn
  have hbW : (b : G) ∉ F.W := by
    intro hm
    exact hn (show u.toMul ∈ hatImage F F.W from ⟨b, hm, hb⟩)
  have hfixb : F.xHatAction g hg ⟨a, ha⟩ (QuotientGroup.mk' (center F.U) b) =
      QuotientGroup.mk' (center F.U) b := by
    have hh := congrArg Additive.toMul hfix
    rw [← he, F.terminalRepresentation_apply_mk, ← hb] at hh
    exact hh
  have hmem := (F.mem_xHatStabilizer g hg _ a).mpr ⟨ha, hfixb⟩
  obtain ⟨z, hz, e, heE, hze⟩ := hstab b hbW hmem
  have hzH : z ∈ F.H := F.X_le_H g hg (F.conjugate_ZU_le_X g hz)
  have heH : e ∈ F.H := F.X_le_H g hg (show e ∈ F.X g from heE.2)
  apply hx
  change (x : F.TerminalHdot) ∈ F.terminalDot (conjugate F.ZU g)
  refine ⟨⟨z, hzH⟩, hz, ?_⟩
  have hq : QuotientGroup.mk' F.terminalHatAction.ker (⟨e, heH⟩ : F.H) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (hker e heE heH)
  have haeq : a = (⟨z, hzH⟩ : F.H) * ⟨e, heH⟩ := Subtype.ext hze.symm
  rw [← he, haeq, map_mul, hq, mul_one]

/-- The actual Chapter12 source data constructs G.10.1 and immediately gives
G.10.2--3 for Hdot and every literal invariant submodule of Uhat. -/
theorem terminal_g10_hypothesis (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : B.Nondegenerate) (hBa : B.IsAlt)
    (hBinv : ∀ a u w, B (F.terminalRepresentation a u) (F.terminalRepresentation a w) = B u w)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hvE : v ∈ hatSpace F (F.E g))
    (hspan : Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot, F.terminalRepresentation a v = w} = ⊤)
    (hT : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hiso : ∀ e ∈ hatSpace F (F.E g), ∀ w ∈ hatSpace F (F.E g), B e w = 0)
    (htrans : ∀ x ∈ F.terminalDot (F.X g), ∀ e ∈ hatSpace F (F.E g),
      F.terminalRepresentation x e - e ∈ hatSpace F (F.Vi 2))
    (hfixed : hatSpace F (F.E g) ⊓ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      hatSpace F (F.Vi 2))
    (hWX : ⁅F.W, F.X g⁆ ≤ F.E g)
    (hperp : hatSpace F F.W = (B v).ker)
    (hrank : finrank (ZMod 2) (hatSpace F (F.E g)) +
      finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) =
      finrank (ZMod 2) (Additive F.Uhat) - 1)
    (hker : ∀ e ∈ F.E g, ∀ he : e ∈ F.H, (⟨e, he⟩ : F.H) ∈ F.terminalHatAction.ker)
    (hstab : ∀ u : F.U, (u : G) ∉ F.W →
      (F.xHatStabilizer g hg (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
        (conjugate F.ZU g : Set G) * (F.E g : Set G)) :
    ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) := by
  let X := F.terminalDot (F.X g)
  let E := hatSpace F (F.E g)
  let α : X →* (Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive F.Uhat)).toMonoidHom.comp
      (F.terminalRepresentation.asGroupHom.comp X.subtype)
  have hf (e : E) : (∀ x : X, α x e = (e : Additive F.Uhat)) ↔
      e ∈ Submodule.span (ZMod 2) {(⟨v, hvE⟩ : E)} := by
    constructor
    · intro he
      have hm : (e : Additive F.Uhat) ∈ hatSpace F (F.Vi 2) := hfixed ▸ ⟨e.property, he⟩
      rw [hline] at hm
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc⟩
    · intro he
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp he
      have hm : v ∈ E ⊓ fixedSpace F.terminalRepresentation X :=
        hfixed.symm ▸ (hline.symm ▸ Submodule.mem_span_singleton_self v)
      intro x
      change F.terminalRepresentation x (c • v) = c • v
      rw [map_smul, show F.terminalRepresentation x v = v from hm.2 x]
  have hfull := BinaryTransvection.full_action_of_fixed_space α E ⟨v,hvE⟩ hv
    (fun x e => hline ▸ htrans x x.property e e.property) hf
  have hfix : X ≤ ChapterG.Section10.pointCentralizer F.terminalRepresentation v := by
    intro x hx
    exact ((hf ⟨v,hvE⟩).mpr (Submodule.mem_span_singleton_self _)) ⟨x,hx⟩
  let S := (T.subtype (F.invariant 1)).mapSurjective
    (f := QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hSC : (S : Subgroup F.TerminalHdot) ≤
      ChapterG.Section10.pointCentralizer F.terminalRepresentation v := by
    intro s hs
    exact hT s hs
  refine ⟨F.terminalRepresentation_injective, hBa, hB, hBinv, hv, hvE, hiso,
    hfix, hspan, ?_, ?_, ?_, ?_, hfull.1, hfull.2⟩
  · exact Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index
      (he.two_dvd.trans (Subgroup.index_dvd_of_le hSC)))
  · rw [elementary_rank_eq_finrank]
    exact hrank
  · intro x u hu
    exact F.terminal_displacement_mem_hatE g hWX x x.property u (hperp.symm ▸ hu)
  · intro x hx u hu
    have hm := F.terminal_fixed_bound g hg hker hstab x hx u hu
    rw [hperp] at hm
    exact hm

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
