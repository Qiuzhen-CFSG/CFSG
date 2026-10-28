module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product

/-!
# Faithful complements and the fixed quotient in B.5.12

If one factor fixes one summand of a faithful action, it is faithful on the
other summand. For complementary group factors acting on opposite summands,
the summands have disjoint images modulo the global fixed space. Indeed, if
u-w is globally fixed, opposite-factor centralization makes u globally fixed.
Surjectivity of the quotient map gives the remaining spanning assertion.

`SourceTwoFactorCase.of_cross_fixed` applies this argument to the literal
quotient action in B.5.6(3). The natural/extension identifications remain honest
inputs; this proves the decomposition step of B.5.12, not those identifications.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.106, 109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D : Type*} [Group D]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (ρ : Representation (ZMod 2) D V)

/-- Faithfulness on the complementary invariant module, as used in B.5.8. -/
theorem faithful_on_supplement (hρ : Function.Injective ρ) (B : Subgroup D)
    (U W : Subrepresentation ρ)
    (hs : U.toSubmodule ⊔ W.toSubmodule = ⊤)
    (hc : U.toSubmodule ≤ fixedSpace ρ B) :
    Function.Injective (W.toRepresentation.comp B.subtype) := by
  intro b c he
  apply Subtype.ext
  apply hρ
  apply LinearMap.ext
  intro v
  have hv : v ∈ U.toSubmodule ⊔ W.toSubmodule := by rw [hs]; trivial
  obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
  have hwu : ρ (b : D) w = ρ (c : D) w := by
    exact congrArg Subtype.val (LinearMap.congr_fun he (⟨w,hw⟩ : W))
  have hbu : ρ (b : D) u = u := hc hu b
  have hcu : ρ (c : D) u = u := hc hu c
  simp only [map_add, hwu, hbu, hcu]


/-- Opposite-factor centralization gives the direct sum in the fixed quotient. -/
theorem quotient_images_isCompl {A B : Subgroup D} (h : InternalProduct A B)
    (U W : Subrepresentation ρ)
    (hs : U.toSubmodule ⊔ W.toSubmodule = ⊤)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A) :
    IsCompl ((fixed ρ).quotientImage U).toSubmodule
      ((fixed ρ).quotientImage W).toSubmodule := by
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    rintro q ⟨⟨u, hu, rfl⟩, w, hw, he⟩
    have hd : u - w ∈ ρ.invariants :=
      (Submodule.Quotient.eq ρ.invariants).mp he.symm
    have huA (a : A) : ρ (a : D) u = u := by
      have hd' := hd (a : D)
      have hw' : ρ (a : D) w = w := hW hw a
      rw [map_sub, hw'] at hd'
      exact sub_left_inj.mp hd'
    have huG : u ∈ ρ.invariants := by
      intro g
      obtain ⟨a,b,rfl⟩ := h.exists_mul g
      change ρ ((a : D) * (b : D)) u = u
      rw [map_mul, Module.End.mul_apply, (show ρ (b : D) u = u from hU hu b), huA]
    exact (Submodule.Quotient.mk_eq_zero ρ.invariants).mpr huG
  · apply codisjoint_iff.mpr
    change U.toSubmodule.map ρ.invariants.mkQ ⊔ W.toSubmodule.map ρ.invariants.mkQ = ⊤
    rw [← Submodule.map_sup, hs, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr ρ.invariants.mkQ_surjective

/-- The actual B.5.12 consumer: retain both factor actions and construct
the missing quotient decomposition in B.5.6(3). -/
noncomputable def SourceTwoFactorCase.of_cross_fixed {A B : Subgroup D}
    (h : InternalProduct A B) (U W : Subrepresentation ρ)
    (hs : U.toSubmodule ⊔ W.toSubmodule = ⊤)
    (hU : U.toSubmodule ≤ fixedSpace ρ B)
    (hW : W.toSubmodule ≤ fixedSpace ρ A)
    (ha : SourceFactorCase ρ A U) (hb : SourceFactorCase ρ B W) : SourceTwoFactorCase ρ where
  first := A
  second := B
  product := h
  firstSpace := U
  secondSpace := W
  decomposition := quotient_images_isCompl ρ h U W hs hU hW
  firstCase := ha
  secondCase := hb

end CFSG.Quasithin.ChapterB.SourceInduction
