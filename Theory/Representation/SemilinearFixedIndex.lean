module
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement
public import Mathlib.FieldTheory.Finiteness
/-!
# Fixed indices of semilinear actors over the field of four elements

A nontrivial field twist gives an injection Fix(A) × Fix(A) into the natural
space by (v,w) ↦ v+c·w for a scalar c moved by the twist. Thus an actor with
a twist on F₄⁴ has fixed quotient of order at least sixteen. If all actors
are field-linear, faithfulness gives a nonzero F₄ fixed quotient and its
order is at least four.

This removes the ambient order-two possibility in the reciprocal critical
seed comparison of MS93 (3.3)--(3.4), printed pp.867--868.
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace Representation
variable {G F V : Type*} [Group G] [Field F] [AddCommGroup V]
  [Module (ZMod 2) V] [Module F V] [Finite V]

theorem fixed_card_sq_le_of_nontrivial_twist
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    {a : G} (ha : a ∈ A) {σ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F)
    (hase : ∀ c v, ρ a (c • v) = σ c • ρ a v) :
    Nat.card (fixedSpace ρ A)^2 ≤ Nat.card V := by
  obtain ⟨c,hc⟩ : ∃ c : F, σ c ≠ c := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  let f : fixedSpace ρ A × fixedSpace ρ A → V := fun p => p.1.val+c•p.2.val
  have hi : Function.Injective f := by
    rintro ⟨v,w⟩ ⟨v',w'⟩ he
    change v.val+c•w.val=v'.val+c•w'.val at he
    have hh : c•(w.val-w'.val)=v'.val-v.val := by
      rw [smul_sub]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using he)
    have hh' := congrArg (ρ a) hh
    have hv : ρ a v.val = v.val := v.property ⟨a,ha⟩
    have hv' : ρ a v'.val = v'.val := v'.property ⟨a,ha⟩
    have hw : ρ a w.val = w.val := w.property ⟨a,ha⟩
    have hw' : ρ a w'.val = w'.val := w'.property ⟨a,ha⟩
    rw [hase,map_sub,map_sub,hv,hv',hw,hw',←hh] at hh'
    have hz : (σ c-c) • (w.val-w'.val)=0 := by rw [sub_smul,hh',sub_self]
    have hww : w=w' := Subtype.ext (sub_eq_zero.mp
      ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)))
    have hvv : v=v' := by
      rw [hww] at he
      exact Subtype.ext (add_right_cancel he)
    exact Prod.ext hvv hww
  simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective f hi

section NaturalFour
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {G : Type*} [Group G]

theorem sixteen_le_fixed_quotient_card_of_twist
    (hF : Nat.card F = 4) (ρ : Representation (ZMod 2) G (Vector F))
    (A : Subgroup G) {a : G} (ha : a ∈ A) {σ : F ≃+* F}
    (hσ : σ ≠ RingEquiv.refl F)
    (hase : ∀ c v, ρ a (c • v) = σ c • ρ a v) :
    16 ≤ Nat.card (Vector F ⧸ fixedSpace ρ A) := by
  have hsq := fixed_card_sq_le_of_nontrivial_twist ρ A ha hσ hase
  have hV : Nat.card (Vector F)=256 := by
    rw [Module.natCard_eq_pow_finrank (K := F)]
    simp [Theory.SpecificGroups.SymplecticFour.Vector,hF]
  have hmul : Nat.card (fixedSpace ρ A) * Nat.card (Vector F ⧸ fixedSpace ρ A) = 256 := by
    rw [←hV, Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vector F ⧸ fixedSpace ρ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Vector F),←pow_add,add_comm,
      (fixedSpace ρ A).finrank_quotient_add_finrank]
  rw [hV] at hsq
  have hfix : Nat.card (fixedSpace ρ A) ≤ 16 := by nlinarith
  by_contra hn
  have hquot : Nat.card (Vector F ⧸ fixedSpace ρ A) ≤ 15 := by omega
  have hh := Nat.mul_le_mul hfix hquot
  rw [hmul] at hh
  norm_num at hh

theorem four_le_fixed_quotient_card_of_semilinear
    (hF : Nat.card F=4) (ρ : Representation (ZMod 2) G (Vector F))
    (hfaith : Function.Injective ρ)
    (hsemi : ∀ a : G, ∃ σ : F ≃+* F, ∀ c v, ρ a (c • v) = σ c • ρ a v)
    (A : Subgroup G) (hne : A ≠ ⊥) :
    4 ≤ Nat.card (Vector F ⧸ fixedSpace ρ A) := by
  classical
  by_cases hlin : ∀ a ∈ A, ∀ (c : F) v, ρ a (c • v)=c • ρ a v
  · let P : Submodule F (Vector F) :=
      { carrier := fixedSpace ρ A
        zero_mem' := (fixedSpace ρ A).zero_mem
        add_mem' := (fixedSpace ρ A).add_mem
        smul_mem' := by
          intro c v hv a
          change ρ a.val (c • v)=c • v
          rw [hlin a.val a.property]
          exact congrArg (c • ·) (hv a) }
    have hP : fixedSpace ρ A=P.restrictScalars (ZMod 2) := rfl
    have hcard : Nat.card (Vector F ⧸ fixedSpace ρ A)=Nat.card (Vector F ⧸ P) := by
      rw [hP]
      exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) P).toEquiv
    have hpos := fixedCodim_pos_of_faithful ρ hfaith hne
    have ht : 2 ≤ Nat.card (Vector F ⧸ fixedSpace ρ A) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hpos
    rw [hcard,Module.natCard_eq_pow_finrank (K := F),hF] at ht ⊢
    have hd : 1 ≤ Module.finrank F (Vector F ⧸ P) := by
      by_contra hn
      have hz : Module.finrank F (Vector F ⧸ P)=0 := by omega
      rw [hz,pow_zero] at ht
      omega
    exact Nat.pow_le_pow_right (by decide : 0 < 4) hd
  · push Not at hlin
    obtain ⟨a,ha,c,v,hcv⟩ := hlin
    obtain ⟨σ,hσ⟩ := hsemi a
    have hn : σ ≠ RingEquiv.refl F := by
      intro he
      apply hcv
      rw [hσ,he]
      rfl
    exact (by decide : 4 ≤ 16).trans
      (sixteen_le_fixed_quotient_card_of_twist hF ρ A ha hn hσ)
end NaturalFour
end Representation
