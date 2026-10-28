module
public import Theory.Representation.AlternatingSixPairedCovers.QuadraticActors
public import Theory.Representation.AlternatingSixPairedCovers.OddMovement
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.OuterCommutator
public import Theory.Representation.BinaryOffender.Basic
/-!
# Involution movement and the simultaneous quadratic classification

An involution in the component moves at least four dimensions. An outer
involution has a component commutator of order three or five. Those elements
move at least six or eight dimensions, while a commutator moves at most twice
as much as the involution. Thus every involution moves at least three.

Combined with the whole-actor order-four bound, the quadratic-member budget
forces rank two. Its actual intersection with the marked component contains
an involution. No stability, disjointness, or separate constituent actor is
assumed. This discharges the actor callback in the original-source consumer
ComponentCriticalPair.AlternatingSix.QuadraticActors.

Source: Aschbacher–Smith, original 14.6.24(2), printed p.1041.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace AlternatingSixPairedCovers.Data
variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) H E} (C : Data ρ)

include C in
/-- Every ambient involution moves at least three dimensions of the same
paired-cover module, including an involution interchanging the supports. -/
theorem involution_movement (a : H) (ha : orderOf a = 2) :
    3 ≤ fixedCodim ρ (zpowers a) := by
  by_cases hin : a ∈ C.component.range
  · obtain ⟨t,ht⟩ := hin
    have hn : t ≠ 1 := by intro h; have : a = 1 := ht.symm.trans (h ▸ map_one _); simp [this] at ha
    have hh := C.component_movement t hn
    rw [ht] at hh
    omega
  let K := C.component.range
  let : K.Normal := C.normal
  let e : alternatingGroup (Fin 6) ≃* K := MonoidHom.ofInjective C.injective
  let f := AlternatingSix.ShadowLocal.conjugationAction K e.symm
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    exact (AlternatingSix.ShadowLocal.conjugationAction_ker K e.symm).trans C.centralizer
  have hout : f a ∉ AlternatingSix.ShadowLocal.inner := by
    intro hm
    have hh : a ∈ AlternatingSix.ShadowLocal.inner.comap f := hm
    rw [AlternatingSix.ShadowLocal.conjugationAction_preimage_inner,C.centralizer,sup_bot_eq] at hh
    exact hin hh
  have horder : orderOf (f a) = 2 := (orderOf_injective f hf a).trans ha
  obtain ⟨g,hg⟩ := AlternatingSix.ShadowLocal.outer_involution_odd_commutator (f a) horder hout
  have hce (k : K) : C.component (e.symm k) = (k : H) :=
    congrArg Subtype.val (e.apply_symm_apply k)
  have hcon : C.component (f a g) = a * C.component g * a⁻¹ := by
    have hh := congrArg C.component
      (AlternatingSix.ShadowLocal.conjugationAction_apply K e.symm a (e g))
    rw [e.symm_apply_apply,hce] at hh
    exact hh
  have hm : C.component (f a g*g⁻¹) = a*C.component g*a⁻¹*(C.component g)⁻¹ := by
    rw [map_mul,map_inv,hcon]
  have hu := fixedCodim_commutator_le_twice ρ a (C.component g)
  rcases hg with hg | hg
  · have hl := C.component_cubic_movement (f a g*g⁻¹) hg
    rw [hm] at hl
    omega
  · have hl := C.component_quintic_movement (f a g*g⁻¹) hg
    rw [hm] at hl
    omega

/-- A positive-rank quadratic member of the whole paired module has rank two
and contains an involution of the marked component. -/
theorem quadratic_member (B : Subgroup H) (hB : IsElementaryTwo B)
    (hq : IsQuadratic ρ B) (hb : fixedCodim ρ B ≤ 2*rank B) :
    rank B = 2 ∧ ∃ t : alternatingGroup (Fin 6), orderOf t = 2 ∧ C.component t ∈ B := by
  let : IsElementaryAbelian 2 B := hB.2
  have hu := C.quadratic_rank_le_two B hq
  have hex : ∃ b ∈ B, b ≠ 1 := by
    by_contra! hn
    exact hB.1 (le_antisymm (fun b h => mem_bot.mpr (hn b h)) bot_le)
  obtain ⟨b,hmem,hne⟩ := hex
  have ho : orderOf b = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hmem) hne
  have hfix : fixedSpace ρ B ≤ fixedSpace ρ (zpowers b) := by
    intro v hv a
    exact hv ⟨a,(zpowers_le.mpr hmem) a.property⟩
  have hdim := Submodule.finrank_mono hfix
  have heB := fixedCodim_add_finrank ρ B
  have heb := fixedCodim_add_finrank ρ (zpowers b)
  have hl := C.involution_movement b ho
  have hr : rank B = 2 := by omega
  exact ⟨hr,C.component_involution_of_rank_gt_one B (by omega)⟩
end AlternatingSixPairedCovers.Data
