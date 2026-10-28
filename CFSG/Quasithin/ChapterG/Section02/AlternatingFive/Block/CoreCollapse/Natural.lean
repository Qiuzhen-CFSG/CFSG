module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Block.Centrality
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Full commutators on the natural upper section in G.2.4(8)

A cubic element in the literal starred image acts without nonzero fixed
vectors on each natural SL₂(4) plane. This includes the sum of zero planes.
The commutator map of the resulting fixed-point-free automorphism is
surjective. The representative formula in NaturalLayer lifts each such
commutator to [S,L₁], giving S=[S,L₁]S₂ in the original ambient group.

The cubic element remains explicit here; the local-image calculation and
the chief-factor step belong to the core-collapse assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(8), printed pp.334–335.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Block
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}
  {F : Type*} [Field F] {s : ℕ}
  {hLI : D.L ≤ D.I g} [((S₂ D g).subgroupOf (D.S g)).Normal]

omit [Finite G] in
/-- A cubic starred element acts freely on the actual upper quotient. -/
theorem NaturalLayer.cubic_fixedPointFree (n : NaturalLayer D g F s hLI)
    (t : D.L) (ht : orderOf (starProjection D t) = 3) :
    MonoidHom.FixedPointFree (n.action ⟨t, hLI t.property⟩) := by
  classical
  let : Finite F := Nat.finite_of_card_ne_zero (n.field_card ▸ by decide)
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa only [Nat.card_eq_fintype_card, show 2 ^ 2 = 4 from rfl] using n.field_card)
  intro x hx
  have hv := n.equivariant t x
  rw [hx] at hv
  have hz : (n.coordinates x).toAdd = 0 := by
    funext j
    exact Matrix.SL2.cubic_fixed_eq_zero _ ((n.model.orderOf_eq _).trans ht) _
      (congrFun hv.symm j)
  apply n.coordinates.injective
  exact (congrArg Multiplicative.ofAdd hz).trans n.coordinates.map_one.symm

/-- Full commutator generation, lifted through the original quotient map. -/
theorem NaturalLayer.core_eq_commutator_sup_second (n : NaturalLayer D g F s hLI)
    (t : D.L) (htL : (t : G) ∈ D.L₁) (ht : orderOf (starProjection D t) = 3)
    (hsecond : S₂ D g ≤ D.S g) :
    D.S g = ⁅D.S g, D.L₁⁆ ⊔ S₂ D g := by
  have hlocal : D.L₁ ≤ D.L := (map_subtype_le _).trans inf_le_left
  have hn : D.L₁ ≤ normalizer (D.S g : Set G) :=
    (hlocal.trans hLI).trans (I_normalizes_core D g)
  have hc : ⁅D.S g, D.L₁⁆ ≤ D.S g :=
    le_normalizer_iff_commutator_le_left.mp hn
  apply le_antisymm _ (sup_le hc hsecond)
  intro x hx
  let q := QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g))
  let xS : D.S g := ⟨x, hx⟩
  let tI : D.I g := ⟨t, hLI t.property⟩
  obtain ⟨y, hy⟩ := (n.cubic_fixedPointFree t ht).commutatorMap_surjective (q xS)
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective ((S₂ D g).subgroupOf (D.S g)) y
  change q z / n.action tI (q z) = q xS at hy
  rw [n.action_mk, ← map_div] at hy
  let w : D.S g := z / coreConjugate D g tI z
  have hw : (w : G) ∈ ⁅D.S g, D.L₁⁆ := by
    have he : (w : G) = ⁅(z : G), (t : G)⁆ := by
      dsimp [w, coreConjugate, tI]
      simp only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv]
      group
    rw [he]
    exact commutator_mem_commutator z.property htL
  have hxw : x / (w : G) ∈ S₂ D g := by
    exact (show xS / w ∈ (S₂ D g).subgroupOf (D.S g) from
      QuotientGroup.eq_iff_div_mem.mp hy.symm)
  have hh := (⁅D.S g, D.L₁⁆ ⊔ S₂ D g).mul_mem (mem_sup_right hxw) (mem_sup_left hw)
  simpa only [div_mul_cancel] using hh

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
