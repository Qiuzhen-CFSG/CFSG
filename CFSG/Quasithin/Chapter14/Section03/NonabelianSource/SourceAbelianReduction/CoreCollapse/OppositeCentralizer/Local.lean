module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.Sylow
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Transfer

/-!
# Consequences of the local opposite-involution calculations

The span is the literal supremum of whole conjugates in T. Commutativity
and the relation among the three squares make their nonidentity product
an involution. The local natural action puts z in the derived group of
the global centralizer, and the original quotient of order four separates
w from H'. Together with centralizer fusion these supply the actual
generalized-transfer contradiction.

The construction of LocalGeometry and the recognition of C_G(w) remain
independent obligations. No existence or global fusion is asserted here.
Source: Aschbacher--Smith, 14.3.22, printed pp.998--999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- Agreement between the closure implementation and the source supremum,
including the source's right-conjugation convention. -/
theorem span_eq_sSup (F : InvariantFlag T V 2) :
    span F = sSup {A : Subgroup G | ∃ a : G,
      conjugate (supplement F) a = A ∧ A ≤ (T : Subgroup G)} := by
  apply le_antisymm
  · apply conjugateSubgroupClosure_le
    intro a ha
    apply le_sSup
    exact ⟨a⁻¹, by simp [conjugate], ha⟩
  · apply sSup_le
    rintro A ⟨a, rfl, ha⟩
    exact map_conj_le_conjugateSubgroupClosure (supplement F) a⁻¹ ha

/-- The actual three factors yield an involution once the plane calculation
gives the square relation and the six-letter image gives nonidentity. -/
theorem triple_product_involution (F : InvariantFlag T V 2)
    (hab : IsMulCommutative (span F)) (d a : G) (hd : d ∈ supplement F)
    (hD : supplement F ≤ (T : Subgroup G))
    (ha : conjugate (supplement F) a ≤ (T : Subgroup G))
    (ha2 : conjugate (supplement F) (a ^ 2) ≤ (T : Subgroup G))
    (hsquares : d ^ 2 * (MulAut.conj a⁻¹) (d ^ 2) *
      (MulAut.conj (a ^ 2)⁻¹) (d ^ 2) = 1)
    (hne : d * (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d ≠ 1) :
    let w := d * (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d
    w ∈ (T : Subgroup G) ∧ orderOf w = 2 := by
  let := hab
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  have h0 : d ∈ span F := by
    apply map_conj_le_conjugateSubgroupClosure (supplement F) (1 : G)
      (by simpa only [hid, map_id] using hD)
    simpa using mem_map_of_mem (MulAut.conj (1 : G)).toMonoidHom hd
  have h1 : (MulAut.conj a⁻¹) d ∈ span F :=
    map_conj_le_conjugateSubgroupClosure (supplement F) a⁻¹ ha
      (mem_map_of_mem _ hd)
  have h2 : (MulAut.conj (a ^ 2)⁻¹) d ∈ span F :=
    map_conj_le_conjugateSubgroupClosure (supplement F) (a ^ 2)⁻¹ ha2
      (mem_map_of_mem _ hd)
  have hc (x y : G) (hx : x ∈ span F) (hy : y ∈ span F) : Commute x y :=
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : span F) ⟨y, hy⟩)
  refine ⟨conjugateSubgroupClosure_le_self _ _ ((span F).mul_mem ((span F).mul_mem h0 h1) h2),
    orderOf_eq_prime ?_ hne⟩
  rw [(hc _ _ ((span F).mul_mem h0 h1) h2).mul_pow, (hc _ _ h0 h1).mul_pow]
  simpa only [map_pow] using hsquares

/-- The local natural plane action puts the original point in C_G(w)'. -/
theorem LocalGeometry.point_mem_global_commutator
    {F : InvariantFlag T V 2} {L : Subgroup G} {z w : G}
    (h : LocalGeometry F L z w) :
    z ∈ (_root_.commutator (centralizer ({w} : Set G))).map
      (centralizer ({w} : Set G)).subtype := by
  have hzV : z ∈ V := F.le_seed 1 (h.point.symm ▸ mem_zpowers z)
  have hc := commutator_mono h.plane_centralizes
    (show F.I₂ L ⊓ centralizer ({w} : Set G) ≤ centralizer ({w} : Set G) from inf_le_right)
  rw [h.plane_moved] at hc
  rw [map_subtype_commutator]
  exact hc hzV

/-- The literal quotient H/(O²(H)R), of order four, excludes w from H'. -/
theorem LocalGeometry.outside_point_commutator
    {F : InvariantFlag T V 2} {L : Subgroup G} {z w : G}
    (h : LocalGeometry F L z w) :
    w ∉ (_root_.commutator F.H).map F.H.subtype := by
  let N := (localResidual F ⊔ (F.I₂ L).pCoreIn 2).subgroupOf F.H
  let : N.Normal := h.quotient_normal
  have hcard : Nat.card (F.H ⧸ N) = 2 ^ 2 := h.quotient_index
  have hc : IsMulCommutative (F.H ⧸ N) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  have hle : _root_.commutator F.H ≤ N :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hc
  rintro ⟨x, hx, rfl⟩
  exact h.outside_residual (hle hx)

variable [Finite G]

/-- Conditional source application to the proved transfer endpoint.
Fusion is the remaining residual-recognition consumer, not a local hypothesis
that is silently discharged. -/
theorem false_of_local_geometry_and_fusion {K : GroupClass}
    (hG : IsSimpleQTKE K G) (F : InvariantFlag T V 2) (L : Subgroup G) (z w : G)
    (h : LocalGeometry F L z w)
    (hf : ∀ a ∈ centralizer ({w} : Set G), IsConj z a →
      ∃ c ∈ centralizer ({w} : Set G), c * z * c⁻¹ = a) : False := by
  have hH := F.H_eq_centralizer (by decide) z h.point
  have hT : (T : Subgroup G) ≤ centralizer ({z} : Set G) := hH ▸ F.invariant 1
  have hwC : w ∈ centralizer ({z} : Set G) := hT h.mem_sylow
  have hnot : (⟨w, hwC⟩ : centralizer ({z} : Set G)) ∉
      _root_.commutator (centralizer ({z} : Set G)) := by
    intro hw
    have hm := mem_map_of_mem (centralizer ({z} : Set G)).subtype hw
    change w ∈ (_root_.commutator (centralizer ({z} : Set G))).map
      (centralizer ({z} : Set G)).subtype at hm
    rw [← hH] at hm
    exact h.outside_point_commutator hm
  let : IsMulCommutative ((centralizer ({z} : Set G)) ⧸
      _root_.commutator (centralizer ({z} : Set G))) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr le_rfl
  exact NonabelianSource.false_of_centralizer_fusion hG T z w hT hwC
    (_root_.commutator (centralizer ({z} : Set G))) h.involution hnot hf

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
