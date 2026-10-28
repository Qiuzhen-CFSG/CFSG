module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Perpendicular

/-!
# Ambient cubic movement and the rank-one endpoint

Lift the explicit derived cubic through the original full automizer. The lift
centralizes the marked plane and moves its whole perpendicular subgroup by
commutators. Restriction to an actual component preserves this action and
supplies the marking required by the L₂(4) fixed-Sylow obstruction.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890. Component membership,
block placement and Sylow centralization remain explicit earlier obligations.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
variable {G : Type*} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem cubic_mem_orthogonal_iff (v : W) :
    rho cubic v ∈ form.orthogonal plane ↔ v ∈ form.orthogonal plane := by
  rw [cubic_action, mem_orthogonal, mem_orthogonal]
  rfl

theorem cubic_normalizes_perpendicular
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (n : normalizer (V : Set G))
    (hn : f (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    n.val ∈ normalizer (perpendicular E : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    let v : Additive V := Additive.ofMul ⟨x, perpendicular_le E hx⟩
    have h := he (V.normalizerMonoidHom.rangeRestrict n) v
    rw [hn] at h
    have hv : E v ∈ form.orthogonal plane := (mem_coordinateGroup E _ v).mp hx
    have hw : E (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v) ∈
        form.orthogonal plane := by
      rw [h]
      exact (cubic_mem_orthogonal_iff _).mpr hv
    exact (mem_coordinateGroup E _ _).mpr hw
  · intro hx
    have hxV : x ∈ V := (mem_normalizer_iff.mp n.property x).mpr
      (perpendicular_le E hx)
    let v : Additive V := Additive.ofMul ⟨x, hxV⟩
    have hv : E (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v) ∈
        form.orthogonal plane := (mem_coordinateGroup E _ _).mp hx
    rw [he, hn, cubic_mem_orthogonal_iff] at hv
    exact (mem_coordinateGroup E _ v).mpr hv

theorem exists_cubic_lift
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (hd : commutator (Atlas.G2.Model K) ≤ f.range)
    (A : Subgroup G) (hAV : A ≤ V) (hA : pointCoordinateSubspace E A = plane) :
    ∃ n : normalizer (V : Set G),
      f (V.normalizerMonoidHom.rangeRestrict n) = cubic ∧
      n.val ∈ centralizer (A : Set G) ∧
      n.val ∈ normalizer (perpendicular E : Set G) := by
  obtain ⟨a, ha⟩ := hd cubic_mem_derived
  obtain ⟨n, rfl⟩ := V.normalizerMonoidHom.rangeRestrict_surjective a
  refine ⟨n, ha, ?_, cubic_normalizes_perpendicular f E he n ha⟩
  intro x hx
  let v : Additive V := Additive.ofMul ⟨x, hAV hx⟩
  have hv : E v ∈ plane := hA ▸ (mem_pointCoordinateSubspace E A v).mpr hx
  have hf : automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) v = v := by
    apply E.injective
    rw [he, ha, cubic_fixes_plane _ hv]
  have hc : n.val * x * n.val⁻¹ = x := congrArg (fun w : Additive V => w.toMul.val) hf
  exact (mul_inv_eq_iff_eq_mul.mp hc).symm

theorem perpendicular_commutator
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (n : normalizer (V : Set G))
    (hn : f (V.normalizerMonoidHom.rangeRestrict n) = cubic) :
    ⁅zpowers n.val, perpendicular E⁆ = perpendicular E := by
  apply le_antisymm
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((zpowers_le).mpr (cubic_normalizes_perpendicular f E he n hn))
  · intro x hx
    let v : Additive V := Additive.ofMul ⟨x, perpendicular_le E hx⟩
    have hv : E v ∈ form.orthogonal plane := (mem_coordinateGroup E _ v).mp hx
    obtain ⟨w, hw, hd⟩ := firstCubic_moved_orthogonal (E v) hv
    let y : V := (E.symm w).toMul
    have hy : y.val ∈ perpendicular E := (mem_coordinateGroup E _ _).mpr (by
      simpa only [LinearEquiv.apply_symm_apply] using hw)
    have hc : ⁅n.val, y.val⁆ = x := by
      have hh : automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n)
          (E.symm w) - E.symm w = v := by
        apply E.injective
        rw [map_sub, he, hn, LinearEquiv.apply_symm_apply, hd]
      have hh' := congrArg (fun z : Additive V => z.toMul.val) hh
      simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul,
        Subgroup.coe_inv] at hh'
      change n.val * y.val * n.val⁻¹ * y.val⁻¹ = x at hh'
      simpa only [commutatorElement_def] using hh'
    exact hc ▸ Subgroup.commutator_mem_commutator (mem_zpowers n.val) hy

variable [Finite G]

theorem not_rankOne_of_perpendicular
    (f : Automizer V →* Atlas.G2.Model K) (E : Additive V ≃ₗ[K] W)
    (he : ∀ a v, E (automizerRepresentation V a v) = rho (f a) (E v))
    (n : normalizer (V : Set G))
    (hn : f (V.normalizerMonoidHom.rangeRestrict n) = cubic)
    (J : Subgroup G) (hJ : ChapterC.IsL2EvenBlock J 2)
    (hEJ : perpendicular E ≤ J) (hnJ : n.val ∈ J)
    (P : Sylow 2 J)
    (hU : (perpendicular E).subgroupOf J ≤ ChapterC.blockU J)
    (hP : perpendicular E ≤ centralizer ((P : Subgroup J).map J.subtype : Set G)) : False := by
  let B := (perpendicular E).subgroupOf J
  let e : B ≃* Multiplicative (form.orthogonal plane) :=
    (subgroupOfEquivOfLe hEJ).trans (coordinateEquiv E _)
  let a : J := ⟨n.val, hnJ⟩
  have ha : a ∈ normalizer (B : Set J) := by
    rw [← subgroupOf_normalizer_eq hEJ]
    exact cubic_normalizes_perpendicular f E he n hn
  apply UnitaryGeometry.not_L2Four_block_of_perpendicular_marking hJ P B hU
    (fun x hx y hy => Subtype.ext (hP hx y.val (mem_map_of_mem J.subtype hy))) e a ha
  intro x
  change E (Additive.ofMul ⟨n.val * x.val.val * n.val⁻¹, _⟩) =
    rho cubic (E (Additive.ofMul ⟨x.val.val, _⟩))
  have hh := he (V.normalizerMonoidHom.rangeRestrict n)
    (Additive.ofMul ⟨x.val.val, perpendicular_le E x.property⟩)
  rw [hn] at hh
  exact hh

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
