module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Canonical
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Transport
public import Theory.GroupTheory.SylowNormalCenterIntersection

/-!
# Residuals at central Sylow involutions

A normal subgroup of even order meets the ambient Sylow center in an
involution. In an actual PSU₃(q), for an odd prime q > 3, its involution-centralizer
residual is SL₂(q). The residual of C_D(Z(S)) lies in this involution residual. Equality
follows when the entire Sylow center centralizes that perfect subgroup.

The latter centralization is an explicit remaining premise. A cyclic center
alone does not justify replacing its centralizer by that of one involution.

Source: Aschbacher–Smith, proof of 1.3.4, printed pp.510–511.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
variable {G : Type*} [Group G]

/-- A normal even-order subgroup meets the entire ambient Sylow center in an involution. -/
theorem exists_involution_mem_centerImage [Finite G]
    (D : Subgroup G) [D.Normal] (S : Sylow 2 G) (hD : 2 ∣ Nat.card D) :
    ∃ z : D, orderOf z = 2 ∧ (z : G) ∈ centerImage (S : Subgroup G) := by
  obtain ⟨x, hx, hx1, hxD⟩ := S.exists_ne_one_mem_center_of_normal D hD
  let n := orderOf x / 2
  have hxn : orderOf (x ^ n) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' (S.isPGroup'.dvd_orderOf hx1)
  refine ⟨⟨(x : G) ^ n, D.pow_mem hxD n⟩, ?_, ?_⟩
  · rw [← orderOf_injective D.subtype D.subtype_injective]
    change orderOf ((x ^ n : S) : G) = 2
    rw [orderOf_coe]
    exact hxn
  · exact ⟨x ^ n, (center S).pow_mem hx n, rfl⟩

/-- The ambient image of the solvable residual of C_D(z). -/
@[expose] def involutionResidual (D : Subgroup G) (z : D) : Subgroup G :=
  ((solvableResidual (centralizer ({z} : Set D))).map
    (centralizer ({z} : Set D)).subtype).map D.subtype

/-- The ambient image of the involution residual lies in D. -/
theorem involutionResidual_le (D : Subgroup G) (z : D) : involutionResidual D z ≤ D :=
  map_subtype_le _

/-- The ambient involution residual in a PSU₃ model is the actual SL₂(q). -/
theorem involutionResidual_equiv [Finite G]
    (D : Subgroup G) (q : ℕ) [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (hmodel : ClassicalGroup.IsPSU D 3 q) (z : D) (hz : orderOf z = 2) :
    Nonempty (involutionResidual D z ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  obtain ⟨e⟩ := isPSU_involution_solvableResidual q hq hlarge hmodel z hz
  let ec := (solvableResidual (centralizer ({z} : Set D))).equivMapOfInjective
    (centralizer ({z} : Set D)).subtype (centralizer ({z} : Set D)).subtype_injective
  let ed := ((solvableResidual (centralizer ({z} : Set D))).map
    (centralizer ({z} : Set D)).subtype).equivMapOfInjective D.subtype D.subtype_injective
  exact ⟨ed.symm.trans (ec.symm.trans e)⟩

private theorem relative_centralizer_map (D : Subgroup G) (z : D) :
    (centralizer ({z} : Set D)).map D.subtype = D ⊓ centralizer ({(z : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx))⟩
  · rintro ⟨hxD, hx⟩
    exact ⟨⟨x, hxD⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hx)), rfl⟩

private theorem involutionResidual_eq [Finite G] (D : Subgroup G) (z : D) :
    involutionResidual D z =
      (solvableResidual (D ⊓ centralizer ({(z : G)} : Set G) : Subgroup G)).map
        (D ⊓ centralizer ({(z : G)} : Set G)).subtype := by
  let C := centralizer ({z} : Set D)
  let e : C ≃* (D ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) :=
    (C.equivMapOfInjective D.subtype D.subtype_injective).trans
      (MulEquiv.subgroupCongr (relative_centralizer_map D z))
  have he := congrArg (Subgroup.map (D ⊓ centralizer ({(z : G)} : Set G)).subtype)
    (map_solvableResidual_eq e.toMonoidHom e.surjective)
  have hcomp : (D ⊓ centralizer ({(z : G)} : Set G)).subtype.comp e.toMonoidHom =
      D.subtype.comp C.subtype := by ext x; rfl
  change ((solvableResidual C).map C.subtype).map D.subtype = _
  simpa only [map_map, hcomp] using he

/-- Centralizing the whole Sylow center implies centralizing each of its involutions. -/
theorem canonicalResidual_le_involutionResidual [Finite G] (D S : Subgroup G) (z : D)
    (hz : (z : G) ∈ centerImage S) : canonicalResidual D S ≤ involutionResidual D z := by
  rw [involutionResidual_eq]
  apply map_solvableResidual_mono
  exact inf_le_inf_left D (centralizer_le (Set.singleton_subset_iff.mpr hz))

/-- Perfectness gives equality once the involution residual centralizes the whole Sylow center. -/
theorem canonicalResidual_eq_involutionResidual [Finite G]
    (D S : Subgroup G) (z : D) (hz : (z : G) ∈ centerImage S)
    (hc : involutionResidual D z ≤ centralizer (centerImage S : Set G)) :
    canonicalResidual D S = involutionResidual D z := by
  apply le_antisymm (canonicalResidual_le_involutionResidual D S z hz)
  rw [involutionResidual_eq] at hc ⊢
  let R := (solvableResidual (D ⊓ centralizer ({(z : G)} : Set G) : Subgroup G)).map
    (D ⊓ centralizer ({(z : G)} : Set G)).subtype
  let _ : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (D ⊓ centralizer ({(z : G)} : Set G)).subtype.subgroupMap (solvableResidual _))
    ((D ⊓ centralizer ({(z : G)} : Set G)).subtype.subgroupMap_surjective _)
  apply le_map_solvableResidual_of_isPerfect
  exact le_inf ((map_subtype_le _).trans inf_le_left) hc
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
