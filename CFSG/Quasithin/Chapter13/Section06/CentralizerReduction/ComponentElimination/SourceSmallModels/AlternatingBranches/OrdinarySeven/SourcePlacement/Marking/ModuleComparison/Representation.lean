module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.Action
public import Theory.Representation.NormalElementaryQuotient


/-!
# The literal binary representation on W₀

Here W₀ is W_K restricted to the plus actor. Its normality is relative to that
actor, and the kernel of the literal plus projection is precisely C(W₀).
The centralizer-quotient construction therefore supplies a faithful binary
representation. Fixed vectors are identified with ambient centralizers through
the same quotient map, with no choice of module coordinates.

Normalization of K and Lᵥ ≤ K also reduce W_K to the span of z under K.
These are the action and seed interfaces for the ordinary A₇ argument in
Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 13.6.22,
printed p.932 (PDF p.949).
-/

@[expose] public section

open Subgroup Equiv
open Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
variable {G : Type*} [Group G]

abbrev Carrier (K L T : Subgroup G) (z v : G) :=
  (WK K L T z v).subgroupOf (plusActor K L T v)

instance carrier_elementary (K L T : Subgroup G) (z v : G)
    [IsElementaryAbelian 2 (WK K L T z v)] : IsElementaryAbelian 2 (Carrier K L T z v) where
  toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative (H := WK K L T z v) (K := plusActor K L T v)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A := WK K L T z v) x x.property

theorem carrier_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hWT : WK K L T z v ≤ Tv T v) : (Carrier K L T z v).Normal :=
  (normal_subgroupOf_iff_le_normalizer (hWT.trans le_sup_right)).mpr
    (plusActor_normalizes_WK K L T z v hL hz)

theorem projection_kernel (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hWT : WK K L T z v ≤ Tv T v) :
    (plusMk K L T z v hL hz).ker = centralizer (Carrier K L T z v : Set (plusActor K L T v)) := by
  rw [plusMk_ker]
  ext x
  constructor
  · intro hx w hw
    apply Subtype.ext
    exact hx w hw
  · intro hx w hw
    exact congrArg Subtype.val (hx ⟨w, (show Tv T v ≤ plusActor K L T v from le_sup_right) (hWT hw)⟩ hw)

noncomputable def representation (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) :
    Representation (ZMod 2) (Gplus K L T z v hL hz) (Additive (Carrier K L T z v)) := by
  let := carrier_normal K L T z v hL hz hWT
  exact Representation.NormalElementaryQuotient.representation _ _
    (plusMk_surjective K L T z v hL hz) (projection_kernel K L T z v hL hz hWT)

theorem representation_apply (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) (x : plusActor K L T v)
    (w : Additive (Carrier K L T z v)) :
    (((representation K L T z v hL hz hWT (plusMk K L T z v hL hz x) w).toMul :
      plusActor K L T v) : G) = (x : G) * (w.toMul : plusActor K L T v) * (x : G)⁻¹ := by
  let := carrier_normal K L T z v hL hz hWT
  exact congrArg Subtype.val (Representation.NormalElementaryQuotient.representation_apply _ _
    (plusMk_surjective K L T z v hL hz) (projection_kernel K L T z v hL hz hWT) x w)

theorem representation_injective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) :
    Function.Injective (representation K L T z v hL hz hWT) := by
  let := carrier_normal K L T z v hL hz hWT
  exact Representation.NormalElementaryQuotient.representation_injective _ _
    (plusMk_surjective K L T z v hL hz) (projection_kernel K L T z v hL hz hWT)

/-- Before descent, the linear action has exactly the original centralizer kernel. -/
theorem representation_comp_kernel (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) :
    ((representation K L T z v hL hz hWT).comp (plusMk K L T z v hL hz)).ker =
      centralizer (Carrier K L T z v : Set (plusActor K L T v)) := by
  rw [← projection_kernel K L T z v hL hz hWT]
  ext x
  change representation K L T z v hL hz hWT (plusMk K L T z v hL hz x) = 1 ↔
    plusMk K L T z v hL hz x = 1
  constructor
  · intro h
    apply representation_injective K L T z v hL hz hWT
    simpa using h
  · intro h
    rw [h, map_one]

theorem mem_fixedSpace_image (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hWT : WK K L T z v ≤ Tv T v) (A : Subgroup G) (hA : A ≤ plusActor K L T v)
    (w : Additive (Carrier K L T z v)) :
    w ∈ fixedSpace (representation K L T z v hL hz hWT) (plusImage K L T z v hL hz A) ↔
      ((w.toMul : plusActor K L T v) : G) ∈ centralizer (A : Set G) := by
  let := carrier_normal K L T z v hL hz hWT
  change w ∈ fixedSpace (Representation.NormalElementaryQuotient.representation _ _
    (plusMk_surjective K L T z v hL hz) (projection_kernel K L T z v hL hz hWT))
      ((A.subgroupOf (plusActor K L T v)).map (plusMk K L T z v hL hz)) ↔ _
  rw [Representation.NormalElementaryQuotient.mem_fixedSpace_image]
  constructor
  · intro hw a ha
    exact congrArg Subtype.val (hw ⟨a, hA ha⟩ ha)
  · intro hw a ha
    exact Subtype.ext (hw a ha)

theorem seed_span (K L T : Subgroup G) (z v : G)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K) :
    WK K L T z v = conjugateSpanBy (zpowers z) K := by
  have hm : Kminus K T v = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy K (Tv T v))
  rw [WK, hm, sup_eq_left.mpr hLv]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking.ModuleComparison
end
