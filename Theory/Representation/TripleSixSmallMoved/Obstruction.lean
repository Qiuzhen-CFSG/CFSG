module

public import Theory.Representation.TripleSixSmallMoved.Sylow
public import Theory.Representation.PlaneRootNormalizer
public import Theory.Representation.ScalarCoinvariants
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Mathlib.GroupTheory.IndexNormal

/-!
# F₄-linear offenders in a group with dihedral Sylow subgroups

An elementary offender in a group with Sylow D8 has rank at most two.
Faithfulness and scalar restriction make its fixed codimension a positive
even integer, hence two, and its order four. It is normal of index two in a
Sylow subgroup. A binary plane bound gives a moved line over F₄. The common
center/axis lemma then puts this four-group in the Sylow center of order two,
a contradiction. No representation-recognition assumption is needed.

Source: the covered-A6 exclusion in Aschbacher–Smith 13.7.15(1), pp.943–944.
-/

public section
open Subgroup Representation.BinaryOffender
namespace Representation.TripleSixSmallMoved
variable {F G V : Type*} [Field F] [CharP F 2]
  [Algebra (ZMod 2) F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [Module (ZMod 2) V]
  [IsScalarTower (ZMod 2) F V] [FiniteDimensional F V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation F G V)

/-- The obstruction on the actual scalar-restricted representation. -/
theorem not_offender_plane (hF : Module.finrank (ZMod 2) F = 2)
    (hf : Function.Injective ρ)
    (hSyl : ∀ T : Sylow 2 G, Nat.card T = 8 ∧ Nat.card (center T) = 2)
    {A : Subgroup G} (hA : IsOffender (restrictScalars (k := ZMod 2) ρ) A)
    (hd : Module.finrank (ZMod 2)
      (subspaceCommutator (restrictScalars (k := ZMod 2) ρ) ⊤ A) ≤ 2) : False := by
  let σ := restrictScalars (k := ZMod 2) ρ
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨T,hAT⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  have hT := hSyl T
  have hcA : Nat.card A ≤ 8 := (Nat.card_le_card_of_injective
    (inclusion hAT) (inclusion_injective hAT)).trans_eq hT.1
  have hA8 : Nat.card A ≠ 8 := by
    intro he
    have hEq : A = (T : Subgroup G) := eq_of_le_of_card_ge hAT (by omega)
    have hcomm (x y : T) : x * y = y * x := by
      apply Subtype.ext
      exact congrArg (fun a : A => (a : G)) (mul_comm' (⟨x,hEq.symm ▸ x.property⟩ : A)
        (⟨y,hEq.symm ▸ y.property⟩ : A))
    have hz : center T = ⊤ := by
      apply top_unique
      intro x _
      exact mem_center_iff.mpr (fun y => hcomm y x)
    have hc := hT.2
    rw [hz,Nat.card_congr Subgroup.topEquiv.toEquiv,hT.1] at hc
    omega
  have hr : rank A ≤ 2 := by
    have hp := hA.1.card_eq_two_pow_rank
    have hh : 2 ^ rank A < 2 ^ 3 := by omega
    have hh' := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh
    omega
  have hfs : Function.Injective σ := by
    intro a b he
    apply hf
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun he v
  have hpos := fixedCodim_pos_of_faithful σ hfs hA.1.1
  have hcost := hA.2
  have hscalar := fixedCodim_restrictScalars ρ A
  rw [hF] at hscalar
  have hr2 : rank A = 2 := by change 0 < fixedCodim (restrictScalars ρ) A at hpos; omega
  have hAc : Nat.card A = 4 := by rw [hA.1.card_eq_two_pow_rank,hr2]; decide
  let A₀ := A.subgroupOf (T : Subgroup G)
  have hAc₀ : Nat.card A₀ = 4 := (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans hAc
  have hidx : A₀.index = 2 := by
    have hh := A₀.card_mul_index
    rw [hAc₀,hT.1] at hh
    omega
  let : A₀.Normal := normal_of_index_eq_two hidx
  have hd₀ : Module.finrank (ZMod 2)
      (subspaceCommutator (restrictScalars (k := ZMod 2) (ρ.comp (T : Subgroup G).subtype)) ⊤ A₀) ≤ 2 := by
    change Module.finrank (ZMod 2) (subspaceCommutator (σ.comp (T : Subgroup G).subtype) ⊤ A₀) ≤ 2
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hAT]
    exact hd
  rw [moved_finrank_restrictScalars,hF] at hd₀
  have hc₀ : fixedCodim (restrictScalars (k := ZMod 2)
      (ρ.comp (T : Subgroup G).subtype)) A₀ ≤ 2 :=
    (fixedCodim_subgroupOf σ hAT).le.trans (hcost.trans hr)
  rw [fixedCodim_restrictScalars,hF] at hc₀
  have hcentral : A₀ ≤ center T := PlaneRootNormalizer.le_center_of_moved_and_fixed_codim_le_one
    (ρ.comp (T : Subgroup G).subtype) T.isPGroup' (hf.comp (T : Subgroup G).subtype_injective) A₀ (by omega) (by omega)
  have hbound := Nat.card_le_card_of_injective (inclusion hcentral) (inclusion_injective hcentral)
  rw [hAc₀,hT.2] at hbound
  omega
end Representation.TripleSixSmallMoved
