module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.SmallSupport
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Pi

/-!
# The actual cubic product and sum of binary planes

Enumerate the distinct nonzero subgroups [F(G),A] for minimal best offenders.
The local-plane law and the checked D.2.12 application give independent,
commuting cubic factors and independent rank-two supports. The product of
the subgroup inclusions and sum of the subspace inclusions have ranges F and
[V,F], respectively. Their injectivity constructs actual internal product
and sum equivalences, with the coordinate inclusions identified explicitly.

These are the cubic and linear parts of B.1.9(2–3); identifying the cubic
factors as the odd cores of the corresponding Gᵢ remains a separate step.
Source: Aschbacher–Smith, B.1.9, printed p.71.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [Finite G]

/-- The number of distinct nonzero minimal-offender Fitting commutators. -/
@[expose] noncomputable def cubicCount : ℕ := Nat.card (minimalMovedFactors ρ)

/-- An enumeration of precisely the source's Fᵢ, with no repetitions. -/
@[expose] noncomputable def cubicEnumeration : Fin (cubicCount ρ) ≃ minimalMovedFactors ρ :=
  (Finite.equivFin (minimalMovedFactors ρ)).symm

/-- The i-th subgroup Fᵢ, still embedded in the original ambient group. -/
@[expose] noncomputable def cubicFactor (i : Fin (cubicCount ρ)) : Subgroup G :=
  (cubicEnumeration ρ i).val

theorem cubicFactor_mem (i : Fin (cubicCount ρ)) :
    cubicFactor ρ i ∈ minimalMovedFactors ρ := (cubicEnumeration ρ i).property

theorem cubicFactor_injective : Function.Injective (cubicFactor ρ) := by
  intro i j hij
  exact (cubicEnumeration ρ).injective (Subtype.ext hij)

theorem range_cubicFactor : Set.range (cubicFactor ρ) = minimalMovedFactors ρ := by
  ext X
  constructor
  · rintro ⟨i, rfl⟩
    exact cubicFactor_mem ρ i
  · intro hX
    obtain ⟨i, hi⟩ := (cubicEnumeration ρ).surjective ⟨X, hX⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem cubicCount_pos (hF : fittingMoved ρ ≠ ⊥) : 0 < cubicCount ρ := by
  obtain ⟨X, hX⟩ := minimalMovedFactors_nonempty ρ hF
  let : Nonempty (minimalMovedFactors ρ) := ⟨⟨X, hX⟩⟩
  exact Nat.card_pos

theorem cubicFactor_iSup : (⨆ i, cubicFactor ρ i) = fittingMoved ρ := by
  rw [← sSup_range, range_cubicFactor, ← fittingMoved_eq_sSup]

theorem cubicFactor_le (i : Fin (cubicCount ρ)) : cubicFactor ρ i ≤ fittingMoved ρ :=
  (le_iSup (cubicFactor ρ) i).trans (cubicFactor_iSup ρ).le

theorem cubicFactor_card (hlocal : LocalPlaneLaw ρ) (i : Fin (cubicCount ρ)) :
    Nat.card (cubicFactor ρ i) = 3 :=
  (minimalMovedFactors_subset_small ρ hlocal (cubicFactor_mem ρ i)).2.1

/-- Each enumerated factor is a genuine cyclic group of order three. -/
noncomputable def cubicFactorModel (hlocal : LocalPlaneLaw ρ)
    (i : Fin (cubicCount ρ)) : cubicFactor ρ i ≃* Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (cubicFactor_card ρ hlocal i) (Nat.card_zmod 3)

theorem cubicFactor_dimension (hlocal : LocalPlaneLaw ρ) (i : Fin (cubicCount ρ)) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (cubicFactor ρ i)) = 2 :=
  (minimalMovedFactors_subset_small ρ hlocal (cubicFactor_mem ρ i)).2.2

variable [FiniteDimensional (ZMod 2) V]

theorem cubicFactors_independent (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    iSupIndep (cubicFactor ρ) :=
  (minimalMovedFactors_decomposition ρ hρ hlocal).1.comp (cubicEnumeration ρ).injective

theorem cubicFactors_commute (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    Pairwise fun i j => ∀ x y : G, x ∈ cubicFactor ρ i → y ∈ cubicFactor ρ j →
      Commute x y := by
  intro i j _ x y hx hy
  have hc := (minimalMovedFactors_decomposition ρ hρ hlocal).2.1
    _ (cubicFactor_mem ρ i) _ (cubicFactor_mem ρ j) hx
  exact (mem_centralizer_iff.mp hc y hy).symm

theorem cubicSupports_independent (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    iSupIndep (fun i => subspaceCommutator ρ ⊤ (cubicFactor ρ i)) :=
  (minimalMovedFactors_decomposition ρ hρ hlocal).2.2.1.comp
    (cubicEnumeration ρ).injective

omit [FiniteDimensional (ZMod 2) V] in
theorem cubicSupports_iSup :
    (⨆ i, subspaceCommutator ρ ⊤ (cubicFactor ρ i)) =
      subspaceCommutator ρ ⊤ (fittingMoved ρ) := by
  rw [← Representation.BinaryGroupAction.moved_iSup, cubicFactor_iSup]

/-- Multiply the actual commuting subgroup inclusions into F. -/
noncomputable def cubicProduct (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    ((i : Fin (cubicCount ρ)) → cubicFactor ρ i) ≃* fittingMoved ρ :=
  (MonoidHom.ofInjective (Subgroup.injective_noncommPiCoprod_of_iSupIndep
    (hcomm := cubicFactors_commute ρ hρ hlocal) (cubicFactors_independent ρ hρ hlocal))).trans
      (MulEquiv.subgroupCongr ((Subgroup.noncommPiCoprod_range).trans (cubicFactor_iSup ρ)))

theorem cubicProduct_single (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    (i : Fin (cubicCount ρ)) (g : cubicFactor ρ i) :
    (cubicProduct ρ hρ hlocal (Pi.mulSingle i g) : G) = g :=
  Subgroup.noncommPiCoprod_mulSingle (hcomm := cubicFactors_commute ρ hρ hlocal) i g

private noncomputable def planeSumMap :
    ((i : Fin (cubicCount ρ)) → subspaceCommutator ρ ⊤ (cubicFactor ρ i)) →ₗ[ZMod 2] V :=
  LinearMap.lsum (ZMod 2) _ (ZMod 2)
    (fun i => (subspaceCommutator ρ ⊤ (cubicFactor ρ i)).subtype)

omit [FiniteDimensional (ZMod 2) V] in
private theorem planeSumMap_apply (v) : planeSumMap ρ v = ∑ i, (v i : V) := by
  simp only [planeSumMap, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply]

private theorem planeSumMap_injective (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    Function.Injective (planeSumMap ρ) := by
  intro v w hvw
  have he := (iSupIndep_iff_finsetSum_eq_imp_eq
    (fun i => subspaceCommutator ρ ⊤ (cubicFactor ρ i))).mp
    (cubicSupports_independent ρ hρ hlocal) Finset.univ
    (fun i => (v i : V)) (fun i => (w i : V))
    (fun i _ => ⟨(v i).property, (w i).property⟩)
    (by simpa only [planeSumMap_apply] using hvw)
  funext i
  exact Subtype.ext (he i (Finset.mem_univ i))

omit [FiniteDimensional (ZMod 2) V] in
private theorem planeSumMap_range :
    (planeSumMap ρ).range = subspaceCommutator ρ ⊤ (fittingMoved ρ) := by
  rw [← cubicSupports_iSup]
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [planeSumMap_apply]
    exact Submodule.sum_mem _ fun i _ =>
      (le_iSup (fun j => subspaceCommutator ρ ⊤ (cubicFactor ρ j)) i) (v i).property
  · refine iSup_le fun i v hv => ?_
    refine ⟨Pi.single i ⟨v, hv⟩, ?_⟩
    exact LinearMap.lsum_piSingle (ZMod 2) _ (ZMod 2)
      (fun j => (subspaceCommutator ρ ⊤ (cubicFactor ρ j)).subtype) i ⟨v, hv⟩

/-- Add the actual plane inclusions into [V,F]. -/
noncomputable def planeSum (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    ((i : Fin (cubicCount ρ)) → subspaceCommutator ρ ⊤ (cubicFactor ρ i)) ≃ₗ[ZMod 2]
      subspaceCommutator ρ ⊤ (fittingMoved ρ) :=
  (LinearEquiv.ofInjective (planeSumMap ρ) (planeSumMap_injective ρ hρ hlocal)).trans
    (LinearEquiv.ofEq _ _ (planeSumMap_range ρ))

theorem planeSum_single (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ)
    (i : Fin (cubicCount ρ)) (v : subspaceCommutator ρ ⊤ (cubicFactor ρ i)) :
    (planeSum ρ hρ hlocal (Pi.single i v) : V) = v :=
  LinearMap.lsum_piSingle (ZMod 2) _ (ZMod 2)
    (fun j => (subspaceCommutator ρ ⊤ (cubicFactor ρ j)).subtype) i v

theorem fittingMoved_card (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    Nat.card (fittingMoved ρ) = 3 ^ cubicCount ρ := by
  rw [← Nat.card_congr (cubicProduct ρ hρ hlocal).toEquiv, Nat.card_pi]
  simp only [cubicFactor_card ρ hlocal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem fittingMoved_dimension (hρ : Function.Injective ρ) (hlocal : LocalPlaneLaw ρ) :
    Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (fittingMoved ρ)) =
      2 * cubicCount ρ := by
  rw [← (planeSum ρ hρ hlocal).finrank_eq, Module.finrank_pi_fintype]
  simp only [cubicFactor_dimension ρ hlocal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

end CFSG.Quasithin.ChapterB.FittingStructure
