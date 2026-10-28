module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure.CoreComparison
public import Theory.GroupTheory.SimpleSectionSolvableReduction
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.Janko1.Model.Certification

/-!
# The actual component kernel in the moving case

The four nonnormal component models from 1.2.1(3) are simple. In the
projective rank-one case the component's perfectness supplies the Iwasawa
simplicity criterion, also excluding small solvable parameters. The
nontrivial plus image therefore embeds K/O₂(K), while its trivial two-core
kills O₂(K). Consequently C_K(W_K) is exactly O₂(K).

This source-specific kernel equality is stronger than what follows from
a paired natural module alone, and is used in the Borel lift in 13.6.14.
Source: Aschbacher--Smith, 1.2.1(3), 13.6.14, pp.504,929.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentElimination.SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem simple_of_model {D : Type*} [Group D] [Group.IsPerfect D]
    (hm : Chapter1.Section02.NonnormalCComponentModel D) : IsSimpleGroup D := by
  have hlinear {q : ℕ} (h : ClassicalGroup.IsPSL D 2 q) : IsSimpleGroup D := by
    obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
    let : Group.IsPerfect PSL(2, F) := Group.IsPerfect.ofSurjective
      (f := e.toMonoidHom) e.surjective
    exact e.isSimpleGroup_congr.mpr
      (MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
        PSL2.Iwasawa inferInstance)
  cases hm with
  | linear_even n hn iso => exact hlinear iso
  | linear_prime p hp ho iso => exact hlinear iso
  | suzuki m hm iso =>
    exact iso.some.isSimpleGroup_congr.mpr
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  | janko iso => exact iso.some.isSimpleGroup

/-- The source orbit theorem identifies the intrinsic quotient as simple. -/
theorem noninvariant_component_core_simple_source (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    IsSimpleGroup (K ⧸ pCore 2 K) := by
  let e := subgroupOfEquivOfLe (show K ≤ K ⊔ Tv T v from le_sup_left)
  let := hK.1.2.1.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact simple_of_model (noninvariant_component_pair_source K L T z v hlocal hK hn).2.1

/-- In the moving case the literal component action has exactly its
intrinsic two-core as kernel. -/
theorem noninvariant_component_centralizer_eq_core_source
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K := by
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    noninvariant_component_core_simple_source K L T z v hlocal hK hn
  let C := plusImage K L T z v hL hz K
  let : Nontrivial C := (nontrivial_iff_ne_bot _).mpr
    (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK)
  let f := subgroupPlusMap K L T K z v hL hz le_rfl
  have hC : pCore 2 C = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK),
      plus_twoCore_eq_bot K L T z v hK.1.1 hL hz hSylow]
    exact (MonoidHom.ker_eq_bot_iff _).mpr C.subtype_injective
  have hcore : pCore 2 K ≤ f.ker := by
    have hh := subgroupPlusMap_core_le K L T K z v hL hz le_rfl
    rw [hC] at hh
    exact hh
  let a := QuotientGroup.lift (pCore 2 K) f hcore
  have ha : Function.Injective a := MonoidHom.injective_of_surjective_of_simple a
    (QuotientGroup.lift_surjective_of_surjective _ _
      (subgroupPlusMap_surjective K L T K z v hL hz le_rfl) _)
  rw [← subgroupPlusMap_ker K L T K z v hL hz le_rfl]
  exact le_antisymm (fun x hx => (QuotientGroup.eq_one_iff _).mp
    (ha (show a (QuotientGroup.mk' (pCore 2 K) x) = a 1 by
      change f x = a 1
      rw [map_one]
      exact hx))) hcore

/-- The actual intrinsic quotient isomorphism, with the original plus map. -/
@[expose] noncomputable def componentCoreEquivPlus
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    (K ⧸ pCore 2 K) ≃* plusImage K L T z v hL hz K :=
  QuotientGroup.liftEquiv _ (subgroupPlusMap_surjective K L T K z v hL hz le_rfl)
    ((subgroupPlusMap_ker K L T K z v hL hz le_rfl).trans
      (noninvariant_component_centralizer_eq_core_source K L T z v hlocal hL hz hSylow hK hn)).symm

/-- The quotient coordinates retain the value of every element of K. -/
theorem componentCoreEquivPlus_mk
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) (k : K) :
    (componentCoreEquivPlus K L T z v hlocal hL hz hSylow hK hn
      (QuotientGroup.mk' (pCore 2 K) k) : Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion (K_le_plusActor K L T v) k) := rfl

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
