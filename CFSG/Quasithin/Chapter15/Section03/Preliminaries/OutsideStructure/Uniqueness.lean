module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ActionQuotient
public import Stellmacher.TwoResidualIdentification
public import BenderSuzuki.External.Huppert.IV.ResidualGenerators
public import Mathlib.GroupTheory.IndexNormal

/-!
# Residual uniqueness in the outside-overgroup argument

Clause (12) of 15.3.11 uses the uniqueness dichotomy of 15.3.2(4).
The subgroup `D = O²(Y ∩ L)` is two-perfect, so it is contained in
`O²(⟨D,T⟩)`. Its nontrivial action excludes the centralizing branch of
that dichotomy. The index-two condition makes `S` normal in `T`, and
characteristicness then puts both `L` and `T` in the relevant normalizer.

The residual functor lemmas use its coprime-order generators; all normality
in the final exclusion is relative to `⟨L,S⟩`. The earlier dichotomy is an
explicit source input to be discharged by the preliminary assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.2(4) and 15.3.11(12), printed pp.1121 and 1123–1124.
-/

public section

open Subgroup
open Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]

private theorem residual_generators (X : Subgroup G) :
    twoResidualAmbient X = closure {x : G | x ∈ X ∧ Nat.Coprime 2 (orderOf x)} := by
  rw [twoResidualAmbient, Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual',
    BenderSuzuki.External.hktPResidual_eq_closure_coprime_orderOf, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, by simpa using hy⟩
  · rintro ⟨hx, ho⟩
    exact ⟨⟨x, hx⟩, by simpa using ho, rfl⟩

omit [Finite G] in
/-- The ambient residual lies in its defining subgroup. -/
theorem residual_le (X : Subgroup G) : twoResidualAmbient X ≤ X :=
  map_subtype_le _

/-- Residuals preserve subgroup inclusion. -/
theorem residual_mono {X Y : Subgroup G} (h : X ≤ Y) :
    twoResidualAmbient X ≤ twoResidualAmbient Y := by
  rw [residual_generators, residual_generators]
  exact closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

/-- The two-residual is two-perfect. -/
theorem residual_idempotent (X : Subgroup G) :
    twoResidualAmbient (twoResidualAmbient X) = twoResidualAmbient X := by
  apply le_antisymm (residual_le _) ?_
  rw [residual_generators X, residual_generators]
  apply Subgroup.closure_mono
  intro x hx
  exact ⟨subset_closure hx, hx.2⟩

/-- Clause (12), with the earlier 15.3.2(4) dichotomy explicit.
The source's additional condition `L ≤ I` is unnecessary for this argument. -/
theorem lemma_15_3_11_12_of_preliminary_uniqueness (T : Sylow 2 G) (M V Y S L : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hST : S ≤ (T : Subgroup G))
    (hindex : (S.subgroupOf (T : Subgroup G)).index = 2)
    (h24 : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ M ⊓ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M)
    (hact : ⁅V, twoResidualAmbient (Y ⊓ L)⁆ ≠ ⊥) (hL : ¬ L ≤ M)
    (C : Subgroup S) [C.Characteristic] (hC : C ≠ ⊥) :
    ¬ ((C.map S.subtype).subgroupOf (L ⊔ S)).Normal := by
  let D := twoResidualAmbient (Y ⊓ L)
  have hDL : D ≤ L := (residual_le _).trans inf_le_right
  have hDM : D ≤ M := (residual_le _).trans (inf_le_left.trans hYM)
  have hSn : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hindex)
  have hDres : D ≤ twoResidualAmbient (D ⊔ (T : Subgroup G)) := by
    calc
      D = twoResidualAmbient D := (residual_idempotent _).symm
      _ ≤ twoResidualAmbient (D ⊔ (T : Subgroup G)) := residual_mono le_sup_left
  have hu : Chapter4.UniqueMaximalOvergroup (D ⊔ (T : Subgroup G)) M := by
    rcases h24 _ le_sup_right (sup_le hDM hTM) with hc | hu
    · exact False.elim (hact (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (hDres.trans (hc.trans inf_le_right)))))
    · exact hu
  exact no_characteristic_subgroup_normal_in_join T S L D M hST hSn hDL hL hu C hC

/-- The residual is invariant under every normalizer of the original subgroup. -/
theorem normalizer_le_normalizer_residual (X : Subgroup G) :
    normalizer (X : Set G) ≤ normalizer (twoResidualAmbient X : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact map_twoResidualAmbient_of_subgroup_image X (MulAut.conj g).toMonoidHom X
    (mem_normalizer_iff_map_conj_eq.mp hg)

/-- Relative normalization of an intersection passes to its residual. -/
theorem intersection_le_normalizer_residual (M Y I : Subgroup G)
    (hMY : M ≤ normalizer (Y : Set G)) :
    M ⊓ I ≤ normalizer (twoResidualAmbient (Y ⊓ I) : Set G) := by
  exact (le_inf (inf_le_left.trans hMY) (inf_le_right.trans I.le_normalizer)).trans
    ((inf_normalizer_le_normalizer_inf (H := Y) (K := I)).trans (normalizer_le_normalizer_residual _))

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
