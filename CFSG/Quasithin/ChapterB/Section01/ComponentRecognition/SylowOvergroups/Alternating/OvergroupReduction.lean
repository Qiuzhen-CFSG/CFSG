module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.SmallModels
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod

/-!
# The intrinsic alternating overgroup input to B.1.13

An order-three subgroup has a genuine A₃ model. If K = L, the given Aₘ
model supplies the conclusion. In the remaining quasisimple case, intersect
K ∨ T with L and retain the exact restricted Sylow subgroup. Relative
subnormality pulls back to this intersection. Transport by the given model
isomorphism makes K a component of a proper Sylow overgroup in Aₘ.

The component classification of those intrinsic overgroups is an explicit
remaining premise. This module proves the ambient transport and discharges
the other branches; it does not claim the full source classification.
The exceptional conclusion uses the actual matrix quotient PSL₃(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), final paragraph. The reference to A.3.12 there
is restricted to SQTK and does not discharge the arbitrary-degree premise.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The genuine alternating or exceptional matrix-model conclusion of B.1.13(3). -/
@[expose] def AlternatingSubgroupModels (m : ℕ) (K : Type*) [Group K] : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧ n ≤ m ∧ Nonempty (K ≃* alternatingGroup (Fin n))) ∨
    (m = 7 ∧ Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)))

/-- The remaining intrinsic classification: components of proper Sylow
overgroups in Aₘ have the source models and the exact exceptional degree. -/
@[expose] def AlternatingProperSylowComponentModels (m : ℕ) : Prop :=
  ∀ (S : Sylow 2 (alternatingGroup (Fin m)))
    (X : Subgroup (alternatingGroup (Fin m))), (S : Subgroup _) ≤ X → X ≠ ⊤ →
    ∀ D : Subgroup X, IsComponent X D → AlternatingSubgroupModels m D

private theorem models_transport {A B : Type*} [Group A] [Group B]
    {m : ℕ} (e : A ≃* B) (h : AlternatingSubgroupModels m B) :
    AlternatingSubgroupModels m A := by
  rcases h with ⟨n,hn,hnm,⟨d⟩⟩ | ⟨hm,⟨d⟩⟩
  · exact Or.inl ⟨n,hn,hnm,⟨e.trans d⟩⟩
  · exact Or.inr ⟨hm,⟨e.trans d⟩⟩

variable {G : Type*} [Group G]

/-- Relative subnormality in the literal local overgroup gives a component
of the actual model Sylow overgroup. The model classification premise remains explicit. -/
theorem alternating_subgroup_models_of_proper_overgroups [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G) {m : ℕ} (hm : 5 ≤ m)
    (e : L ≃* alternatingGroup (Fin m))
    (hL : IsComponent G L) (hKL : K ≤ L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hLK : ⁅L, K⁆ = L) (hmodels : AlternatingProperSylowComponentModels m) :
    AlternatingSubgroupModels m K := by
  rcases hkind with hq | hc
  swap
  · exact Or.inl ⟨3, le_rfl, by omega, ⟨mulEquivOfPrimeCardEq hc (by
      rw [nat_card_alternatingGroup]; norm_num [Nat.card_fin, Nat.factorial])⟩⟩
  by_cases heq : K = L
  · subst K
    exact Or.inl ⟨m, by omega, le_rfl, ⟨e⟩⟩
  let := hq
  let H := K ⊔ (T : Subgroup G)
  let X : Subgroup L := H.subgroupOf L
  let D : Subgroup X := (K.subgroupOf L).subgroupOf X
  have hDX : K.subgroupOf L ≤ X := comap_mono le_sup_left
  let d : D ≃* K := (subgroupOfEquivOfLe hDX).trans (subgroupOfEquivOfLe hKL)
  have hD : IsComponent X D := by
    constructor
    · let f : X →* H := {
        toFun x := ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      exact hK.comap f
    · exact IsQuasisimple.of_mulEquiv d.symm
  obtain ⟨S,hSX,hX,_⟩ := local_intersection_sylow K L T hL hLK hK (lt_of_le_of_ne hKL heq)
  let Y := X.map e.toMonoidHom
  let i : X ≃* Y := e.subgroupMap X
  let B : Subgroup Y := D.map i.toMonoidHom
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hY : Y ≠ ⊤ := by
    intro h
    apply hX
    apply map_injective (f := e.toMonoidHom) e.injective
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using h
  have hQB : (Q : Subgroup _) ≤ Y := map_mono hSX
  have hB := hmodels Q Y hQB hY B (hD.map_equiv i)
  exact models_transport (d.symm.trans (i.subgroupMap D)) hB

/-- The already proved degree-five classification has the same model output. -/
theorem alternatingFive_subgroup_models_full (K L : Subgroup G)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3) (hKL : K ≤ L)
    (e : L ≃* alternatingGroup (Fin 5)) : AlternatingSubgroupModels 5 K :=
  Or.inl (alternatingFive_subgroup_models K L hkind hKL e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
