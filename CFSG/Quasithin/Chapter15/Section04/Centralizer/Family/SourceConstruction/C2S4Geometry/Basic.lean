module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Basic
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylow

/-!
# Residual coordinates for the C₂ × S₄ branch of 15.4.13

A two-perfect T-invariant subgroup X is normal in XT, with two-group quotient,
so it is exactly the two-residual of XT. This verifies the identification that
is needed before transporting the model's alternating subgroup to X. The
actual Sylow T restricts to XT, and the known model theorem identifies T with
C₂ × D₈. `DihedralCover` specifies the remaining local construction, retaining
its literal inclusions, core, index, and conjugacy relation in XT.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 15.4.13, printed p.1161. This module does not assert existence of the
dihedral cover or the final exclusion.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
variable {G : Type*} [Group G]

/-- T-invariance and two-perfectness identify the actual residual in XT. -/
theorem residual_eq_member (T : Sylow 2 G) (X : Subgroup G)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    pResidual 2 (X ⊔ (T : Subgroup G) : Subgroup G) =
      X.subgroupOf (X ⊔ (T : Subgroup G)) := by
  let H := X ⊔ (T : Subgroup G)
  let : (X.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le X.le_normalizer hn)
  have hperf : IsPPerfect 2 (X.subgroupOf H) :=
    hp.of_surjective (subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).symm.toMonoidHom
      (subgroupOfEquivOfLe (show X ≤ H from le_sup_left)).symm.surjective
  apply pResidual_eq_of_isPPerfect_sup (X.subgroupOf H) ((T : Subgroup G).subgroupOf H)
    hperf T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup (show X ≤ H from le_sup_left)
    (show (T : Subgroup G) ≤ H from le_sup_right)]
  exact subgroupOf_self H

/-- The embedded residual equality uses the actual subtype map of XT. -/
theorem embedded_residual_eq_member (T : Sylow 2 G) (X : Subgroup G)
    (hp : IsPPerfect 2 X) (hn : (T : Subgroup G) ≤ normalizer (X : Set G)) :
    (pResidual 2 (X ⊔ (T : Subgroup G) : Subgroup G)).map
      (X ⊔ (T : Subgroup G)).subtype = X := by
  rw [residual_eq_member T X hp hn, map_subgroupOf_eq_of_le le_sup_left]

/-- The canonical Y-family supplies precisely the perfectness and invariance used above. -/
theorem y_member_residual (T : Sylow 2 G) {X : Subgroup G} (hX : X ∈ Y (T : Subgroup G)) :
    (pResidual 2 (X ⊔ (T : Subgroup G) : Subgroup G)).map
      (X ⊔ (T : Subgroup G)).subtype = X :=
  embedded_residual_eq_member T X (YFamily.perfect hX) (YFamily.invariant hX)

/-- Restrict the given ambient Sylow to XT before applying the concrete model theorem. -/
theorem sylow_equiv [Finite G] (T : Sylow 2 G) (X : Subgroup G)
    (e : (X ⊔ (T : Subgroup G) : Subgroup G) ≃*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) :
    Nonempty (T ≃* Multiplicative (ZMod 2) × DihedralGroup 4) := by
  let hTH : (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) := le_sup_right
  obtain ⟨eT⟩ := CyclicTwoSymmetricFour.sylow_two_equiv ⟨e⟩ (T.subtype hTH)
  exact ⟨(subgroupOfEquivOfLe hTH).symm.trans eT⟩

/-- The local geometric data still to be constructed inside the actual XT model.
This is an output specification; no existence is asserted by this definition. -/
structure DihedralCover (T : Sylow 2 G) (X : Subgroup G) where
  t : T
  z : T
  R : Subgroup T
  t_order : orderOf t = 2
  t_outside_core : (t : G) ∉ (X ⊔ (T : Subgroup G)).pCoreIn 2
  z_order : orderOf z = 2
  z_mem_frattini : z ∈ frattini T
  R_eq : R.map (T : Subgroup G).subtype = zpowers (t : G) ⊔ X.pCoreIn 2
  R_index : R.index = 2
  R_equiv : Nonempty (R ≃* DihedralGroup 4)
  center_inter : center T ⊓ R = frattini T
  cover : ∀ r : T, r ∈ R → orderOf r = 2 →
    IsConj (⟨r, (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right) r.property⟩ : (X ⊔ (T : Subgroup G) : Subgroup G))
      (⟨t, (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right) t.property⟩ : (X ⊔ (T : Subgroup G) : Subgroup G)) ∨
    IsConj (⟨r, (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right) r.property⟩ : (X ⊔ (T : Subgroup G) : Subgroup G))
      (⟨z, (show (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) from le_sup_right) z.property⟩ : (X ⊔ (T : Subgroup G) : Subgroup G))

end CFSG.Quasithin.Chapter15.Section04.FamilySource.C2S4Geometry
