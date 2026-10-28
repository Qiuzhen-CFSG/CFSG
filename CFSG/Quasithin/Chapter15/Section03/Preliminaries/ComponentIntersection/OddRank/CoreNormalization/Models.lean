module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.SpecificGroups.Janko1.Model.Certification
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Centers of the nonnormal C-component models

Every nonsolvable member of the actual four-model list in 1.2.1(3) is
centerless. We transport existing simplicity proofs through the supplied
multiplicative equivalences. Nonsolvability excludes the small parameter
`PSL₂(3)`; no extra order or simplicity certificates are requested.

This is the model fact used in the component-permutation step of 15.3.12,
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1125.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.CoreNormalization

open Subgroup
open CFSG.Quasithin.Chapter1.Section02

private theorem model_simple {G : Type*} [Group G]
    (h : NonnormalCComponentModel G) (hns : ¬ Group.IsSolvable G) :
    IsSimpleGroup G := by
  cases h with
  | linear_even n hn iso =>
    obtain ⟨F, hF, hf, hc, ⟨e⟩⟩ := iso
    let : Field F := hF
    let : Finite F := hf
    have hfour : 4 ≤ Nat.card F := by
      rw [hc]
      exact (show 4 = 2 ^ 2 from rfl).le.trans (Nat.pow_le_pow_right (by decide) hn)
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hfour
    exact e.isSimpleGroup
  | linear_prime p hp ho iso =>
    obtain ⟨F, hF, hf, hc, ⟨e⟩⟩ := iso
    let : Field F := hF
    let : Finite F := hf
    have hnsF : ¬ Group.IsSolvable (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
      intro hs
      let := hs
      exact hns (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
    have hgt := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hc ▸ ho) hnsF
    let := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hgt
    exact e.isSimpleGroup
  | suzuki m hm iso =>
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    exact iso.some.isSimpleGroup
  | janko iso => exact iso.some.isSimpleGroup

/-- The nonnormal alternatives of 1.2.1(3) have trivial center whenever
nonsolvable, as is the actual two-core quotient of a C-component. -/
theorem nonnormalModel_center_eq_bot {G : Type*} [Group G]
    (h : NonnormalCComponentModel G) (hns : ¬ Group.IsSolvable G) :
    center G = ⊥ := by
  let := model_simple h hns
  rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply hns
    apply Group.isSolvable_of_comm
    intro a b
    exact mem_center_iff.mp (h.symm ▸ mem_top b) a

end CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.CoreNormalization
