module

public import Theory.GroupTheory.PStar.Basic
public import Theory.GroupTheory.PStar.Chief
public import Theory.GroupTheory.PStar.Solvable
public import Theory.GroupTheory.PStar.Supplement
public import Theory.GroupTheory.PStar.Radical
public import Theory.GroupTheory.PStar.Extension
public import Theory.GroupTheory.PStar.RadicalActionReduction
public import Theory.GroupTheory.PStar.SylowBound

/-!
# Structural properties of p-star groups

The elementary structure consists of quotient closure, the centrality of
normal p-subgroups, the prime-to-p order of solvable p-star groups, and the
p-star property of chief residuals. Normal p-star subgroups define a
characteristic, p-perfect join. Its p-core extension has precisely that
join as its embedded p-residual.

At the prime two, the Sylow-centralizer residual theorem supplies the
action decomposition and normal-product closure. The radical is therefore
itself two-star, is monotone on normal subgroups, and is unchanged by
passing to the embedded two-residual. These unconditional radical results
are re-exported from `RadicalActionReduction`.

Finally, normal-product closure and the full two-star extension criterion
discharge both inputs of the Sylow-centralizer bound. Its proof passes
through the ambient two-residual before applying the extension criterion;
an ordinary Sylow-centralizer supplement alone is not its stronger premise.

Source: GLS II, Chapter B, Definitions 5.1 and 5.7, Lemmas 5.2--5.6,
the radical calculations of 5.8(i),(ii), and Theorem 5.9. The last bound
has target O_{2*2}, correcting the transcript's O_{2'2} as required by
its proof. All residuals here are O^p, not O^{p'}.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- GLS II 5.5 for a two-group acting on a two-star group. The earlier
Sylow-centralizer residual theorem is fully discharged. -/
theorem IsPStar.commutator_sup_fixed {A : Type*} [Group A]
    [MulDistribMulAction A G] (hG : IsPStar 2 G) (hA : IsPGroup 2 A) :
    commutatorAction A G ⊔ fixedPointSubgroup A G = ⊤ :=
  IsPStar.commutator_sup_fixed_of_centralizerResidual
    (fun _ _ _ hY N _ P => hY.isPStar_pResidual_centralizer N P) hA hG

/-- The residual refinement in GLS II 5.5, using the literal inclusion
of the intrinsic two-residual of the fixed subgroup. -/
theorem IsPStar.commutator_sup_fixedResidual {A : Type*} [Group A]
    [MulDistribMulAction A G] (hG : IsPStar 2 G) (hA : IsPGroup 2 A) :
    commutatorAction A G ⊔ (pResidual 2 (fixedPointSubgroup A G)).map
      (fixedPointSubgroup A G).subtype = ⊤ :=
  IsPStar.commutator_sup_fixedResidual_of_centralizerResidual
    (fun _ _ _ hY N _ P => hY.isPStar_pResidual_centralizer N P) hA hG

/-- Two normal two-star subgroups generating the ambient group make it
two-star, with no additional earlier-source hypothesis. -/
theorem isPStar_of_normal_sup_eq_top
    (X₁ X₂ : Subgroup G) [X₁.Normal] [X₂.Normal]
    (h₁ : IsPStar 2 X₁) (h₂ : IsPStar 2 X₂) (hgen : X₁ ⊔ X₂ = ⊤) :
    IsPStar 2 G :=
  isPStar_of_normal_sup_eq_top_of_centralizerResidual
    (fun _ _ _ hY N _ P => hY.isPStar_pResidual_centralizer N P) X₁ X₂ h₁ h₂ hgen

/-- Normal-product closure, GLS II 5.6 at the prime two. -/
theorem IsPStar.normal_sup (X₁ X₂ : Subgroup G) [X₁.Normal] [X₂.Normal]
    (h₁ : IsPStar 2 X₁) (h₂ : IsPStar 2 X₂) : IsPStar 2 (X₁ ⊔ X₂ : Subgroup G) :=
  IsPStar.normal_sup_of_centralizerResidual
    (fun _ _ _ hY N _ P => hY.isPStar_pResidual_centralizer N P) X₁ X₂ h₁ h₂

end Theory.GroupTheory

namespace Subgroup
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The corrected GLS II 5.9 bound at the prime two. Both normal-product
closure and the full extension criterion are supplied by proved theorems. -/
theorem centralizer_sylow_twoStarPCore_le_self
    (P : Sylow 2 (pStarPCore 2 G)) :
    centralizer ((P : Subgroup (pStarPCore 2 G)).map (pStarPCore 2 G).subtype : Set G) ≤
      pStarPCore 2 G := by
  apply centralizer_sylow_twoStarPCore_le
    (fun _ _ _ X₁ X₂ hN₁ hN₂ h₁ h₂ => ?_)
    (fun _ _ _ N _ P hquot hres hgen =>
      isPStar_pResidual_of_extension N P hquot hres hgen) P
  let : X₁.Normal := hN₁
  let : X₂.Normal := hN₂
  exact IsPStar.normal_sup X₁ X₂ h₁ h₂

end Subgroup
