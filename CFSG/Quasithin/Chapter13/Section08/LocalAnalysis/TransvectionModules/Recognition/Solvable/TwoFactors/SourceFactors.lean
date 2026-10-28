module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Solvable.TwoFactors.Cubic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.Notation

/-!
# Source quotient adapters for the two-factor argument

The source subgroup L₁ is literally O²(N_LT(V₁)), using the definitions
from Notation 13.2.1. It is two-perfect, as is its image in H/O₂(H), so
it fixes each of the two actual factors. The earlier seed identity
V₃=[V₃,L₁] proves that this image is nontrivial.

The Sylow obstruction is applied to the literal star image of the original
Sylow subgroup and to the literal U_H/V₁ carrier. It still requires a cubic
subgroup inside the transvection closure. Placing L₁* in that closure by the
three-rank bound, and constructing its invariant cubic subgroup from the
marked A₆ or covered-A₆ geometry, remain source-assembly obligations.
No later component-existence or solvable-exclusion theorem is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, printed p.877, and proof of 13.8.5, p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors
open ChapterB
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]

omit [Finite G] in
/-- A two-perfect source subgroup remains two-perfect in the literal star quotient. -/
theorem starImage_isPPerfect (H B : Subgroup G) (hBH : B ≤ H) (hB : IsPPerfect 2 B) :
    IsPPerfect 2 (Source.starImage H B) := by
  let e := (subgroupOfEquivOfLe hBH).symm
  have he : IsPPerfect 2 (B.subgroupOf H) := hB.of_surjective e.toMonoidHom e.surjective
  exact he.of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (B.subgroupOf H))
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)

/-- The actual L₁=O²(N_LT(V₁)) fixes each factor in the two-factor branch. -/
theorem source_one_normalizes_factors (L T V₁ G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (ρ : Representation (ZMod 2) (Source.Hstar H) E) (t : Source.Hstar H)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : d.count = 2) (i : Fin d.count) :
    Source.starImage H (one L T V₁) ≤ normalizer (ambientFactor t d i : Set (Source.Hstar H)) := by
  apply twoPerfect_normalizes_factors t d hc (factorAction t d hJ hc)
  apply starImage_isPPerfect H (one L T V₁) (le_sup_left.trans hH.1.2)
  exact isPPerfect_embedded_pResidual 2 (parabolic L T V₁)

/-- The obstruction uses the original Sylow subgroup and its literal quotient
image. Its invariant cubic witness remains a geometric obligation. -/
theorem source_no_invariant_cubic (T : Sylow 2 G) (H L₁ G₁ M V₃ V₁ : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (t : Source.Hstar H) (ht : IsTransvection ρ t)
    (d : SolvableFFFactors (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype))
    (hJ : offenderSubgroup (ρ.comp (normalClosure ({t} : Set (Source.Hstar H))).subtype) = ⊤)
    (hc : d.count = 2) (C : Subgroup (Source.Hstar H))
    (hCK : C ≤ normalClosure ({t} : Set (Source.Hstar H)))
    (hC : Nat.card C = 3)
    (hTC : Source.starImage H T ≤ normalizer (C : Set (Source.Hstar H))) : False :=
  no_invariant_cubic t ht d hJ hc (sourceSylow T H (le_sup_right.trans hH.1.2)) C hCK hC hTC

omit [Finite G] in
/-- The earlier source generation V₃=[V₃,L₁] and nonzero seed imply that
L₁* is nontrivial; this is not an additional local-image hypothesis. -/
theorem source_starImage_ne_bot (H L₁ V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hL : L₁ ≤ H)
    (hgen : V₃ = ⁅V₃, L₁⁆) (hseed : ¬ V₃ ≤ V₁) : Source.starImage H L₁ ≠ ⊥ := by
  intro he
  have hb : subspaceCommutator ρ ⊤ (Source.starImage H L₁) = ⊥ := by
    apply (subspaceCommutator_eq_bot_iff _ _ _).mpr
    rw [he, fixedSpace_bot]
  apply hseed
  intro v hv
  have hm := seed_mem_commutator ρ hρ L₁ hL hgen ⟨v, hv⟩
  rw [hb, Submodule.mem_bot] at hm
  exact (QuotientGroup.eq_one_iff
    (N := V₁.subgroupOf (Source.UH H V₃))
    (⟨v, le_conjugateSpanBy V₃ H hv⟩ : Source.UH H V₃)).mp hm

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Solvable.TwoFactors

end
