module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FanoGeometry
public import Theory.Representation.PSL3Two.FanoLineQuotients

/-!
# The original involution module has a dual-natural quotient

The marked Fano-line identification and the line-core quotient calculation
apply to the literal orbit-sum surjection. They give dimensions 3, 4, 6 or 7
and a surjective LT-intertwiner onto the dual of the original subgroup V,
using the same conjugation action. The orbit span here equals the source
Ve = ⟨e^L⟩ by source_involution_span_eq. The final theorem supplies the
involution from the actual nontrivial parabolic center.

This proves the module implication in 14.3.29(1), conditional on the preceding
14.3.25 seed exclusion. It does not assert Thompson normality or centerlessness.
Both seed exclusions, the Thompson argument and the remaining nonsolvable and
Goldschmidt contradictions stay with qt-d-hs-centerless-source. Final
LocalStructure assembly remains with qt-d-hs-local-structure.

Source: Aschbacher--Smith, 14.3.29(1), printed p.1002, using H.5.3,
printed pp.385--386, refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinearThree BinaryLinearThree.FanoDecomposition
open Representation.BinaryConjugacyOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 14.3.29(1), for the literal orbit module and the dual of the original V. -/
theorem source_involution_dual_quotient (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (e : G) (he : orderOf e = 2)
    (heI : e ∈ Chapter12.Section08.centerIn (F.I₂ L)) (heT : e ∈ sylowOmega T) :
    letI := chosen.elementary
    ∃ hE : IsElementaryAbelian 2 (Span (L ⊔ (T : Subgroup G)) e), letI := hE
      (Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 3 ∨
       Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 4 ∨
       Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 6 ∨
       Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 7) ∧
      ∃ r : (representation (L ⊔ (T : Subgroup G)) e).IntertwiningMap
        (elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)).dual,
        Function.Surjective r := by
  let := chosen.elementary
  obtain ⟨_, hE, _, hdim, _, _, _, _⟩ :=
    source_involution_permutation_quotient d earlier hq chosen structural alternatives F hne hseed e he heI heT
  let := hE
  obtain ⟨β, f, hf, hβ, _, E, hEq, _⟩ :=
    source_involution_fano_lines d earlier hq chosen structural alternatives F hne hseed e he heI heT
  let A := L ⊔ (T : Subgroup G)
  let R : Representation.Equiv (FanoLineQuotients.lineRepresentation.comp f)
      ((BinaryPermutation.representation (Orbit A e)).comp (permutation A e)) :=
    .mk (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) E) (by
      intro a
      apply LinearMap.ext
      intro c
      funext x
      change c ((linePerm (f a)).symm (E x)) = c (E ((permutation A e a).symm x))
      have hh := hEq a⁻¹ x
      simp only [map_inv, Equiv.Perm.inv_def] at hh
      exact congrArg c hh.symm)
  let q := (quotient A e).comp R.toIntertwiningMap
  have hq' : Function.Surjective q := (quotient_surjective A e).comp R.toLinearEquiv.surjective
  have hd : 1 < Module.finrank (ZMod 2) (Additive (Span A e)) := lt_of_lt_of_le (by decide : 1 < 3) hdim
  obtain ⟨r, hr⟩ := FanoLineQuotients.dual_quotient f hf (representation A e) q hq' hd
  let σ := elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)
  let D : Representation.Equiv (W.dual.comp f) σ.dual :=
    .mk β.dualMap (by
      intro a
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro v
      change φ (W (f a)⁻¹ (β v)) = φ (β (σ a⁻¹ v))
      rw [← map_inv, hβ])
  exact ⟨hE, FanoLineQuotients.quotient_dimensions f hf (representation A e) q hq' hd,
    D.toIntertwiningMap.comp r, D.toLinearEquiv.surjective.comp hr⟩


/-- The complete 14.3.29(1) module conclusion for a witness extracted from
 the actual contrary center; its ambient and Sylow markings are retained. -/
theorem source_contrary_dual_quotient (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    letI := chosen.elementary
    ∃ e : G, orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      ∃ hE : IsElementaryAbelian 2 (Span (L ⊔ (T : Subgroup G)) e), letI := hE
        (Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 3 ∨
         Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 4 ∨
         Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 6 ∨
         Module.finrank (ZMod 2) (Additive (Span (L ⊔ (T : Subgroup G)) e)) = 7) ∧
        ∃ r : (representation (L ⊔ (T : Subgroup G)) e).IntertwiningMap
          (elementaryRepresentation (p := 2) (F.naturalFlagAction L chosen.normalizes)).dual,
          Function.Surjective r := by
  obtain ⟨e, he, heI, heT, heU, heV⟩ :=
    source_center_involution d earlier hq chosen structural alternatives F hne hI
  exact ⟨e, he, heI, heT, heU, heV,
    source_involution_dual_quotient d earlier hq chosen structural alternatives F hne hseed e he heI heT⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
