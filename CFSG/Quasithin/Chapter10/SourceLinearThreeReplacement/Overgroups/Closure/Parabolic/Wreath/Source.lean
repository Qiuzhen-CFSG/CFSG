module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Wreath.Intrinsic
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The literal wreath residual in the diagonal-parabolic argument

The actual projective-action isomorphism SL₂(2) ≃ S₃ identifies the two
wreath carriers. The intrinsic calculation then proves Xi membership for
O²(P). The embedding P → G transports its two-core and Frattini quotients,
intertwines their conjugation actions, and sends the intrinsic Sylow to T.
Thus the result concerns exactly `(pResidual 2 P).map P.subtype`.

The final application discharges the wreath premise of the published
parabolic-seed consumer. Natural-action recognition remains independent.
Source: Aschbacher--Smith Definition 1.3.1 and 10.2.4, pp.508 and 747.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open Chapter1
variable {G : Type*} [Group G] [Finite G]
/-- The independent wreath-residual calculation for every actual Sylow overgroup. -/
public theorem wreathResidualAt (T : Sylow 2 G) : WreathResidualAt T := by
  intro P hTP hP ⟨e⟩
  obtain ⟨eSL⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let ew : ParabolicWreath ≃* WreathTwoResidual.Actor :=
    RegularWreathProduct.congr eSL.symm (MulEquiv.refl _)
  have htop : (⊤ : Subgroup P) ∈ H P := by
    intro hb
    apply hP
    have hm := congrArg (Subgroup.map P.subtype) hb
    rw [map_pCoreIn_of_injective 2 _ P.subtype P.subtype_injective] at hm
    simpa only [←MonoidHom.range_eq_map,range_subtype,Subgroup.map_bot] using hm
  obtain ⟨hx,hq⟩ := Wreath.residual_mem_Xi (T.subtype hTP) htop (e.trans ew)
  constructor
  · have hx' := (mem_Xi_map_iff P.subtype P.subtype_injective).mpr hx
    change (pResidual 2 P).map P.subtype ∈ Xi G
      (((T : Subgroup G).subgroupOf P).map P.subtype) at hx'
    rwa [map_subgroupOf_eq_of_le hTP] at hx'
  · let eX := (pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective
    exact hq.of_mulEquiv (QuotientGroup.congr _ _ eX (pCore_map_iso 2 eX))

/-- Apply the intrinsic calculation to the literal diagonal-parabolic seed.
Only the independent natural-action recognition remains with its source owner. -/
public theorem parabolicSeed_of_diagonalRecognition {T : Sylow 2 G}
    (hnatural : DiagonalRecognitionAt T) : ParabolicSeedAt T :=
  parabolicSeed_of_recognition hnatural (wreathResidualAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
