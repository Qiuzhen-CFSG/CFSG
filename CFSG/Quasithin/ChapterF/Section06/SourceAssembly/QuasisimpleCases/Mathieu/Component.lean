module

public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SupercriticalAction
public import Theory.Mathieu.M12.ValueBoundParabolics.ComponentReduction
public import Theory.Mathieu.M12.ValueBoundParabolics.CentralCovers
public import Theory.Mathieu.M12.ValueBoundParabolics.Ambient
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Amalgam

/-!
# The actual Mathieu component and ambient group in F.6.18

The original quotient by O₃′ has trivial two-core. The central-cover theorem
therefore removes the center of a quasisimple residual whose central quotient
is M₁₂. Faithful conjugation on the generalized Fitting subgroup identifies
the ambient group with M₁₂ or its full automorphism group. The literal ambient
Sylow order distinguishes these two possibilities.

The central-quotient identification is the Mathieu branch of the separate
Theorem C and marked-amalgam sieve. No local extension data are used to infer
this identification. Source: Aschbacher–Smith, F.6.18(12–13), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu
open Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

/-- The original O₃′ quotient kills the center of its actual Mathieu residual. -/
theorem residual_equiv_of_central_quotient
    (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hq : IsQuasisimple (pResidual 2 G))
    (j : ((pResidual 2 G) ⧸ center (pResidual 2 G)) ≃* M12) :
    Nonempty (pResidual 2 G ≃* M12) := by
  let : IsQuasisimple (pResidual 2 G) := hq
  have hcore := Noncyclic.twoCore_eq_bot_of_primeToThreeCore_eq_bot
    (Noncyclic.primeToThreeCore_eq_bot_of_quotient e)
  have hz := CentralCovers.center_eq_bot
    (pCore_eq_bot_of_normal 2 hcore (pResidual 2 G)) j
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hz.symm)).trans j⟩

/-- The two actual ambient models above the Mathieu central quotient. -/
theorem ambient_models_of_central_quotient
    (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (j : ((pResidual 2 G) ⧸ center (pResidual 2 G)) ≃* M12) :
    Nonempty (pResidual 2 G ≃* M12) ∧
      ((pResidual 2 G = ⊤ ∧ Nonempty (G ≃* M12)) ∨
        Nonempty (G ≃* MulAut M12)) := by
  obtain ⟨jL⟩ := residual_equiv_of_central_quotient e hq j
  let : IsQuasisimple (pResidual 2 G) := hq
  let : IsSimpleGroup M12 := m12_isSimpleGroup
  let : IsSimpleGroup (pResidual 2 G) := jL.isSimpleGroup
  have hc := centralizer_eq_bot_of_simple_generalizedFitting
    (pResidual 2 G) hFstar.symm
  refine ⟨⟨jL⟩, ?_⟩
  rcases Ambient.ambient_equiv_alternatives (pResidual 2 G) hc jL with
    hinner | ⟨jG, _⟩
  · exact .inl hinner
  · exact .inr ⟨jG.trans M12ExceptionalExtension.automorphismEquiv⟩

private theorem sylow_card_of_m12_equiv (T : Sylow 2 G) (j : G ≃* M12) :
    Nat.card T = 64 := by
  have h := T.card_eq_multiplicity
  rw [Nat.card_congr j.toEquiv, m12_order] at h
  exact h.trans (by decide +kernel)

private theorem sylow_card_of_aut_m12_equiv (T : Sylow 2 G)
    (j : G ≃* MulAut M12) : Nat.card T = 128 := by
  have h := T.card_eq_multiplicity
  rw [Nat.card_congr (j.trans M12ExceptionalExtension.automorphismEquiv.symm).toEquiv,
    M12ExceptionalExtension.carrier_order] at h
  exact h.trans (by decide +kernel)

/-- In the order-64 source branch, the Mathieu component is the entire group. -/
theorem ambient_m12_of_sylow_sixty_four
    (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (j : ((pResidual 2 G) ⧸ center (pResidual 2 G)) ≃* M12)
    (T : Sylow 2 G) (hT : Nat.card T = 64) :
    pResidual 2 G = ⊤ ∧ Nonempty (G ≃* M12) := by
  rcases (ambient_models_of_central_quotient e hFstar hq j).2 with hm | hm
  · exact hm
  · obtain ⟨jG⟩ := hm
    have hc := sylow_card_of_aut_m12_equiv T jG
    omega

/-- In the order-128 source branch, the full automorphism extension occurs. -/
theorem ambient_aut_m12_of_sylow_one_twenty_eight
    (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (j : ((pResidual 2 G) ⧸ center (pResidual 2 G)) ≃* M12)
    (T : Sylow 2 G) (hT : Nat.card T = 128) :
    Nonempty (generalizedFitting G ≃* M12) ∧ Nonempty (G ≃* MulAut M12) := by
  obtain ⟨⟨jL⟩, hm⟩ := ambient_models_of_central_quotient e hFstar hq j
  refine ⟨⟨(MulEquiv.subgroupCongr hFstar.symm).trans jL⟩, ?_⟩
  rcases hm with ⟨_, ⟨jG⟩⟩ | hm
  · have hc := sylow_card_of_m12_equiv T jG
    omega
  · exact hm

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
