module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.ComponentApplication
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.JankoLargeCenterRadical.Unconditional

/-!
# The actual terminal odd actor and its remaining component

The original flag supplies the plane-centralizer and noncentrality controls,
constructs the escaping prime actor, and discharges residual uniqueness using
the completed relative-Sylow pushing-up argument. The same actor then has a
normal component with J₄ or Rudvalis central quotient, containing the entire
chosen module and its literal fixed residual. No local action or uniqueness
callback is retained. The last sporadic odd-normalizer inspection is still
required for 13.3.16; the earlier 12.2/13.3.2 inputs belong to `qt-theorem-d`.

Source: Aschbacher--Smith 13.3.16--20, pp.893--896, applying 4.4.3, pp.619--623.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open OriginalPlaneCentralizers Chapter12.Section02
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original flag supplies every premise of the normal-component
inspection, including the formerly missing relative-Sylow uniqueness. -/
theorem unitary_original_terminal_component
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (s : Context D.T D.L D.V)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
    (fixed : OriginalFixedModule1332At D.T D.L)
    (five : OriginalAlternatingFiveModules1332At D.T D.L) :
    centralizer (D.Vplus : Set G) ≤ normalizer (D.L : Set G) ∧
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
      A ≤ normalizer (D.L : Set G) ∧ A ≤ centralizer (D.V : Set G) ∧
      ⁅A,D.L⁆ ≤ D.L.pCoreIn 2 ∧
      ¬ normalizer (A : Set G) ≤ normalizer (D.L : Set G) ∧
      UniqueMaximalOvergroup (oddActorResidual D.L A) (normalizer (D.L : Set G)) ∧
      ∃ K : Subgroup (normalizer (A : Set G)),
        IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
        ⁅K,D.V.subgroupOf (normalizer (A : Set G))⁆ = K ∧
        ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (D.L : Set G) ∧
        pCore 2 K = ⊥ ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          Nonempty (K ⧸ center K ≃* Rudvalis.Model)) ∧
        D.V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual D.L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) := by
  obtain ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,_⟩ :=
    unitary_original_terminal_prime_reduction D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic A := isCyclic_of_prime_card hcard
  have hne : A ≠ ⊥ := A.one_lt_card_iff_ne_bot.mp (by omega)
  have hodd : Odd (Nat.card A) := by
    rw [hcard]
    exact hp.odd_of_ne_two (by omega)
  have hu := unitary_original_oddActorResidual_unique D s earlier hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull h1332 fixed five A hAN hcomm hodd hAV
  exact ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,
    unitary_original_component_models s A hne hAN hcomm hodd hAV hu hout⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
