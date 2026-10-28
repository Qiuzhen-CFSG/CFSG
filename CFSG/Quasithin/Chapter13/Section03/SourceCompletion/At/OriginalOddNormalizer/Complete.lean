module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.Complete
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.TerminalJanko
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.TerminalRudvalis

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.Complete`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open OriginalPlaneCentralizers Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source maximal-local inspection on the original prime actor.
Every quotient and inclusion belongs to the component produced from this A;
no full ambient Sylow or additional native placement is assumed. -/
theorem unitary_original_prime_normalizer_le
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (p : ℕ) (A : Subgroup G) (hp : p.Prime) (hp3 : 3 < p)
    (hcard : Nat.card A = p) (hAN : A ≤ normalizer (L : Set G))
    (hAV : A ≤ centralizer (V : Set G)) (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2)
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  classical
  by_contra hout
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic A := isCyclic_of_prime_card hcard
  have hne : A ≠ ⊥ := A.one_lt_card_iff_ne_bot.mp (by omega)
  have hodd : Odd (Nat.card A) := by
    rw [hcard]
    exact hp.odd_of_ne_two (by omega)
  obtain ⟨K,hK,_,_,_,hcore,hmodel,hV,hR,_⟩ :=
    unitary_original_component_models s A hne hAN hcomm hodd hAV hu hout
  rcases hmodel with hj | hr
  · obtain ⟨e⟩ := hj
    exact unitary_original_terminal_janko_false s A hAN hcomm hodd hAV hu
      K hK hcore hV hR e
  · obtain ⟨e⟩ := hr
    exact unitary_original_terminal_rudvalis_false s Z B U hZV hBV hUV
      hTZ hTB hTU hZ hB hU hC A hAN hcomm hodd hAV K hK hcore e hV hR

section OriginalFlag
variable (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
  (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context D.T D.L D.V)
  (earlier : Theorem12213At KnownSimple.IsKnownSimple D.T)
  (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
  (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
  (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
  (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
  (B : Subgroup G) (hBV : B ≤ D.V)
  (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
  (hHfull : D.H = normalizer (D.V₁ : Set G))
  (h1332 : Noncentrality.SupercriticalSource.Source1332OneTwo D.T)
  (fixed : OriginalFixedModule1332At D.T D.L)
  (five : OriginalAlternatingFiveModules1332At D.T D.L)

include s earlier hUV hZV hTZ hTU hZ hU hBV hTB hB hHfull h1332 fixed five

/-- The original flag discharges both the three-space centralizer bound and
residual uniqueness in the prime-order specialization of 4.4.3. -/
theorem unitary_original_primeNormalizerControl :
    UnitaryPrimeNormalizerControl D.L D.V := by
  have hC := (unitary_original_geometric_controls D s earlier hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull h1332 fixed five).2.2.1
  intro p A hp hp3 hcard hAN hAV hcomm
  have hodd : Odd (Nat.card A) := by
    rw [hcard]
    exact hp.odd_of_ne_two (by omega)
  have hu := unitary_original_oddActorResidual_unique D s earlier hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull h1332 fixed five A hAN hcomm hodd hAV
  exact unitary_original_prime_normalizer_le s D.V₁ B D.Vplus hZV hBV hUV
    hTZ hTB hTU hZ hB hU hC p A hp hp3 hcard hAN hAV hcomm hu

/-- The original 13.3.16 contradiction on its chosen flag, with every local
geometric and odd-normalizer obligation discharged. Earlier source theorems
remain explicit and are not asserted by this conditional application. -/
theorem unitary_original_false_of_source_inputs : False := by
  exact unitary_original_false_of_prime_normalizer_control D s earlier hUV hZV
    hTZ hTU hZ hU B hBV hTB hB hHfull h1332 fixed five
    (unitary_original_primeNormalizerControl D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five)

end OriginalFlag
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
