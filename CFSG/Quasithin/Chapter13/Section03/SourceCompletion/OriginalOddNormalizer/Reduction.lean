module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalGeometry
public import CFSG.Quasithin.Chapter4.Section04.OddActorQuotient
public import CFSG.Quasithin.Chapter4.Section04.OddActorOddCore
public import CFSG.Quasithin.Chapter4.Section04.OddActorReduction

/-!
# The terminal prime actor in the original unitary odd-local argument

The escaping actor constructed from the completed unitary geometry has a
proper quasithin K-group normalizer. The original chosen module centralizes
its odd core. The already proved N(V) bound puts that odd core in N(L),
without assuming uniqueness for the smaller residual L_A.

Restriction of the original quotient map also identifies L_A/O₂(L_A)
with the same binary G₂ derived group. The final theorem applies all these
facts to the actual Hall actor, retaining the rank-three centralizer bound.
The remaining pushing-up uniqueness and component inspection belong to
qt-d-13316-source. This is a reduction, not the conclusion of 4.4.3 or 13.3.16.

Source: Aschbacher--Smith 4.4.5--8, pp.620--621, and 13.3.20, p.896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterE Chapter4 Chapter4.Section04
open Chapter12.Section02 OriginalPlaneCentralizers
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual unitary prime actor has the original residual quotient,
and its odd core is controlled without a residual-uniqueness premise. -/
theorem unitary_original_prime_actor_reduction
    {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (s : Context T L V) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (A : Subgroup G) (hcard : Nat.card A = p)
    (hAN : A ≤ normalizer (L : Set G))
    (hAV : A ≤ centralizer (V : Set G)) (hAL : ⁅A,L⁆ ≤ L.pCoreIn 2) :
    normalizer (A : Set G) ≠ ⊤ ∧ IsQuasithin (normalizer (A : Set G)) ∧
      IsKGroup KnownSimple.IsKnownSimple (normalizer (A : Set G)) ∧
      ⁅V,(pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (L : Set G) ∧
      ∃ e : (oddActorResidual L A ⧸ pCore 2 (oddActorResidual L A)) ≃*
          Atlas.G2.Natural.BinaryNormalizer.Derived,
        ∀ x : oddActorResidual L A,
          e (QuotientGroup.mk' (pCore 2 (oddActorResidual L A)) x) =
            s.quotient (QuotientGroup.mk' (pCore 2 L)
              ⟨x.val,((oddActorResidual_le L A).trans inf_le_left) x.property⟩) := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsCyclic A := isCyclic_of_prime_card hcard
  have hne : A ≠ ⊥ := A.one_lt_card_iff_ne_bot.mp (by omega)
  have ho : Odd (Nat.card A) := by
    rw [hcard]
    exact hp.odd_of_ne_two (by omega)
  have h12 := (unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient).toHypothesis1221
  have hV : Nat.card V = 64 := by
    have hd : Module.finrank (ZMod 2) (Additive V) = 6 :=
      s.coordinates.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod,hd] at hc
    exact hc
  obtain ⟨hn,hq,hK⟩ := oddNormalizer_properQTK s.hypothesis.qtke A hne
  have hc := chosen_oddNormalizer_centralizes_oddCore h12 s.chosen hV A hAN hAL ho hAV
  have hNV := (unitary_original_module_normalizers s.hypothesis s.maximal s.quotient
    s.chosen s.structural).2
  have hcore := (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNV)
  obtain ⟨e,he⟩ := chosen_oddActorResidual_quotient h12 s.chosen A hAN hAL ho hAV
  exact ⟨hn,hq,hK,hc,hcore,e.trans s.quotient,fun x => congrArg s.quotient (he x)⟩

/-- Apply the odd-core reduction and literal residual quotient to the actual
escaping Hall actor. All geometric inputs are proved on the original flag. -/
theorem unitary_original_terminal_prime_reduction
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
      normalizer (A : Set G) ≠ ⊤ ∧ IsQuasithin (normalizer (A : Set G)) ∧
      IsKGroup KnownSimple.IsKnownSimple (normalizer (A : Set G)) ∧
      ⁅D.V,(pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype⁆ = ⊥ ∧
      (pPrimeCore 2 (normalizer (A : Set G))).map (normalizer (A : Set G)).subtype ≤
        normalizer (D.L : Set G) ∧
      Nonempty ((oddActorResidual D.L A ⧸ pCore 2 (oddActorResidual D.L A)) ≃*
        Atlas.G2.Natural.BinaryNormalizer.Derived) := by
  have hC := (unitary_original_geometric_controls D s earlier hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull h1332 fixed five).2.2.1
  obtain ⟨H,_,_,_,p,A,hp,hp3,hcard,_,hAH,hAV,hAL,hout⟩ :=
    unitary_original_escaping_prime_actor_of_source_geometry D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five
  have hAN := hAH.trans inf_le_right
  obtain ⟨hn,hq,hK,hc,hcore,e,_⟩ := unitary_original_prime_actor_reduction s hp hp3 A hcard hAN hAV hAL
  exact ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hAL,
    fun h => hout (inf_le_right.trans h),hn,hq,hK,hc,hcore,⟨e⟩⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
