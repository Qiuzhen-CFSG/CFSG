module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalRudvalis.Exclusion

/-!
# Excluding the original terminal Rudvalis component

Remove the central cover using the original quotient map, and retain the
whole fixed residual and chosen module. The original Sylow-invariant flag
places its actual three-space in the native point-core commutator. A native
quaternion centralizes that commutator and escapes the full module normalizer,
contradicting the proved original centralizer bound.

The final application removes only the Rudvalis disjunct from the original
terminal component theorem and retains every witness, equation and earlier
source input, including residual uniqueness and the escaping mapped component.
The remaining J₄ branch and two-row assembly have their existing owners.
Source: Aschbacher--Smith 4.4.3 case (c), printed p.623, through
12.2.11(c) and 13.3.20, printed pp.798--799 and 896.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open OriginalPlaneCentralizers Chapter12.Section02
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original marked three-space centralizer excludes a Rudvalis component.
Its central covering map and the whole original residual are preserved. -/
theorem unitary_original_terminal_rudvalis_false (s : Context T L V)
    (Z B U : Subgroup G) (hZV : Z ≤ V) (hBV : B ≤ V) (hUV : U ≤ V)
    (hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hZ : Nat.card Z = 2) (hB : Nat.card B = 4) (hU : Nat.card U = 8)
    (hC : centralizer (U : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) (hcore : pCore 2 K = ⊥)
    (e : K ⧸ center K ≃* Rudvalis.Model)
    (hV : V ≤ K.map (normalizer (A : Set G)).subtype)
    (hR : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) : False := by
  obtain ⟨hz,d,hd,hRV,hRcard,hPE,hBcard,hel,hE,hNC,hUE,hUcard,hcentral,hpoints⟩ :=
    unitary_original_terminal_rudvalis_marking s U hUV hU hC A hAN hcomm hodd hAV
      K hK hcore e hV hR
  let J := K.map (normalizer (A : Set G)).subtype
  let j : J ≃* Rudvalis.Model :=
    (K.equivMapOfInjective (normalizer (A : Set G)).subtype
      (normalizer (A : Set G)).subtype_injective).symm.trans d
  have hout := unitary_terminal_native_three_escape s Z B U hZV hBV hUV hTZ hTB hTU
    hZ hB hU A hAN hcomm hodd hAV J j hV hR
  dsimp only at hNC hcentral hout
  rw [hNC] at hout
  exact hout hcentral

/-- The actual terminal actor retains every original source clause, with its
Rudvalis alternative now discharged. -/
theorem unitary_original_terminal_component_without_rudvalis
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
        Nonempty (K ⧸ center K ≃* Janko4.Model) ∧
        D.V ≤ K.map (normalizer (A : Set G)).subtype ∧
        oddActorResidual D.L A ≤ K.map (normalizer (A : Set G)).subtype ∧
        centralizer (K : Set (normalizer (A : Set G))) =
          pPrimeCore 2 (normalizer (A : Set G)) := by
  obtain ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,
    K,hK,hN,hm,houtK,hcore,hmodel,hV,hR,hcent⟩ :=
    unitary_original_terminal_component D s earlier hUV hZV hTZ hTU hZ hU
      B hBV hTB hB hHfull h1332 fixed five
  have hJ4 : Nonempty (K ⧸ center K ≃* Janko4.Model) := by
    rcases hmodel with hJ4 | hRu
    · exact hJ4
    · obtain ⟨e⟩ := hRu
      have hodd : Odd (Nat.card A) := by
        rw [hcard]
        exact hp.odd_of_ne_two (by omega)
      exact (unitary_original_terminal_rudvalis_false s D.V₁ B D.Vplus
        hZV hBV hUV hTZ hTB hTU hZ hB hU hC A hAN hcomm hodd hAV
        K hK hcore e hV hR).elim
  exact ⟨hC,p,A,hp,hp3,hcard,hAN,hAV,hcomm,hout,hu,
    K,hK,hN,hm,houtK,hcore,hJ4,hV,hR,hcent⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
