module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalGeometry

/-!
# The original unitary module has commuting intersecting conjugates

The completed plane and noncentrality results give the rank and parabolic
bounds for the original flag. They discharge the hypotheses of the existing
point-closure proof, yielding 13.3.19(1) on the actual chosen module.

The Rudvalis central-cover exclusion consumes this ambient intersection
property. Only the earlier Structural1222 and catalogue inputs retain their
named source producers and final discharge at qt-theorem-d; no odd-normalizer
conclusion is used to prove this result.
Source: Aschbacher--Smith 13.3.17--19, printed pp.893--896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory ChapterE
open Chapter12.Section02 OriginalPlaneCentralizers
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]

section OriginalFlag
variable (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
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
  (five : OriginalAlternatingFiveModules1332At D.T D.L)

include s earlier hUV hZV hTZ hTU hZ hU hBV hTB hB hHfull h1332 fixed five

/-- Original 13.3.19(1) with its actual earlier geometry discharged. -/
theorem unitary_original_commuting_intersections :
    ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hg := unitary_original_geometric_controls D s earlier hUV hZV hTZ hTU hZ hU
    B hBV hTB hB hHfull h1332 fixed five
  have hm := hg.1
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  obtain ⟨hTV,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : IsSimpleGroup Atlas.G2.Natural.BinaryNormalizer.Derived :=
    Atlas.G2.isSimple_commutator_binary
  have hs := s.quotient.isSimpleGroup
  have hfaith : D.L ⊓ centralizer (D.V : Set G) ≤ D.L.pCoreIn 2 := by
    have hc := congrArg (map D.L.subtype) (s.chosen.centralizer_eq_core_of_simple hs)
    exact (show D.L ⊓ centralizer (D.V : Set G) = D.L.pCoreIn 2 by
      simpa only [pCoreIn,subgroupOf_map_subtype,inf_comm] using hc).le
  have huniq := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hcharL : generalizedFitting D.L = pCore 2 D.L :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo D.T
        (s.hypothesis.qtke.evenCharacteristic D.T) s.maximal.1)
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hZp : IsPGroup 2 D.V₁ := (IsElementaryAbelian.isPGroup 2 D.V).to_le hZV
  have hcharH : generalizedFitting D.H = pCore 2 D.H := by
    rw [hHfull]
    exact generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le D.T
        (s.hypothesis.qtke.evenCharacteristic D.T) ⟨D.V₁,hZn,hZp,rfl⟩ hTZ))
  have hout : ¬ D.H ≤ normalizer (D.L : Set G) := by
    rw [hHfull]
    exact unitary_original_line_escape s.hypothesis h12 earlier s.chosen
      s.actor s.coordinates s.equivariant hZV hZ
  have hres := (pResidual_eq_top_iff 2 D.L).mpr
    (Chapter1.Section02.Adequate.mem_L_isPPerfect s.maximal.1)
  have hVL := s.chosen.le_sylow.trans (le_sup_right : (D.T : Subgroup G) ≤ D.LT)
  have hred := ((s.structural G D.T D.L h12).2.2 D.V s.chosen).2.1
  have hsyl := unitary_chosen_sylow_kernel s.chosen hs hTV
  have hTI := h12.source_chosen_TI s.structural s.chosen
  have hcomm := unitary_intersection_commutator_eq_bot_of_source D s.hypothesis.qtke
    s.actor s.coordinates s.equivariant hUV hZV hTZ hTU hZ hU
    s.chosen.sylow_normalizes_component hVL hred hsyl hg.2.2.2 hNL huniq.2
    B hBV hTB hB hHfull hTI
  exact (unitary_weakClosure_of_original_module D (normalizer (D.L : Set G))
    s.actor s.coordinates s.equivariant hUV hZV hTZ hTU hZ hU hres
    s.chosen.sylow_normalizes_component hcharL hVL hred hsyl hcharH hg.2.2.2
    hNL hfaith huniq.2 hout (fun g _ hc => hcomm g hc)
    B hBV hTB hB hg.2.1 hHfull hm).2.1

end OriginalFlag
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
