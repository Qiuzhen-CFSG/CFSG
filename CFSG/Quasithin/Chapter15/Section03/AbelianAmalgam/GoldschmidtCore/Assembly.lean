module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.AssemblyGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.AssemblyTransport

/-!
# Four clauses of the terminal Goldschmidt construction

The genuine earlier local conclusions construct `s ∈ S − T_E`, the second
singular four-group `F = Eˢ`, the literal local products, their intrinsic
symmetric quotients, their intersection, and the maximal-local Sylow assertion.
The commutator identity of 15.3.66 puts `V` in the two-core of the generated
group. The resulting intrinsic Goldschmidt triple and the transported local
controls then instantiate the Thompson extension argument, proving the
three-prime core equals the two-core.

`exists_terminal_configuration` proves clauses (1), (3), (4), and (5) of
15.3.68 conditionally on the earlier source conclusions. Its only further
earlier-theorem witnesses are F.6.11(1), with precisely its Sylow and solvability
outputs, and the complete B.2.16 statement. The singular-line seed needed in
the Thompson argument is proved by `AssemblyGeometry`; no separate B.2.14
witness is needed in this route.

Clause (2), `V ≤ Z(O₂(G₀))`, remains with the independent centrality owner.
The printed common-core equality is false under the genuine local inputs;
this assembly uses neither it nor a replacement common-core containment.
`TerminalConfiguration.module_le_core` deliberately states only containment
in the core. This module does not assert the full numbered 15.3.68.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1152–1155, including the continuation of 15.3.68 on p.1155.
-/

public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
open LocalRelations ThompsonExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Constructed geometry and clauses (1), (3), (4), (5) of 15.3.68.
The containment in the two-core is not the still-open centrality clause (2). -/
structure TerminalConfiguration (T : Sylow 2 G) (M Y V E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M) : Prop where
  line_le : F ≤ V
  seed_le : centralInvolutions T ≤ F
  line_card : Nat.card F = 4
  line_four : Nonempty (F ≃* Multiplicative (ZMod 2 × ZMod 2))
  line_singular : ∀ f : F, d.singular ⟨f, line_le f.property⟩
  line_ne : F ≠ E
  lineT_eq : lineT (T : Subgroup G) F = lineT (T : Subgroup G) E
  product_Y : (Y : Set G) = (lineY Y E : Set G) * (lineY Y F : Set G) *
    (twoCoreAmbient Y : Set G)
  relative_normal : ((lineY Y E).subgroupOf (Y ⊔ lineT (T : Subgroup G) E)).Normal
  product_first : (firstAmalgamGroup Y (T : Subgroup G) E F : Set G) =
    (lineY Y F : Set G) * (lineT (T : Subgroup G) E : Set G)
  product_second : (secondAmalgamGroup (T : Subgroup G) E : Set G) =
    (lineX E : Set G) * (lineT (T : Subgroup G) E : Set G)
  quotient_first : Nonempty ((firstAmalgamGroup Y (T : Subgroup G) E F ⧸
    pCore 2 (firstAmalgamGroup Y (T : Subgroup G) E F)) ≃* Equiv.Perm (Fin 3))
  quotient_second : Nonempty ((secondAmalgamGroup (T : Subgroup G) E ⧸
    pCore 2 (secondAmalgamGroup (T : Subgroup G) E)) ≃* Equiv.Perm (Fin 3))
  intersection : firstAmalgamGroup Y (T : Subgroup G) E F ⊓
    secondAmalgamGroup (T : Subgroup G) E = lineT (T : Subgroup G) E
  normalizes_lineY : amalgamGroup Y (T : Subgroup G) E F ≤ normalizer (lineY Y E : Set G)
  module_le_core : V ≤ twoCoreAmbient (amalgamGroup Y (T : Subgroup G) E F)
  maximalLocal_sylow : ∀ K ∈ Theory.GroupTheory.maximalTwoLocalOvergroups
    (amalgamGroup Y (T : Subgroup G) E F), IsSylowSubgroupIn (lineT (T : Subgroup G) E) K
  sylow : IsSylowSubgroupIn (lineT (T : Subgroup G) E) (amalgamGroup Y (T : Subgroup G) E F)
  goldschmidt : ChapterF.IsGoldschmidtTriple
    ((firstAmalgamGroup Y (T : Subgroup G) E F).subgroupOf (amalgamGroup Y (T : Subgroup G) E F))
    ((secondAmalgamGroup (T : Subgroup G) E).subgroupOf (amalgamGroup Y (T : Subgroup G) E F))
  core_eq : pPrimeCore 3 (amalgamGroup Y (T : Subgroup G) E F) =
    pCore 2 (amalgamGroup Y (T : Subgroup G) E F)
  seed_span : F = conjugateSpan (lineY Y F) (centralInvolutions T)
  thompson_normal : ((elementaryAbelianMaxJ (lineT (T : Subgroup G) E)).subgroupOf
    (firstAmalgamGroup Y (T : Subgroup G) E F)).Normal
  thompson_normalizer : normalizer (elementaryAbelianMaxJ (lineT (T : Subgroup G) E) : Set G) ≤ M
  support_M : ∀ p : ℕ, p.Prime → p ∣ Nat.card M → p = 2 ∨ p = 3
  support_centralizer : ∀ p : ℕ, p.Prime → p ∣ Nat.card (centralizer (F : Set G)) → p = 2 ∨ p = 3
  extension : ∃ U : Sylow 2 (amalgamGroup Y (T : Subgroup G) E F),
    (U : Subgroup (amalgamGroup Y (T : Subgroup G) E F)).map
        (amalgamGroup Y (T : Subgroup G) E F).subtype = lineT (T : Subgroup G) E ∧
      ExtensionResult U ((lineY Y F).subgroupOf (amalgamGroup Y (T : Subgroup G) E F))
        (F.subgroupOf (amalgamGroup Y (T : Subgroup G) E F))

/-- The four noncentrality clauses, constructed from the earlier local source
conclusions and the explicit F.6.11(1) and B.2.16 witnesses. -/
theorem exists_terminal_configuration
    (T : Sylow 2 G) (M Mc Y V R V₁ E : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hM : M = normalizer (V : Set G))
    (hY : Y = residualY M Mc)
    (hR : R = centralizer (V : Set G))
    (hRT : R = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hMproduct : (M : Set G) = (Y : Set G) * (T : Set G))
    (hV₁ : V₁ ≤ V) (hV₁card : Nat.card V₁ = 4)
    (hdefinite : ∀ v : V₁, v ≠ 1 → ¬ d.singular ⟨v, hV₁ v.property⟩)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hfour : Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)))
    (hEsingular : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (hZcard : Nat.card (centralInvolutions T) = 2)
    (hZE : centralInvolutions T ≤ E)
    (hS : (planeStabilizer T V₁).relIndex (T : Subgroup G) = 2)
    (hD : (lineT (T : Subgroup G) E).relIndex (T : Subgroup G) = 2)
    (hSD : planeStabilizer T V₁ ≠ lineT (T : Subgroup G) E)
    (himage : actionImage d Y = pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hcore : twoCoreAmbient (Y ⊔ (T : Subgroup G)) = R)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 9 ∨ Nat.card (Y ⧸ pCore 2 Y) = 27)
    (hfirst : Nonempty (((lineY Y E ⊔ lineT (T : Subgroup G) E : Subgroup G) ⧸
      pCore 2 (lineY Y E ⊔ lineT (T : Subgroup G) E : Subgroup G)) ≃*
        Equiv.Perm (Fin 3)))
    (hSylow : IsSylowSubgroupIn (lineT (T : Subgroup G) E) (lineNormalizer E))
    (hBaumann : ChapterB.baumann (lineT (T : Subgroup G) E) ≤ R)
    (hcontrol : (ChapterB.baumann (lineT (T : Subgroup G) E)).characteristicNormalizerClosure ≤ M)
    (hYN : ((lineY Y E).subgroupOf (lineNormalizer E)).Normal)
    (hYEq : Nonempty ((lineY Y E ⧸ pCore 2 (lineY Y E)) ≃* Multiplicative (ZMod 3)))
    (hXq : Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)))
    (hGEq : Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hME : lineM M E = lineY Y E ⊔ lineT (T : Subgroup G) E)
    (hGEproduct : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT (T : Subgroup G) E : Set G))
    (hcomm : lineX E = ⁅lineX E, elementaryAbelianMaxJ R⁆)
    (hmaximal : IsMaximalTwoLocal M) (hXoutside : ¬ lineX E ≤ M)
    (hVcomm : ⁅V, lineY Y E⁆ = V)
    (hF611 : ∀ (H : Subgroup G) (A B : Subgroup H), ChapterF.IsGoldschmidtTriple A B →
      IsSylowSubgroupIn (pCore 2 H) (pPrimeCore 3 H) ∧ Group.IsSolvable (pPrimeCore 3 H))
    (hB216 : Chapter1.RadicalNormalizers.ThompsonSource.TheoremB216.{u}) :
    ∃ s ∈ planeStabilizer T V₁, s ∉ lineT (T : Subgroup G) E ∧
      lineY Y (otherLine E s) = otherLine (lineY Y E) s ∧
      TerminalConfiguration T M Y V E (otherLine E s) d := by
  obtain ⟨s, hs, hsE, hFV, hZF, hFcard, hFfour, hFsingular, hFE, hTF,
    hYF, hproduct, _himageComm, hlocalNormal, hprod1, hprod2, hquot1, hquot2,
    hinter, _hNM, _hgenerate, _hgenerateAll, _hN, hNJ, hJnormal,
    hMsupport, hFsupport, hmaxSylow⟩ :=
    exists_terminal_local_relations T M Mc Y V R V₁ E d hM hY hR hRT hMproduct
      hV₁ hV₁card hdefinite hEV hEcard hfour hEsingular hZcard hZE hS hD hSD himage
      hcore hYquot hfirst hSylow hBaumann hcontrol hYN hYEq hXq hGEq hME hGEproduct
      hcomm hmaximal hXoutside
  let F := otherLine E s
  let H := amalgamGroup Y (T : Subgroup G) E F
  have hYM : Y ≤ M := by
    rw [hY]
    exact Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hVC : V ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff_isMulCommutative.mpr
    exact ⟨⟨fun a b => d.coordinates.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hCT : centralizer (V : Set G) ≤ (T : Subgroup G) :=
    hR.symm.le.trans (hRT.le.trans inf_le_left)
  have hVT : V ≤ lineT (T : Subgroup G) E :=
    le_inf (hVC.trans hCT)
      (hVC.trans ((centralizer_le hEV).trans (centralizer_le_normalizer (E : Set G))))
  have hLocalN : Y ⊔ lineT (T : Subgroup G) E ≤ normalizer (lineY Y E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans
      (inf_le_left.trans le_sup_left))).mp hlocalNormal
  have hEN : lineNormalizer E ≤ normalizer (lineY Y E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((lineY_le Y E).trans inf_le_right)).mp hYN
  have hVQ : V ≤ twoCoreAmbient H := amalgam_module_le_core Y (T : Subgroup G) V E F
    (T.isPGroup'.to_le (hVT.trans inf_le_left)) hVT (hYM.trans d.normalizes)
    hLocalN hEN hVcomm
  have hVne : V ≠ ⊥ := by
    intro hv
    have he := eq_bot_mono hEV hv
    have hc := hEcard
    rw [he, card_bot] at hc
    omega
  have hTH : IsSylowSubgroupIn (lineT (T : Subgroup G) E) H :=
    amalgam_sylow_of_maximalLocals Y (T : Subgroup G) V E F hVne hVQ hmaxSylow
  have hGold := goldschmidtTriple_of_local_quotients
    (firstAmalgamGroup Y (T : Subgroup G) E F) (secondAmalgamGroup (T : Subgroup G) E)
    (lineT (T : Subgroup G) E) hquot1 hquot2 hinter hTH
  have hZne : centralInvolutions T ≠ ⊥ :=
    (one_lt_card_iff_ne_bot _).mp (by rw [hZcard]; decide)
  have hFspan := singular_line_eq_span V M Y F (centralInvolutions T)
    d hYM hFV hFcard hFsingular himage hZne hZF
  have hJB : elementaryAbelianMaxJ (lineT (T : Subgroup G) E) ≤
      ChapterB.baumann (lineT (T : Subgroup G) E) := by
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    intro j hj
    apply mem_centralizer_iff.mpr
    intro w hw
    obtain ⟨wJ, hwJ, rfl⟩ := hw
    obtain ⟨wZ, _, rfl⟩ := hwJ
    exact congrArg Subtype.val ((mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm
  have hJF : elementaryAbelianMaxJ (lineT (T : Subgroup G) E) ≤ centralizer (F : Set G) :=
    hJB.trans (hBaumann.trans (hR.le.trans (centralizer_le hFV)))
  have hYJN : lineY Y F ≤ normalizer (elementaryAbelianMaxJ (lineT (T : Subgroup G) E) : Set G) :=
    le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
      ((sSup_le fun _ hA => hA.1).trans
        (show lineT (T : Subgroup G) E ≤ firstAmalgamGroup Y (T : Subgroup G) E F from
          le_sup_right))).mp hJnormal)
  have hZomega : centralInvolutions T ≤ omegaOneCenterAmbient (lineT (T : Subgroup G) E) := by
    intro z hz
    obtain ⟨_, hp, hc⟩ := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    exact (mem_omegaOneCenterAmbient_iff _ z).mpr
      ⟨hVT (hEV (hZE hz)), hp, fun t ht => hc t ht.1⟩
  obtain ⟨U, hU⟩ := hTH
  have hext := extension_of_ambient_data H (lineT (T : Subgroup G) E) V R (lineY Y F)
    (centralInvolutions T) F M (hF611 H) hB216 _ _ hGold U hU
    hVQ hR.ge (T.isPGroup'.to_le (hRT.le.trans inf_le_left))
    (le_sup_left.trans le_sup_left) (hFV.trans (hVT.trans (le_sup_right.trans le_sup_left)))
    hYJN hZomega hFspan hJF hFsupport hMsupport hNJ
  refine ⟨s, hs, hsE, hYF, ?_⟩
  exact ⟨hFV, hZF, hFcard, hFfour, hFsingular, hFE, hTF, hproduct, hlocalNormal,
    hprod1, hprod2, hquot1, hquot2, hinter,
    amalgam_normalizes_lineY Y (T : Subgroup G) E F hLocalN hEN,
    hVQ, hmaxSylow, ⟨U, hU⟩, hGold, hext.core_eq, hFspan, hJnormal, hNJ,
    hMsupport, hFsupport, U, hU, hext⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
