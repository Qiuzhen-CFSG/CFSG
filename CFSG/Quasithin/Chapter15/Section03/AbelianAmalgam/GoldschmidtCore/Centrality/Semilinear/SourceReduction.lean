module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceOperators
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ParabolicResidual
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.SourceRealization
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.KernelModule

/-!
# The source-correct good-or-bad module reduction

The actual character on B/O₂(B) gives a dichotomy. If its restriction to
Q=O₂(H) is trivial, the proved source kernel calculation gives Q≤C_G(V).
Otherwise the constructed fixed module, offender transfer, full conditional
F.6.18/B.5.6 comparison and Fano marking produce the doubled natural
K/O₂(K) module. The output retains the actual Sylow subgroup, index-seven
parabolic, both embedded core identities and compatible quotient maps.

The same assembly proves U=V_E and supplies the commuting conjugate and
M-normalized nontrivial elementary pair required by pushing-up. No action,
recognition, dimension, common-core or ambient-transport target is assumed.
The two complete universal classification implications and genuine preceding
source conclusions remain explicit, for their existing source owners and
the parent centrality assembly to discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.46, 15.3.50, 15.3.66–68 and the terminal argument,
printed pp.1141–1145 and 1152–1155.
-/

@[expose] public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Proved bad-branch output on the actual ambient subgroups and quotient maps.
This is an output contract, never an assumed classification or action premise. -/
def BadCharacterReduction (H B G₁ S V U M : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (s : G) : Prop :=
  let K := characterKernel H B hHB
  let N := ambientTwoCore H ⊓ K
  let P := (G₁ ⊓ K).subgroupOf K
  let Uk := U.subgroupOf K
  B ⊓ H = ambientTwoCore B ∧
  (N.subgroupOf (B ⊔ H)).Normal ∧ ambientTwoCore (B ⊔ H) = N ∧
  Chapter1.IsSylowIn 2 S (B ⊔ H) ∧
  ambientTwoCore K = N ∧
  ambientTwoCore G₁ ⊓ K = centralizer (V : Set G) ∧
  ∃ Sk : Sylow 2 K,
    (Sk : Subgroup K).map K.subtype = S ⊓ K ∧ (Sk : Subgroup K) ≤ P ∧
    IsCoatom P ∧ P.index = 7 ∧
    ((pCore 2 P).map P.subtype).map K.subtype = centralizer (V : Set G) ∧
    ∃ hnormal : Uk.Normal, letI := hnormal
      IsElementaryAbelian 2 Uk ∧ Uk ≤ pCore 2 K ∧ Uk.map K.subtype = U ∧
      H ⊓ centralizer (Uk.map K.subtype : Set G) = (pCore 2 K).map K.subtype ∧
      ∃ m : (H ⧸ pCore 2 H) ≃* Matrix.PSL3Two.SL,
        (G₁.subgroupOf H).map (m.toMonoidHom.comp (QuotientGroup.mk' _)) =
          Matrix.PSL3Two.lineParabolicSL ∧
        ∃ eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL,
          (∀ k : K, eK (QuotientGroup.mk' _ k) =
            m (QuotientGroup.mk' (pCore 2 H) (inclusion (map_subtype_le _) k))) ∧
          ∃ eU : Uk ≃* Multiplicative (Fin 2 → BinaryLinearThree.Vector),
            (∀ (k : K) (u : Uk), (eU (MulAut.conjNormal k u)).toAdd =
              fun j => Matrix.mulVec (eK (QuotientGroup.mk' _ k)).val ((eU u).toAdd j)) ∧
            otherLine U s ≤ centralizer (V : Set G) ∧ ⁅otherLine U s,U⁆ = ⊥ ∧
            IsElementaryAbelian 2 (U ⊔ otherLine U s : Subgroup G) ∧
            U ⊔ otherLine U s ≠ ⊥ ∧
            M ≤ normalizer ((U ⊔ otherLine U s : Subgroup G) : Set G)

/-- The genuine source good-or-bad module reduction, including the compatible
intrinsic doubled module and the ambient pair needed by the exclusion owner. -/
theorem terminal_good_or_bad_module {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (sourceF : Recognition.FSource.ClassificationInput κ)
    (sourceB : GeneralClassificationInput.{u,u} κ)
    (T : Sylow 2 G) (M Mc Y V E F : Subgroup G) [IsElementaryAbelian 2 V]
    (d : OrthogonalFourBinary.NaturalAction V M)
    (c : TerminalConfiguration T M Y V E F d)
    (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hEV : E ≤ V) (hEcard : Nat.card E = 4)
    (hE : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (hZE : centralInvolutions T ≤ E) (hZcard : Nat.card (centralInvolutions T) = 2)
    (himage : LocalRelations.actionImage d Y =
      pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup)
    (hYcore : twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (h66F : twoCoreAmbient (firstAmalgamGroup Y T E F) =
      firstAmalgamGroup Y T E F ⊓ centralizer (F : Set G))
    (hc : Nat.card (lineY Y E ⧸ localTwoCore (lineY Y E)) = 3)
    (hXM : ¬ lineX E ≤ M)
    (hXJ : lineX E = ⁅lineX E,elementaryAbelianMaxJ (lineT T E)⁆)
    (hY : Y = residualY M Mc)
    (hMproduct : (M : Set G) = (Y : Set G) * (T : Set G))
    (hindex : (lineT T E).relIndex (T : Subgroup G) = 2)
    (hTMc : (T : Subgroup G) ≤ Mc)
    (h46 : ∀ g : G, g ∉ M → ∀ v : V,
      (v : G) ∈ V.map (MulAut.conj g).toMonoidHom → d.singular v)
    (hGEproduct : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT T E : Set G))
    (hVE : lineV V E ≤ conjugateSpanBy V Mc)
    [IsMulCommutative (conjugateSpanBy V Mc)]
    (s : G) (hs : s ∈ (T : Subgroup G)) (hsE : s ∉ lineT T E) :
    ambientTwoCore (amalgamGroup Y T E F) ≤ centralizer (V : Set G) ∨
      (conjugateSpanBy V (amalgamGroup Y T E F) = lineV V E ∧
       BadCharacterReduction (amalgamGroup Y T E F) (lineY Y E)
         (firstAmalgamGroup Y T E F) (lineT T E) V
         (conjugateSpanBy V (amalgamGroup Y T E F)) M c.normalizes_lineY s) := by
  let H := amalgamGroup Y T E F
  let B := lineY Y E
  let U := conjugateSpanBy V H
  let K := characterKernel H B c.normalizes_lineY
  let P := (firstAmalgamGroup Y T E F ⊓ K).subgroupOf K
  have hZ : centralInvolutions T ≠ ⊥ := by
    intro he
    rw [he] at hZcard
    norm_num at hZcard
  obtain ⟨h0Q,h0U,hlocal,hN⟩ := terminal_kernel_reduction T M Y V E F d c
    hYM hEV hEcard hE hZE hZ himage hYcore hCT h66F
  by_cases hbad : ∃ q : ambientTwoCore H,
      quotientAction H B c.normalizes_lineY ⟨q.1,pCoreIn_le 2 H q.2⟩ ≠ 1
  · right
    obtain ⟨hU,hWZ,hWcard,hWX,m,hS,h₁,h₂,Φ,hΦ,hUVE,hUMc,hpair⟩ :=
      terminal_bad_character_ambient hG sourceF sourceB T M Mc Y V E F d c hTM hYM
        hEV hEcard hE hZE hZcard himage hYcore hCT h66F hc hXM hXJ hY hMproduct
        hindex hTMc h46 hGEproduct hVE hbad
    let := hU
    refine ⟨hUVE,?_⟩
    obtain ⟨hnormal,hUk,hUkcore,hmap,hC,eK,heK,eU,heU⟩ := intrinsic_kernel_double H B U
      c.normalizes_lineY (le_normalizer_conjugateSpanBy V H) hc hbad
      (span_le_core Y T V E F c.module_le_core) hN m Φ hΦ
    let := hnormal
    have hmax := kernel_marked_parabolic H B (firstAmalgamGroup Y T E F)
      c.normalizes_lineY hc hbad ((core_le_lineT Y T E F c.sylow).trans le_sup_right)
      m (by rw [map_map]; exact h₁)
    have hR := nested_first_core H B (firstAmalgamGroup Y T E F) (centralizer (V : Set G))
      c.normalizes_lineY le_sup_left hlocal
    have hBV : B ≤ normalizer (V : Set G) :=
      (lineY_le Y E).trans (inf_le_left.trans (hYM.trans d.normalizes))
    have hVc : V = ⁅V,B⁆ := Orthogonal.lineY_commutator d Y E hYM hEV hEcard hE himage
    have hVB : V ≤ B := hVc.le.trans (le_normalizer_iff_commutator_le_right.mp
      ((c.module_le_core.trans (pCoreIn_le 2 H)).trans c.normalizes_lineY))
    have hV0 : V ≤ ambientTwoCore B :=
      le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVB hBV
    have hVne : V ≠ ⊥ := fun he => hZ (bot_unique ((hZE.trans hEV).trans he.le))
    obtain ⟨hinter,hnBH,hcoreBH,hSylBH,hcoreK,_hfirst,hSylK,_hr⟩ :=
      ExternalQuotient.terminal_external_reduction hG H B (firstAmalgamGroup Y T E F)
        (lineT T E) V c.normalizes_lineY hc h0Q h0U hN hVne hV0
        le_sup_left hlocal c.sylow hbad
    obtain ⟨Sk,hSk⟩ := hSylK
    have hSkP : (Sk : Subgroup K) ≤ P := by
      intro k hk
      have hm : (k : G) ∈ lineT T E ⊓ K := hSk ▸ mem_map_of_mem K.subtype hk
      exact ⟨Subgroup.mem_sup_right hm.1,hm.2⟩
    obtain ⟨_hUs,hUsR,hcomm,hA,hne,hMA⟩ := hpair s hs hsE
    exact ⟨hinter,hnBH,hcoreBH,hSylBH,hcoreK,hlocal,Sk,hSk,hSkP,hmax.1,hmax.2,hR,
      hnormal,hUk,hUkcore,hmap,hC,m,h₁,eK,heK,eU,heU,hUsR,hcomm,hA,hne,hMA⟩
  · left
    exact trivial_character_core_centralizes H B V c.normalizes_lineY hN
      (fun q => not_not.mp (fun hq => hbad ⟨q,hq⟩))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
