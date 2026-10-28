module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullWeightComparison
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CommutingAction
public import Theory.GroupTheory.PResidual.NormalClosureCover

/-!
# The fixed line in the product alternative's moved module

For the original pair P,L₂T, the product commutator bound makes O²(P)
normal in their join. Its two-core therefore acts trivially on the reduced
orbit of Ω₁Z(T). The proved commuting-action theorem gives mutual residual
normalization. Consequently the P-orbit of C_V(L) is centralized by L₂.
Its P-fixed part is trivial: a nonidentity fixed element would put P in
C_G(C_V(L))=N_G(L), contrary to escape.

Sylow averaging now makes this entire fixed-line orbit moved. The normal
residual and its Sylow supplement identify it with [C_V(L),O²(P)]. Thus
C_V(L) ≤ [Ω₁Z(T),O²(P)] ≤ [⟨Ω₁Z(T)^K⟩,K], with the final containment
using the same recognized C_G(z)=KT. The application constructs the actual
original pair in both the linear-three and ordinary A₆ rows, discharges
all its applicability premises, and retains the existing weight-four and
Thompson-normalizer alternatives.

This establishes the fixed-line placement in 13.4.10(8i) and the product
case's commutator placement used in 13.4.14(1). The weight of that line
inside a five-dimensional K-module, the linear module alternatives,
the P₂/P₄ comparison and the later commutator/graph assembly remain.
The earlier plane amalgam, Chapter12/13.3 and LargeDistanceInput premises
retain their existing producers and final discharge.
Source: Aschbacher–Smith 13.4.10(8i), 13.4.14(1), printed pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem product_fixed_span_eq_seed_commutator
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (P B : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hTB : (T : Subgroup G) ≤ B)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : P ≠ B)
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcomm : ⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      ((pResidual 2 P).map P.subtype).pCoreIn 2)
    (hfix : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G) ⊓
      centralizer (B : Set G) = ⊥) :
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F P
    U = ⁅F,(pResidual 2 P).map P.subtype⁆ := by
  let X := P ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let R := (pResidual 2 P).map P.subtype
  let S := (pResidual 2 B).map B.subtype
  let F := Z ⊓ centralizer (B : Set G)
  let U := conjugateSpanBy F P
  have hTX : (T : Subgroup G) ≤ X := hTP.trans le_sup_left
  have hZT : Z ≤ (T : Subgroup G) := fun z hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hWX : W ≤ X := conjugateSpanBy_le (hZT.trans hTX) X.le_normalizer
  obtain ⟨hred,hker,_,_⟩ := Amalgam.original_pair_action_kernel h₀ D m hTP hTB eP eB hne hiP hiB
  have hRN : X ≤ normalizer (R : Set G) := by
    apply sup_le (le_normalizer_embedded_pResidual 2 P)
    have hs : S ⊔ (T : Subgroup G) = B := embedded_pResidual_sup_of_common_sylow B T
      (T.subtype hTB) (by rw [T.coe_subtype,map_subgroupOf_eq_of_le hTB])
    rw [←hs]
    exact sup_le (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 R)))
      (hTP.trans (le_normalizer_embedded_pResidual 2 P))
  have hcore : R.pCoreIn 2 ≤ X.pCoreIn 2 := pCoreIn_mono_of_normalizes
    ((map_subtype_le _).trans le_sup_left) hRN
  have hc : ⁅R,S⁆ ≤ centralizer (W : Set G) :=
    hcomm.trans (hcore.trans (hker.symm.le.trans inf_le_right))
  obtain ⟨_,_,hnS,_,_⟩ := Amalgam.original_pair_commuting_action h₀ D m hTP hTB eP eB hne
    hiP hiB hcentral hc
  have hSN : X ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans le_sup_right)).mp hnS
  have hUS : U ≤ centralizer (S : Set G) := conjugateSpanBy_le
    (inf_le_right.trans (centralizer_le (map_subtype_le _)))
    ((le_sup_left.trans hSN).trans (normalizer_le_normalizer_centralizer S))
  have hUW : U ≤ W := conjugateSpanBy_mono inf_le_left le_sup_left
  let : IsElementaryAbelian 2 (W.subgroupOf X) := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf X).map X.subtype) := IsElementaryAbelian.map X.subtype
    rwa [map_subgroupOf_eq_of_le hWX] at hh
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUW
  have hUT : U ≤ (T : Subgroup G) := by
    intro a ha
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTX)
      (hred.le_pCore (show (⟨a,hWX (hUW ha)⟩ : X) ∈ W.subgroupOf X from hUW ha))
  have hzero : U ⊓ centralizer (P : Set G) = ⊥ := by
    apply bot_unique
    intro a ha
    have haZ : a ∈ Z := (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hUT ha.1,elemPow_eq_one_of_isElementaryAbelian a ha.1,centralizer_le hTP ha.2⟩
    have haB : a ∈ centralizer (B : Set G) :=
      ((Amalgam.omega_fixed_twoResidual B hTB).le ⟨haZ,hUS ha.1⟩).2
    exact hfix.le ⟨⟨haZ,ha.2⟩,haB⟩
  have hFT : F ≤ centralizer (T : Set G) := fun a ha =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp ha.1).2.2
  have hsplit := conjugateSpan_split_of_sylow_fixed (T.subtype hTP)
    (show F ≤ centralizer (((T.subtype hTP : Sylow 2 P) : Subgroup P).map P.subtype : Set G) by
      rw [T.coe_subtype,map_subgroupOf_eq_of_le hTP]; exact hFT)
  change U = ⁅U,P⁆ ⊔ (U ⊓ centralizer (P : Set G)) at hsplit
  rw [hzero,sup_bot_eq] at hsplit
  have hFP : F ≤ P := inf_le_left.trans (hZT.trans hTP)
  have hUP : U ≤ P := conjugateSpanBy_le_self hFP
  have hcseed := normalClosure_commutator_eq_of_centralizing_supplement
    (F.subgroupOf P) (pResidual 2 P) (T.subtype hTP : Subgroup P)
    (pResidual_sup_sylow_eq_top (T.subtype hTP))
    (show F.subgroupOf P ≤ centralizer (T.subtype hTP : Set P) from
      fun a ha t ht => Subtype.ext (hFT ha t.val ht))
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy F P hFP] at hcseed
  have hm := congrArg (map P.subtype) hcseed
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hUP,
    map_subgroupOf_eq_of_le hFP,←MonoidHom.range_eq_map,range_subtype] at hm
  exact hsplit.trans hm


/-- In the product branch the original fixed line lies in the commutator
of the full central seed with the parabolic residual, and hence in the
moved module of the same component. -/
theorem original_product_fixed_commutator
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (P B K : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hTB : (T : Subgroup G) ≤ B) (hBM : B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hiP : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hfixed : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
      V ⊓ centralizer (L : Set G))
    (hcentral : let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hcomm : ⁅(pResidual 2 P).map P.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      ((pResidual 2 P).map P.subtype).pCoreIn 2)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hPK : P ≤ K ⊔ (T : Subgroup G)) :
    V ⊓ centralizer (L : Set G) ≤
      ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 P).map P.subtype⁆ ∧
    ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 P).map P.subtype⁆ ≤
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let U := conjugateSpanBy F P
  let R := (pResidual 2 P).map P.subtype
  let H := K ⊔ (T : Subgroup G)
  have hTP := hP.1.1.2
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hfix : Z ⊓ centralizer (P : Set G) ⊓ centralizer (B : Set G) = ⊥ := by
    apply bot_unique
    intro a ha
    by_contra hn
    have ha1 : a ≠ 1 := by simpa only [mem_bot] using hn
    have haF : a ∈ V ⊓ centralizer (L : Set G) := hfixed.le ⟨ha.1.1,ha.2⟩
    have hPC : P ≤ centralizer ({a} : Set G) := fun p hp =>
      mem_centralizer_singleton_iff.mpr (ha.1.2 p hp)
    exact hP.1.2 (hPC.trans (fixed_generator_centralizer h structural D m haF ha1).le)
  have hmove : U = ⁅F,R⁆ := product_fixed_span_eq_seed_commutator h₀ D m P B hTP hTB
    eP eB hne hiP hiB hcentral hcomm hfix
  have hRK : R ≤ K := by
    have hKH : K ≤ H := le_sup_left
    have hTH : (T : Subgroup G) ≤ H := le_sup_right
    let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
      (sup_le K.le_normalizer hTK)
    have hsup : K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤ := by
      apply map_injective H.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hTH,
        ←MonoidHom.range_eq_map,range_subtype]
    have hr := embedded_pResidual_le_of_normal_sup_pGroup
      (K.subgroupOf H) ((T : Subgroup G).subgroupOf H) (P.subgroupOf H)
      T.isPGroup'.comap_subtype (by rw [hsup]; exact le_top)
    have hm := map_mono (f := H.subtype) hr
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hPK,
      map_subgroupOf_eq_of_le hKH] at hm
    exact hm
  refine ⟨?_,commutator_mono (le_conjugateSpanBy Z K) hRK⟩
  rw [←hfixed]
  exact (le_conjugateSpanBy F P).trans
    (hmove.le.trans (commutator_mono inf_le_left le_rfl))


open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
/-- Apply the earlier plane amalgam input in either recognized component
row. Its product alternative has weight four and the literal fixed-line
commutator chain; its linear alternative is the full Thompson normalizer. -/
theorem small_component_original_module_amalgam
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        X ∈ Chapter1.HOver G (T : Set G) ∧
        ((⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∧ m.weight z = 4 ∧
          V ⊓ centralizer (L : Set G) ≤
            ⁅omegaOneCenterAmbient (T : Subgroup G),K₂⁆ ∧
          ⁅omegaOneCenterAmbient (T : Subgroup G),K₂⁆ ≤
            ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆) ∨
          (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P))) := by
  obtain ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,hfixed,hcentral⟩ :=
    small_component_original_pair hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK model
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hB : B ∈ Chapter1.HOver G (T : Set G) := by
    have hVB : V ≤ B.pCoreIn 2 := by
      let := D.elementary
      exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
        (D.le_sylow.trans hTB) (hBM.trans (normalizer_component_le_module h structural D m))
    refine ⟨?_,hTB⟩
    intro he
    have hv : V = ⊥ := bot_unique (he ▸ hVB)
    have hc := m.card_module
    rw [hv,card_bot] at hc
    omega
  have hcentral' :
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let X := P ⊔ B
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂) := by
    dsimp only
    intro hx
    obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral (P ⊔ B) hx.1 le_sup_left le_sup_right
    exact ⟨h₁,h₂,Or.inl hr⟩
  have hc := h1347 W hW hT P hP.1.1 hB ⟨eP⟩ ⟨eB⟩ hne
    (Solvable.original_second_flag_residual_eq_inner D m W hT)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB
    hcentral'
  refine ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,hlocal,?_⟩
  rcases hc.2 with hc | hc
  · have hH : centralizer ({z.val} : Set G) = K ⊔ (T : Subgroup G) := by
      rcases model with he | he <;> obtain ⟨eK⟩ := he
      · exact (linear_full_centralizer hl h₀ h structural modules D m h1332 fixed hindex
          hM z hzT hzL hK.1 hHN hKM hfK eK).1
      · exact (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed hindex
          hM z hzT hzL hK hHN hKM hfK eK).1
    have hfixedB : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
        V ⊓ centralizer (L : Set G) := by
      rw [←Amalgam.omega_fixed_twoResidual B hTB]
      exact hfixed
    exact Or.inl ⟨hc,original_product_weight_four h structural D m W hW hT P hP
      z hzL hPH.le hc,original_product_fixed_commutator h₀ h structural D m P B K
        hP hTB hBM eP eB hiP hiB hfixedB hcentral' hc
        ((Solvable.original_sylow_le_centralizer hzT).trans hHN) (hPH.le.trans_eq hH)⟩
  · exact Or.inr ⟨hc,original_linear_pair_maximal h structural D m z.val hzT P B hP hTB
      hBM eP eB hlocal (fun Y hY hPY hBY =>
        ⟨(hcentral Y hY hPY hBY).1,(hcentral Y hY hPY hBY).2.1⟩) hc⟩


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
