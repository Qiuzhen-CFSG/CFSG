module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductModule

/-!
# The component core's weight in the original product alternative

The component's invariant-plane normalizer is the actual outside
parabolic P. Its residual fixes only the component's constant line, so
it cannot centralize the original fixed generator d once d belongs to
the component module. Finite minimal descent and the proved uniqueness
of the outside parabolic identify the two literal subgroups.

The product commutator bound and the reduced omega action give reverse
residual normalization. If d had weight two in the component core, the
marked tetrahedral orbit calculation would put the original L₂ inside
N_G(K)=C_G(z). But L₂ fixes only the original constant line, contradicting
the escaping choice of z. Thus d has weight four.

The final application constructs the five-dimensional marking, original
pair and component plane from the existing source inputs. The previously
proved commutator chain supplies d's module membership. Both the original
and reciprocal weights are four in the product branch; the linear branch
retains its full Thompson-normalizer conclusion. This supplies the last
five-dimensional weight clause of 13.4.10(8i). The other module alternatives,
both-weight comparison, reciprocal commutator exclusions and graph assembly
remain separate obligations. Earlier Chapter12/13.3 and plane-amalgam inputs
retain their existing producers and final discharge.

Source: Aschbacher–Smith 13.4.10(8i), printed pp.909–910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V K U : Subgroup G}

private theorem product_reverse_residual_normalization
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
      ((pResidual 2 P).map P.subtype).pCoreIn 2) :
    (pResidual 2 P).map P.subtype ≤
      normalizer (((pResidual 2 B).map B.subtype : Subgroup G) : Set G) := by
  let X := P ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let R := (pResidual 2 P).map P.subtype
  let S := (pResidual 2 B).map B.subtype
  obtain ⟨_,hker,_,_⟩ := Amalgam.original_pair_action_kernel h₀ D m hTP hTB eP eB hne hiP hiB
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
  exact ((map_subtype_le _).trans le_sup_left).trans
    ((normal_subgroupOf_iff_le_normalizer ((map_subtype_le _).trans le_sup_right)).mp hnS)

/-- Once the original fixed generator lies in the component core, the
component plane normalizer is the unique actual outside parabolic. -/
theorem component_core_plane_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hK12 : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (DK : ChosenModule T K U) (mK : CoreMarking DK)
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hd : m.constant.val ∈ U)
    (z : G) (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hH : centralizer ({z} : Set G) = K ⊔ (T : Subgroup G))
    (P : Subgroup G) (hPH : P ⋖ centralizer ({z} : Set G))
    (hunique : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Q ≤ centralizer ({z} : Set G) → Q = P) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (mK.naturalPreimage W : Set G) ∧
      P = (K ⊔ (T : Subgroup G)) ⊓ normalizer (mK.naturalPreimage W : Set G) := by
  classical
  obtain ⟨W,hW,hT⟩ := Solvable.exists_original_invariant_plane hK12 structural DK mK
  let Q := (K ⊔ (T : Subgroup G)) ⊓ normalizer (mK.naturalPreimage W : Set G)
  have hTQ : (T : Subgroup G) ≤ Q := le_inf le_sup_right hT
  have hQH : Q ≤ centralizer ({z} : Set G) := hH.symm ▸ inf_le_left
  have hQM : ¬ Q ≤ normalizer (L : Set G) := by
    intro hQM
    have hdR : m.constant.val ∈ centralizer ((pResidual 2 Q).map Q.subtype : Set G) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      have haC : a ∈ centralizer ({m.constant.val} : Set G) := by
        rw [fixed_generator_centralizer h structural D m
          ⟨m.constant.property,m.constant_fixed⟩
          (fun hh => m.constant_ne_one (Subtype.ext hh))]
        exact hQM (map_subtype_le _ ha)
      exact mem_centralizer_singleton_iff.mp haC
    have hdK : m.constant.val ∈ centralizer (K : Set G) :=
      ((Solvable.original_second_flag_fixed DK mK W hW hT).le ⟨hd,hdR⟩).2
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hdK a ha)
  have hlocal : Q ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTQ hQH (Solvable.centralizer_mem_HOver hzT hz1)
  let S : Set (Subgroup G) := {Y | Y ∈ Chapter1.HOver G (T : Set G) ∧
    ¬ Y ≤ normalizer (L : Set G) ∧ Y ≤ Q}
  obtain ⟨R,hR⟩ := (Set.toFinite S).exists_minimalFor id S ⟨Q,hlocal,hQM,le_rfl⟩
  have hstar : R ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
    refine ⟨⟨hR.1.1,hR.1.2.1⟩,?_⟩
    intro Y hY hYR
    exact hR.2 ⟨hY.1,hY.2,hYR.trans hR.1.2.2⟩ hYR
  have hPQ : P ≤ Q := hunique R hstar (hR.1.2.2.trans hQH) ▸ hR.1.2.2
  have hne : Q ≠ centralizer ({z} : Set G) := by
    intro he
    have hc := (Solvable.original_second_flag_coatom DK mK W hW hT).1
    apply hc
    change Q.subgroupOf (K ⊔ (T : Subgroup G)) = ⊤
    rw [he,hH,subgroupOf_self]
  exact ⟨W,hW,hT,((hPH.eq_or_eq hPQ hQH).resolve_right hne).symm⟩

/-- Reverse residual normalization excludes weight two for the original
fixed generator in the component core, retaining both literal planes. -/
theorem original_product_component_core_weight_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hK12 : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (DK : ChosenModule T K U) (mK : CoreMarking DK)
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hd : m.constant.val ∈ U)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) (hzU : z.val ∈ U)
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hH : centralizer ({z.val} : Set G) = K ⊔ (T : Subgroup G))
    (P : Subgroup G) (hPH : P ⋖ centralizer ({z.val} : Set G))
    (hunique : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Q ≤ centralizer ({z.val} : Set G) → Q = P)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hnorm : let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      (pResidual 2 P).map P.subtype ≤ normalizer
        (((pResidual 2 B).map B.subtype : Subgroup G) : Set G)) :
    mK.weight ⟨m.constant.val,hd⟩ = 4 := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hc
    apply hKM
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    exact fun a ha => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc a ha)
  rcases mK.nonfixed_weight ⟨m.constant.val,hd⟩ hdK with hw | hw
  · exfalso
    obtain ⟨WK,hWK,hTK,hP⟩ := component_core_plane_parabolic h hK12 structural D m DK mK hKM hd
      z.val hzT hz1 hH P hPH hunique
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let S := (pResidual 2 B).map B.subtype
    have hSL : S ≤ L := by
      exact (Solvable.original_second_flag_residual_eq_inner D m W hT).le.trans
        ((map_subtype_le _).trans inf_le_left)
    have hdS : m.constant.val ∈ centralizer (S : Set G) :=
      centralizer_le hSL m.constant_fixed
    have hSN : S ≤ normalizer (K : Set G) :=
      original_second_residual_weight_two hK12 structural DK mK WK hWK hTK S
        (hP ▸ hnorm) ⟨m.constant.val,hd⟩ hdS hw
    have hzK : z.val ∈ centralizer (K : Set G) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      exact mem_centralizer_singleton_iff.mp (hKz ha)
    have hSC : S ≤ centralizer ({z.val} : Set G) := by
      rw [fixed_generator_centralizer hK12 structural DK mK ⟨hzU,hzK⟩ hz1]
      exact hSN
    have hzS : z.val ∈ centralizer (S : Set G) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      exact mem_centralizer_singleton_iff.mp (hSC ha)
    exact hzL (((Solvable.original_second_flag_fixed D m W hW hT).le
      ⟨z.property,hzS⟩).2)
  · exact hw

/-- In the five-dimensional ordinary component row, construct the original
pair and its reciprocal plane, and prove both product-branch weights. -/
theorem ordinary_six_original_core_weight_amalgam
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
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U, ∃ mK : CoreMarking DK,
      ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
        Module.finrank (ZMod 2) W = 2 ∧
        (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
        ∃ P : Subgroup G,
          P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
          P ⋖ centralizer ({z.val} : Set G) ∧
          let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
          let X := P ⊔ B
          let K₂ := (pResidual 2 P).map P.subtype
          let L₂ := (pResidual 2 B).map B.subtype
          X ∈ Chapter1.HOver G (T : Set G) ∧
          ((⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∧ m.weight z = 4 ∧
              ∃ hd : m.constant.val ∈ U, mK.weight ⟨m.constant.val,hd⟩ = 4 ∧
                ∃ WK : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
                  Module.finrank (ZMod 2) WK = 2 ∧
                  (T : Subgroup G) ≤ normalizer (mK.naturalPreimage WK : Set G) ∧
                  P = (K ⊔ (T : Subgroup G)) ⊓ normalizer (mK.naturalPreimage WK : Set G)) ∨
            (Solvable.LinearAmalgamConclusion T X ∧
              X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
              IsMaximalTwoLocal X ∧
              Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
              (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
                Q ≤ X → Q = P))) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,hfixK,_,_,_,_⟩ := component_core_marking_of_source_fixed
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hzU : z.val ∈ U := (hfixK.symm ▸ mem_zpowers z.val).1
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,hfixedB,hcentral⟩ :=
    ordinary_six_original_pair h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK eK
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT
  have hBM : B ≤ normalizer (L : Set G) := by rw [hM]; exact inf_le_left
  have hne : P ≠ B := fun he => hP.1.2 (he ▸ hBM)
  have hB : B ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTB le_sup_right hlocal
  have hcentral' :
      let X := P ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 P).map P.subtype
      let K₂ := (pResidual 2 B).map B.subtype
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
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB hcentral'
  refine ⟨DK,mK,W,hW,hT,P,hP,hPH,hlocal,?_⟩
  rcases hc.2 with hc | hc
  · have hH := (ordinary_six_full_centralizer h₀ h structural modules D m h1332 fixed
      hindex hM z hzT hzL hK hHN hKM hfK eK).1
    have hfixedP : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G) =
        V ⊓ centralizer (L : Set G) := by
      rw [←Amalgam.omega_fixed_twoResidual B hTB]
      exact hfixedB
    have hmove := original_product_fixed_commutator h₀ h structural D m P B K hP hTB hBM
      eP eB hiP hiB hfixedP hcentral' hc
      ((Solvable.original_sylow_le_centralizer hzT).trans hHN) (hPH.le.trans_eq hH)
    have hd : m.constant.val ∈ U := hmove.2 (hmove.1 ⟨m.constant.property,m.constant_fixed⟩)
    obtain ⟨P₀,_,_,_,_,_,_,_,_,_,_,_,_,hunique₀⟩ :=
      ordinary_six_full_centralizer_parabolic h₀ h structural modules D m h1332 fixed
        hindex hM z hzT hzL hK hHN hKM hfK eK
    have hPP : P = P₀ := hunique₀ P hP hPH.le
    have hunique : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        Q ≤ centralizer ({z.val} : Set G) → Q = P := by
      intro Q hQ hQH
      exact (hunique₀ Q hQ hQH).trans hPP.symm
    have hnorm := product_reverse_residual_normalization h₀ D m P B hP.1.1.2 hTB eP eB hne hiP hiB hcentral' hc
    exact Or.inl ⟨hc,original_product_weight_four h structural D m W hW hT P hP z hzL hPH.le hc,
      hd,original_product_component_core_weight_four h hK12 structural D m DK mK hKM hd z hzT hzL hzU hK.1 hH P hPH
        hunique W hW hT hnorm,
      component_core_plane_parabolic h hK12 structural D m DK mK hKM hd z.val hzT hz1 hH P hPH hunique⟩
  · exact Or.inr ⟨hc,original_linear_pair_maximal h structural D m z.val hzT P B hP hTB
      hBM eP eB hlocal (fun Y hY hPY hBY =>
        ⟨(hcentral Y hY hPY hBY).1,(hcentral Y hY hPY hBY).2.1⟩) hc⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
