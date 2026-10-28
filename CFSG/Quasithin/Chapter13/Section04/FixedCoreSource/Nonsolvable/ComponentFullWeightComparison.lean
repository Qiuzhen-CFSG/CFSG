module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullLinearPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixWeights
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Comparison at both escaping weights in the two component rows

Both the linear-three and ordinary A₆ centralizer constructions verify the
literal original-pair applicability clauses. Apply the earlier 13.4.7 input,
then the marked tetrahedral weight calculation: at weight two the join is
N_G(J(T)), has quotient L₃(2), and has a unique outside parabolic.

The same invariant plane identifies L₂T for both escaping weights, even
when their components have different quotient rows. Their distinct fixed
lines force distinct outside parabolics. The weight-four join therefore
has the product commutator bound, and its residual is normalized by L₂T.
The P₂/P₄ pair is local, has its two actual fixed lines, and the full orbit
of Ω₁Z(T) is reduced with its literal parabolic and Sylow action kernels.
The solvable-normalizer obstruction then excludes both normalization of
O²(P₄) by O²(P₂) and containment of P₂P₄ in N_G(J(T)).

This proves the first comparison of 13.4.12 for all four combinations of
the two recognized quotient rows. It retains the actual full core and maps.
It does not replace the additional P₂/P₄ application of general 13.4.7,
the module-weight conclusions, or the later commutator and graph arguments.
Earlier source inputs, including LargeDistanceInput, retain their existing
producers and final discharge. Source: Aschbacher–Smith 13.4.10(8) and
13.4.12, printed pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Either recognized component row supplies the original pair and all
literal applicability clauses of the plane amalgam input. -/
theorem small_component_original_pair
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
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
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
        let Z := omegaOneCenterAmbient (T : Subgroup G)
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
        B = L₂ ⊔ (T : Subgroup G) ∧ X ∈ Chapter1.HOver G (T : Set G) ∧
        L₂ ≤ L ∧
        (∀ s : NoncentralChiefRefinement.ChiefSeries L₂,
          s.head = ⊥ → s.last = ⊤ → 3 ≤ s.noncentralTwoCount) ∧
        (Z ⊓ centralizer (P : Set G)).relIndex Z = 2 ∧
        (Z ⊓ centralizer (B : Set G)).relIndex Z = 2 ∧
        Z ⊓ centralizer (L₂ : Set G) = V ⊓ centralizer (L : Set G) ∧
        (∀ Y : Subgroup G, Y ∈ Chapter1.H G → P ≤ Y → B ≤ Y →
          let C₁ := Y ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
          let C₂ := Y ⊓ centralizer ((Z ⊓ centralizer (L₂ : Set G) : Subgroup G) : Set G)
          Y ⊓ normalizer (L : Set G) = B ∧
          Y ⊓ centralizer ({z.val} : Set G) = P ∧
          C₁ = P ∧ C₂ = B ∧ (K₂.subgroupOf C₁).Normal ∧ (L₂.subgroupOf C₂).Normal ∧
          (primeToResidual 3 C₁).map C₁.subtype = K₂) := by
  rcases model with he | he <;> obtain ⟨eK⟩ := he
  · exact linear_original_pair hl h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK.1 hHN hKM hfK eK
  · exact ordinary_six_original_pair h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK eK

/-- The original pair alternatives for either recognized component quotient. -/
theorem small_component_original_weight_amalgam
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
        ((⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∧ m.weight z = 4) ∨
          (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P))) := by
  obtain ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,_,hcentral⟩ :=
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
  have hc := h1347 W hW hT P hP.1.1 hB ⟨eP⟩ ⟨eB⟩ hne
    (Solvable.original_second_flag_residual_eq_inner D m W hT)
    (Or.inr (fun s hs ht => le_trans (by decide : 2 ≤ 3) (hchief s hs ht))) hiP hiB
    (fun hx => by
      obtain ⟨_,_,_,_,h₁,h₂,hr⟩ := hcentral (P ⊔ B) hx.1 le_sup_left le_sup_right
      exact ⟨h₁,h₂,Or.inl hr⟩)
  refine ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,hlocal,?_⟩
  rcases hc.2 with hc | hc
  · exact Or.inl ⟨hc,original_product_weight_four h structural D m W hW hT P hP
      z hzL hPH.le hc⟩
  · exact Or.inr ⟨hc,original_linear_pair_maximal h structural D m z.val hzT P B hP hTB
      hBM eP eB hlocal (fun Y hY hPY hBY =>
        ⟨(hcentral Y hY hPY hBY).1,(hcentral Y hY hPY hBY).2.1⟩) hc⟩

/-- Weight two forces the full Thompson normalizer in either component row. -/
theorem small_component_weight_two_thompson
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
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)))
    (hweight : m.weight z = 2) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        X ∈ Chapter1.HOver G (T : Set G) ∧
        (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P)) := by
  obtain ⟨W,hW,hT,P,hP,hPH,hqP,hlocal,halt⟩ := small_component_original_weight_amalgam
    hl h₀ h structural modules D m h1332 fixed hindex hM h1347
    z hzT hzL hK hHN hKM hfK model
  refine ⟨W,hW,hT,P,hP,hPH,hqP,hlocal,?_⟩
  exact halt.resolve_left (fun hh => by omega)


private theorem original_comparison_pair_obstruction
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z w : V) (hz : m.weight z = 2) (hw : m.weight w = 4)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P Q B : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hQ : Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G))
    (hQw : Q ≤ centralizer ({w.val} : Set G))
    (eQ : (Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3))
    (hTB : (T : Subgroup G) ≤ B)
    (hX : P ⊔ B = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hmax : IsMaximalTwoLocal (P ⊔ B))
    (eX : ((P ⊔ B : Subgroup G) ⧸ pCore 2 (P ⊔ B : Subgroup G)) ≃* Matrix.PSL3Two.SL)
    (hu : ∀ U ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      U ≤ P ⊔ B → U = P)
    (hBN : B ≤ normalizer ((pResidual 2 Q).map Q.subtype : Set G)) :
    ¬ (pResidual 2 P).map P.subtype ≤ normalizer ((pResidual 2 Q).map Q.subtype : Set G) ∧
    ¬ P ⊔ Q ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let L₂ := (pResidual 2 B).map B.subtype
  have hB : L₂ ⊔ (T : Subgroup G) = B :=
    embedded_pResidual_sup_of_common_sylow B T (T.subtype hTB)
      (by rw [T.coe_subtype,map_subgroupOf_eq_of_le hTB])
  have hz1 : z ≠ 1 := by intro he; rw [he,m.weight_one] at hz; omega
  have hw1 : w ≠ 1 := by intro he; rw [he,m.weight_one] at hw; omega
  have exclude (hpair : (pResidual 2 P).map P.subtype ≤
      normalizer ((pResidual 2 Q).map Q.subtype : Set G) ∨
      P ⊔ Q ≤ thompsonNormalizer T) : False := by
    let C : ParabolicComparison T (normalizer (L : Set G)) L₂
        (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) z.val w.val := {
      two := P
      four := Q
      two_mem := hP
      four_mem := hQ
      two_fixed := m.central_four_fixed_of_escape h structural z hz1 hzT P hPz hP.1.2
      four_fixed := m.central_four_fixed_of_escape h structural w hw1 hwT Q hQw hQ.1.2
      four_solvable := SymmetricThreeTwoCore.solvable eQ
      four_characteristic := Chapter1.mem_He_iff.mp
        (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hQ.1.1)
      maximal := by simpa only [thompsonNormalizer, ←hX] using hmax
      quotient := by
        unfold thompsonNormalizer
        rw [←hX]
        exact eX
      generation := by rw [hB,sup_comm]; exact hX
      unique_parabolic := by
        intro U hU hUN
        apply hu U hU
        rwa [hX]
      four_alternatives := Or.inl (by rwa [hB])
      pair_alternatives := hpair }
    exact C.false_of_weights m L₂ z w hz hw
  exact ⟨fun hn => exclude (Or.inl hn),fun hn => exclude (Or.inr hn)⟩

/-- Compare both escaping weights, allowing different component quotient rows. -/
theorem small_components_both_weights_comparison
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
    (z w : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hwL : w.val ∉ centralizer (L : Set G))
    (hz : m.weight z = 2) (hw : m.weight w = 4)
    (K N : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)))
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({w.val} : Set G)))
    (hNN : centralizer ({w.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (modelN : Nonempty ((N ⧸ pCore 2 N) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6))) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P Q : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ⋖ centralizer ({z.val} : Set G) ∧ Q ⋖ centralizer ({w.val} : Set G) ∧
        Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty ((Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) ∧ P ≠ Q ∧
        P ⊔ Q ∈ Chapter1.HOver G (T : Set G) ∧
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (P : Set G) = zpowers z.val ∧
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (Q : Set G) = zpowers w.val ∧
        let X := P ⊔ Q
        let W₀ := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X₂ := P ⊔ B
        let R₄ := (pResidual 2 Q).map Q.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        X₂ = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        IsMaximalTwoLocal X₂ ∧ Nonempty ((X₂ ⧸ pCore 2 X₂) ≃* Matrix.PSL3Two.SL) ∧
        (∀ U ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)), U ≤ X₂ → U = P) ∧
        Q ⊔ B ∈ Chapter1.HOver G (T : Set G) ∧ ⁅R₄,L₂⁆ ≤ R₄.pCoreIn 2 ∧
        B ≤ normalizer (R₄ : Set G) ∧
        ¬ (pResidual 2 P).map P.subtype ≤ normalizer (R₄ : Set G) ∧
        ¬ P ⊔ Q ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        IsPReduced 2 (W₀.subgroupOf X) ∧
        P ⊓ centralizer (W₀ : Set G) = X.pCoreIn 2 ∧
        Q ⊓ centralizer (W₀ : Set G) = X.pCoreIn 2 ∧
        (T : Subgroup G) ⊓ centralizer (W₀ : Set G) = X.pCoreIn 2 := by
  obtain ⟨W₂,hW₂,hT₂,P,hP,hPz,⟨eP⟩,_,_,hX₂,hmax,hquot,hunique⟩ :=
    small_component_weight_two_thompson hl h₀ h structural modules D m h1332 fixed hindex hM h1347
      z hzT hzL hK hKN hKM hfK model hz
  obtain ⟨W₄,hW₄,hT₄,Q,hQ,hQw,⟨eQ⟩,hlocal,halt⟩ :=
    small_component_original_weight_amalgam hl h₀ h structural modules D m h1332 fixed hindex hM h1347
      w hwT hwL hN hNN hNM hfN modelN
  have hWe := original_invariant_plane_unique D m W₂ W₄ hW₂ hW₄ hT₂ hT₄
  subst W₄
  have hne := different_weight_parabolics h structural D m z w hz hw hzT hwT P Q hP hQ hPz.le hQw.le
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W₂ : Set G)
  let R := (pResidual 2 Q).map Q.subtype
  let L₂ := (pResidual 2 B).map B.subtype
  have hcomm : ⁅R,L₂⁆ ≤ R.pCoreIn 2 := by
    rcases halt with hprod | ⟨_,hX₄,_,_,_⟩
    · exact hprod.1
    · exfalso
      apply hne
      apply (hunique Q hQ ?_).symm
      rw [hX₂,←hX₄]
      exact le_sup_left
  have hZ : omegaOneCenterAmbient (T : Subgroup G) =
      V ⊓ omegaOneCenterAmbient (T : Subgroup G) := by
    rcases model with he | he <;> obtain ⟨eK⟩ := he
    · obtain ⟨_,_,_,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry
        hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hKN hKM hfK eK
      exact hZ
    · obtain ⟨_,_,_,_,_,_,hZ,_⟩ := ordinary_six_component_geometry
        h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hKN hKM hfK eK
      exact hZ
  have hz1 : z ≠ 1 := fun he => hzL (congrArg Subtype.val he ▸ one_mem _)
  have hw1 : w ≠ 1 := fun he => hwL (congrArg Subtype.val he ▸ one_mem _)
  have hfixP := m.central_four_fixed_of_escape h structural z hz1 hzT P hPz.le hP.1.2
  have hfixQ := m.central_four_fixed_of_escape h structural w hw1 hwT Q hQw.le hQ.1.2
  have hiP := escaping_residual_fixed_index h structural m z hz1 hzT P hP hPz.le
  have hiQ := escaping_residual_fixed_index h structural m w hw1 hwT Q hQ hQw.le
  rw [←hZ] at hfixP hfixQ hiP hiQ
  rw [Amalgam.omega_fixed_twoResidual P hP.1.1.2] at hiP
  rw [Amalgam.omega_fixed_twoResidual Q hQ.1.1.2] at hiQ
  have hpair := Amalgam.original_pair_local D m hP.1.1.2 hQ.1.1.2 eP eQ hne hiP hiQ
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT₂
  have hB : L₂ ⊔ (T : Subgroup G) = B :=
    embedded_pResidual_sup_of_common_sylow B T (T.subtype hTB)
      (by rw [T.coe_subtype,map_subgroupOf_eq_of_le hTB])
  have hBN : B ≤ normalizer (R : Set G) := by
    rw [←hB]
    exact sup_le (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 R)))
      (hQ.1.1.2.trans (le_normalizer_embedded_pResidual 2 Q))
  obtain ⟨eX⟩ := hquot
  have hexclude := original_comparison_pair_obstruction h₀ h structural D m z w hz hw
    hzT hwT P Q B hP hQ hPz.le hQw.le eQ hTB hX₂ hmax eX hunique hBN
  have haction := Amalgam.original_pair_action_kernel h₀ D m
    hP.1.1.2 hQ.1.1.2 eP eQ hne hiP hiQ
  exact ⟨W₂,hW₂,hT₂,P,Q,hP,hQ,hPz,hQw,⟨eP⟩,⟨eQ⟩,hne,hpair,hfixP,hfixQ,
    hX₂,hmax,⟨eX⟩,hunique,hlocal,hcomm,hBN,hexclude.1,hexclude.2,haction⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
