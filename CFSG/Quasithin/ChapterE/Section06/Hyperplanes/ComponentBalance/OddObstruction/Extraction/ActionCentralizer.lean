module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction.Preparation
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent
public import Theory.GroupTheory.SylowCentralOddCoreImage
public import Mathlib.GroupTheory.IndexNormal

/-!
# The full action-centralizer obstruction in E.6.19

For an ordinary component L of H = C_G(A), component calculus makes the
solvable kernel O(H)A centralize L. Perfect centralizer lifting and the
C-component normalizer correspondence identify Aut_H(L) with the actual
full automizer of its image in H/(O(H)A). This identification carries every
normalizing subgroup's induced action through the specified quotient map.
It therefore identifies the two action centralizers as groups.

To establish the odd-core obstruction, use the earlier normal-or-two-conjugates
clause of 1.2.1(3). It makes the component normalizer normal, including in the
quotient, so the ambient Sylow two-subgroup restricts to it. The source U-action
is still central in this Sylow subgroup. `SylowCentralOddCoreImage` then sends
the odd centralizer core into the odd core of the **full** induced automizer
centralizer. The given component commutator makes its action nontrivial.

Thus the smaller automizer in the printed proof of Aschbacher 31.18(2) is
not silently enlarged: a Frattini surjection proves the needed normality
in the full automizer. The result retains 1.2.1(3) as an explicit earlier-source
input, as permitted for this E.6 helper. It assumes no action odd-core,
balance, exceptional-model, or E.6.18 conclusion. DetectedComponent assembly
remains in the parent extraction module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263), and 1.2.1(3), printed p.504 (PDF p.521);
Aschbacher, *Finite Group Theory*, second edition, 31.18(2), printed p.161
(PDF p.171). The solvable-quotient correspondence is source A.3.3(4).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V A U L : Subgroup G}

/-- The actual solvable quotient kernel centralizes every ordinary component. -/
theorem quotientKernel_centralizes_component
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent A L) :
    quotientKernel A ≤ centralizer (L.subgroupOf (centralizer (A : Set G)) :
      Set (centralizer (A : Set G))) := by
  let _ := quotientKernel_solvable h earlier hA
  let _ := hL.2.2
  rcases hL.2.normal_dichotomy (quotientKernel A) with hl | hc
  · let J := L.subgroupOf (centralizer (A : Set G))
    let _ : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
    let _ : Nontrivial J := (QuotientGroup.mk'_surjective (center J)).nontrivial
    let _ : Group.IsSolvable J :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hl)
    exact (Group.IsPerfect.not_isSolvable J inferInstance).elim
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)

/-- The normalizer correspondence for the given component and actual quotient map. -/
theorem component_normalizer_preimage
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent A L) :
    (normalizer (quotientImage A L : Set (CentralizerQuotient A))).comap (quotientMap A) =
      (normalizer (L : Set G)).subgroupOf (centralizer (A : Set G)) := by
  let _ := quotientKernel_solvable h earlier hA
  rw [subgroupOf_normalizer_eq hL.1]
  exact normalizer_cComponent_quotient hL.2.isCComponent (quotientKernel A)

/-- Perfectness lifts the quotient component centralizer across the actual kernel. -/
theorem component_centralizer_preimage
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent A L) :
    (centralizer (quotientImage A L : Set (CentralizerQuotient A))).comap (quotientMap A) =
      centralizer (L.subgroupOf (centralizer (A : Set G)) :
        Set (centralizer (A : Set G))) := by
  let _ := hL.2.2
  apply comap_centralizer_map_eq_of_perfect
  rw [quotientMap_ker]
  exact quotientKernel_centralizes_component h earlier hA hL

private theorem equiv_of_surjective_ker_eq
    {N B C : Type*} [Group N] [Group B] [Group C]
    (f : N →* B) (g : N →* C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hk : f.ker = g.ker) : ∃ e : B ≃* C, ∀ n, e (f n) = g n := by
  let ef := QuotientGroup.liftEquiv f.ker hf rfl
  let eg := QuotientGroup.liftEquiv f.ker hg hk
  refine ⟨ef.symm.trans eg, fun n => ?_⟩
  change eg (ef.symm (f n)) = g n
  rw [← QuotientGroup.liftEquiv_mk f.ker hf rfl n, ef.symm_apply_apply]
  rfl

/-- The two automizers agree through the actual quotient, including every induced actor. -/
theorem exists_component_automizer_equiv
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent A L) :
    ∃ e : inducedAutomizer L (centralizer (A : Set G)) ≃* Automizer (quotientImage A L),
      ∀ U : Subgroup G, U ≤ centralizer (A : Set G) → U ≤ normalizer (L : Set G) →
        ((inducedAutomizer L U).subgroupOf
          (inducedAutomizer L (centralizer (A : Set G)))).map e.toMonoidHom =
            inducedAutomizer (quotientImage A L) (quotientImage A U) := by
  let H := centralizer (A : Set G)
  let D := quotientImage A L
  let N := H.subgroupOf (normalizer (L : Set G))
  let f : N →* inducedAutomizer L H := L.normalizerMonoidHom.rangeRestrict.subgroupMap N
  let nH : N →* H := ((normalizer (L : Set G)).subtype.comp N.subtype).codRestrict H
    (fun n => n.property)
  have hn (n : N) : quotientMap A (nH n) ∈ normalizer (D : Set (CentralizerQuotient A)) := by
    have hh : nH n ∈ (normalizer (D : Set (CentralizerQuotient A))).comap (quotientMap A) := by
      rw [component_normalizer_preimage h earlier hA hL]
      exact n.val.property
    exact hh
  let qN : N →* normalizer (D : Set (CentralizerQuotient A)) :=
    ((quotientMap A).comp nH).codRestrict _ hn
  let g : N →* Automizer D := D.normalizerMonoidHom.rangeRestrict.comp qN
  have hf : Function.Surjective f := L.normalizerMonoidHom.rangeRestrict.subgroupMap_surjective N
  have hqN : Function.Surjective qN := by
    intro d
    obtain ⟨n, he⟩ := quotientMap_surjective A (d : CentralizerQuotient A)
    have hm : n ∈ (normalizer (L : Set G)).subgroupOf H := by
      rw [← component_normalizer_preimage h earlier hA hL]
      change quotientMap A n ∈ normalizer (D : Set (CentralizerQuotient A))
      rw [he]
      exact d.property
    exact ⟨⟨⟨n, hm⟩, n.property⟩, Subtype.ext he⟩
  have hg : Function.Surjective g := D.normalizerMonoidHom.rangeRestrict_surjective.comp hqN
  have hk : f.ker = g.ker := by
    ext n
    have hfker : n ∈ f.ker ↔ (n.val : G) ∈ centralizer (L : Set G) := by
      change f n = 1 ↔ _
      rw [← Subtype.val_inj, ← Subtype.val_inj]
      exact Iff.rfl.trans (show n.val ∈ L.normalizerMonoidHom.ker ↔ _ from by
        rw [normalizerMonoidHom_ker]; rfl)
    have hgker : n ∈ g.ker ↔ quotientMap A (nH n) ∈ centralizer (D : Set (CentralizerQuotient A)) := by
      change g n = 1 ↔ _
      rw [← Subtype.val_inj]
      exact Iff.rfl.trans (show qN n ∈ D.normalizerMonoidHom.ker ↔ _ from by
        rw [normalizerMonoidHom_ker]; rfl)
    rw [hfker, hgker]
    change _ ↔ nH n ∈ (centralizer (D : Set (CentralizerQuotient A))).comap (quotientMap A)
    rw [component_centralizer_preimage h earlier hA hL]
    constructor
    · intro hc l hl
      exact Subtype.ext (hc l hl)
    · intro hc l hl
      exact congrArg Subtype.val (hc ⟨l, hL.1 hl⟩ hl)
  obtain ⟨e, he⟩ := equiv_of_surjective_ker_eq f g hf hg hk
  refine ⟨e, fun U hUH hUN => ?_⟩
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n, hnU, hna⟩ := ha
    let n' : N := ⟨n, hUH hnU⟩
    have hna' : f n' = a := Subtype.ext hna
    change e a ∈ _
    rw [← hna', he]
    refine ⟨qN n', ?_, rfl⟩
    exact ⟨nH n', hnU, rfl⟩
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨u, hu, hud⟩ := hd
    let n : N := ⟨⟨u, hUN hu⟩, u.property⟩
    refine ⟨f n, ?_, ?_⟩
    · exact ⟨n.val, hu, rfl⟩
    · change e (f n) = _
      rw [he]
      apply congrArg D.normalizerMonoidHom.rangeRestrict
      exact Subtype.ext hud


/-- The centralizer in the full automizer of the quotient component. -/
def quotientActionCentralizer (A U L : Subgroup G) :
    Subgroup (Automizer (quotientImage A L)) :=
  centralizer (inducedAutomizer (quotientImage A L) (quotientImage A U) :
    Set (Automizer (quotientImage A L)))

/-- Descent identifies both full action centralizers, preserving the actual U-action. -/
theorem exists_actionCentralizer_equiv
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent A L)
    (hUH : U ≤ centralizer (A : Set G)) (hUN : U ≤ normalizer (L : Set G)) :
    Nonempty (actionCentralizer A U L ≃* quotientActionCentralizer A U L) := by
  obtain ⟨e, he⟩ := exists_component_automizer_equiv h earlier hA hL
  have hc : (actionCentralizer A U L).map e.toMonoidHom = quotientActionCentralizer A U L := by
    rw [actionCentralizer, map_centralizer_equiv]
    change centralizer ((((inducedAutomizer L U).subgroupOf
      (inducedAutomizer L (centralizer (A : Set G)))).map e.toMonoidHom) :
        Set (Automizer (quotientImage A L))) = _
    rw [he U hUH hUN]
    rfl
  exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr hc)⟩

/-- Source 1.2.1(3), through the actual solvable quotient, makes the component
normalizer normal. Normality of the component itself is not required. -/
theorem quotient_component_normalizer_normal
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hL : CentralizerComponent A L)
    (horbit : (L.subgroupOf (centralizer (A : Set G))).Normal ∨
      (normalizer (L.subgroupOf (centralizer (A : Set G)) :
        Set (centralizer (A : Set G)))).index = 2) :
    (normalizer (quotientImage A L : Set (CentralizerQuotient A))).Normal := by
  apply (normal_comap_iff_of_surjective (quotientMap_surjective A)).mp
  rw [component_normalizer_preimage h earlier hA hL, subgroupOf_normalizer_eq hL.1]
  rcases horbit with hn | hi
  · let _ := hn
    rw [normalizer_eq_top]
    infer_instance
  · exact normal_of_index_eq_two hi

private theorem oddCore_action_ne_bot_of_normal_normalizer
    (S : Sylow 2 G) (B D : Subgroup G) (hD : IsComponent G D)
    (hN : (normalizer (D : Set G)).Normal)
    (hBS : B ≤ (S : Subgroup G)) (hBC : B ≤ centralizer (S : Set G))
    (hBN : B ≤ normalizer (D : Set G))
    (hcomm : ⁅D, oddCentralizer B⁆ = D) :
    pPrimeCore 2 (centralizer (inducedAutomizer D B : Set (Automizer D))) ≠ ⊥ := by
  let _ := hN
  let N := normalizer (D : Set G)
  let R := oddCentralizer B
  let C := centralizer (B : Set G)
  let f := D.normalizerMonoidHom.rangeRestrict
  have hRN : R ≤ N := le_normalizer_iff_commutator_le_left.mpr hcomm.le
  have hn : C ≤ normalizer (R : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C))
  have hodd : Nat.Coprime 2 (Nat.card R) :=
    pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)
  have hi := map_odd_subgroup_le_of_sylow_central_normal_domain N f
    D.normalizerMonoidHom.rangeRestrict_surjective S B R hBS hBC hBN hRN
    (oddCentralizer_le B) hn hodd
  intro hbot
  change (R.subgroupOf N).map f ≤
    (pPrimeCore 2 (centralizer (inducedAutomizer D B : Set (Automizer D)))).map
      (centralizer (inducedAutomizer D B : Set (Automizer D))).subtype at hi
  rw [hbot, Subgroup.map_bot] at hi
  have hk : R.subgroupOf N ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hi)
  have hRC : R ≤ centralizer (D : Set G) := by
    intro r hr
    have hh : (⟨r, hRN hr⟩ : N) ∈ f.ker := hk hr
    change (⟨r, hRN hr⟩ : N) ∈ D.normalizerMonoidHom.rangeRestrict.ker at hh
    rw [MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker] at hh
    exact hh
  have hc : ⁅D, R⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hRC)
  let _ := hD.2
  let _ : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let _ : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  exact (nontrivial_iff_ne_bot D).mp inferInstance (hcomm.symm.trans hc)

/-- The action odd-core obstruction in E.6.19. The only additional earlier
source input is the normal-or-two-conjugates clause of 1.2.1(3), for the actual
component in C_G(A). Neither odd-core nontriviality nor a balance conclusion
is assumed. The quotient commutator forces the odd action to survive. -/
theorem actionCentralizer_oddCore_ne_bot
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U) (hUV : U ≤ V)
    (hL : CentralizerComponent A L)
    (hD : IsComponent (CentralizerQuotient A) (quotientImage A L))
    (hcomm : ⁅quotientImage A L, oddCentralizer (quotientImage A U)⁆ = quotientImage A L)
    (hVN : V ≤ normalizer (L : Set G))
    (horbit : (L.subgroupOf (centralizer (A : Set G))).Normal ∨
      (normalizer (L.subgroupOf (centralizer (A : Set G)) :
        Set (centralizer (A : Set G)))).index = 2) :
    pPrimeCore 2 (actionCentralizer A U L) ≠ ⊥ := by
  let _ := h.elementary
  have hUN := hUV.trans hVN
  obtain ⟨e⟩ := exists_actionCentralizer_equiv h earlier hA hL
    (subspace_le_centralizer (hAU.trans hUV) hUV) hUN
  obtain ⟨S, _, hVS, hVC⟩ := quotient_sylow_geometry h hA
  have hUQ : quotientImage A U ≤ quotientImage A V := map_mono (comap_mono hUV)
  have hN := quotient_component_normalizer_normal h earlier hA hL horbit
  have hBN : quotientImage A U ≤ normalizer (quotientImage A L : Set (CentralizerQuotient A)) := by
    apply map_le_iff_le_comap.mpr
    rw [component_normalizer_preimage h earlier hA hL]
    exact comap_mono hUN
  have hne := oddCore_action_ne_bot_of_normal_normalizer S (quotientImage A U)
    (quotientImage A L) hD hN (hUQ.trans hVS) (hUQ.trans hVC) hBN hcomm
  intro hb
  apply hne
  change pPrimeCore 2 (quotientActionCentralizer A U L) = ⊥
  rw [← pPrimeCore_map_iso 2 e, hb, Subgroup.map_bot]

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
