module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SourceAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalLinearAmalgam

/-!
# The linear alternative for the original nonsolvable centralizer pair

The original pair supplies every applicability premise of the retained
13.4.7 input. In its linear alternative, the actual S₃ parabolic excludes
the outer extension of the L₃(2) component. The resulting quotient lattice
identifies the unique outside parabolic and its intersection with L₂T.
In every local overgroup Y, the centralizer of the full orbit of Ω₁Z(T)
lies in the intersection of the two original parabolics, hence in T.
The source overgroup formula therefore gives Y=H₀. Applying this to the
normalizer of the nontrivial Thompson subgroup identifies H₀=N_G(J(T))
and proves maximal two-locality, as required in 13.4.10(8ii).

PlaneAmalgamSource1347 remains an explicit earlier-source input owned by
qt-d-1341-fixed-core-source. Its product commutator alternative alone does
not supply the module-weight conclusions of 13.4.10(8i). Those conclusions,
the both-weight comparison, and the later commutator and graph arguments
remain with qt-d-1341-nonsolvable-source.
Source: Aschbacher–Smith 13.4.10(8), printed pp.909–910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The linear alternative is the full Thompson normalizer and is maximal
among two-local subgroups. The literal intersection data discharges the
centralizer term in the earlier overgroup formula. -/
theorem original_linear_pair_maximal
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P B : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hTB : (T : Subgroup G) ≤ B) (hBM : B ≤ normalizer (L : Set G))
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hlocal : P ⊔ B ∈ Chapter1.HOver G (T : Set G))
    (hinter : ∀ Y : Subgroup G, Y ∈ Chapter1.H G → P ≤ Y → B ≤ Y →
      Y ⊓ normalizer (L : Set G) = B ∧ Y ⊓ centralizer ({z} : Set G) = P)
    (hlinear : Solvable.LinearAmalgamConclusion T (P ⊔ B)) :
    P ⊔ B = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
      IsMaximalTwoLocal (P ⊔ B) ∧
      Nonempty (((P ⊔ B : Subgroup G) ⧸ pCore 2 (P ⊔ B : Subgroup G)) ≃* Matrix.PSL3Two.SL) ∧
      (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        Q ≤ P ⊔ B → Q = P) := by
  let X := P ⊔ B
  obtain ⟨⟨K,_,_,_,hTK,hX,⟨eK⟩⟩,hnormal,hsupp⟩ := hlinear
  obtain ⟨e⟩ := Solvable.third_quotient_of_normalized_linear_component X K P hX hTK eK
    hP.1.1.2 le_sup_left eP
  let e' : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL := e.trans Matrix.PSL3Two.equiv.symm
  have hout : ¬ X ≤ normalizer (L : Set G) := fun hh => hP.1.2 (le_sup_left.trans hh)
  have hTB' : (T : Subgroup G) < B := lt_of_le_not_ge hTB (fun hh =>
    Solvable.not_twoGroup_of_symmetricThree_quotient eB (T.isPGroup'.to_le hh))
  have hBX : B < X := lt_of_le_not_ge le_sup_right (fun hh => hout (hh.trans hBM))
  obtain ⟨Q,_,_,_,_,hBP,hunique⟩ := small_quotient_unique_outside T
    (normalizer (L : Set G)) X B D.sylow_normalizes_component hlocal hout hTB' hBX hBM
    (Or.inl ⟨e'⟩)
  have hPQ : P = Q := hunique P hP le_sup_left
  rw [←hPQ] at hBP hunique
  have hcent : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G) := by
    rw [←fixed_centralizer_eq_normalizer h structural D m]
    exact centralizer_le (Solvable.fixed_le_original_omegaCenter h structural D m)
  have hover (Y : Subgroup G) (hY : Y ∈ Chapter1.H G) (hXY : X ≤ Y) : Y ≤ X := by
    obtain ⟨hYM,hYH⟩ := hinter Y hY (le_sup_left.trans hXY) (le_sup_right.trans hXY)
    have hc : Y ⊓ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X : Set G) ≤
          (T : Subgroup G) := by
      apply le_trans ?_ hBP.le
      intro c hc
      have hcz := centralizer_le (le_conjugateSpanBy
        (omegaOneCenterAmbient (T : Subgroup G)) X) hc.2
      refine ⟨?_,?_⟩
      · rw [←hYM]
        exact ⟨hc.1,hcent hcz⟩
      · rw [←hYH]
        exact ⟨hc.1,centralizer_le (Set.singleton_subset_iff.mpr hz) hcz⟩
    intro y hy
    obtain ⟨a,ha,c,hc',rfl⟩ := (hsupp Y ⟨hY,hXY⟩).le hy
    exact X.mul_mem ha (hlocal.2 (hc hc'))
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let N := normalizer (J : Set G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hN : IsTwoLocal N :=
    ⟨J,Solvable.original_maxJ_ne_bot D m,T.isPGroup'.to_le hJT,rfl⟩
  have heq : X = N := le_antisymm hnormal
    (hover N (Chapter1.mem_H_of_isTwoLocal hN) hnormal)
  refine ⟨heq,?_,⟨e'⟩,hunique⟩
  refine ⟨?_,?_⟩
  · change IsTwoLocal X
    rwa [heq]
  · intro Y hY hXY
    exact hover Y (Chapter1.mem_H_of_isTwoLocal hY) hXY

/-- Apply the precise earlier 13.4.7 consequence to the constructed ordinary
A₆ pair, and fully identify the linear alternative's normalizer and quotient.
The product case still requires its module and weight analysis. -/
theorem ordinary_six_original_amalgam
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
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ≤ centralizer ({z.val} : Set G) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        X ∈ Chapter1.HOver G (T : Set G) ∧
        (⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∨
          (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P))) := by
  obtain ⟨W,hW,hT,P,hP,hPH,⟨eP⟩,⟨eB⟩,_,hlocal,_,hchief,hiP,hiB,_,hcentral⟩ :=
    ordinary_six_original_pair h₀ h structural modules D m h1332 fixed hindex hM
      z hzT hzL hK hHN hKM hfK eK
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
  refine ⟨W,hW,hT,P,hP,hPH.le,hlocal,?_⟩
  rcases hc.2 with hc | hc
  · exact Or.inl hc
  · exact Or.inr ⟨hc,original_linear_pair_maximal h structural D m z.val hzT P B hP hTB
      hBM eP eB hlocal (fun Y hY hPY hBY =>
        ⟨(hcentral Y hY hPY hBY).1,(hcentral Y hY hPY hBY).2.1⟩) hc⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
