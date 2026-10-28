module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.SemisimpleWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LineCoreSocle
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModule

/-!
# Weight and socle alternatives for the original nonsolvable pair

Whole-module recognition supplies one of the three actual six-dimensional
linear models under one quotient marking. Applying the semisimple, point-core
and line-core calculations gives the original weight, residual commutator
and full-H₀ socle alternatives without an additional chosen-model premise.

The source application constructs the original H₂,L₂T pair for either
recognized component row. It obtains the whole omega-center containment
from that recognition, applies the earlier plane amalgam, and discharges
all local hypotheses of the linear alternatives. The product alternative
retains its weight-four and component-commutator bounds. The companion
LineCoreSocle and SemisimpleWeights theorems give the component membership
and reciprocal five-dimensional weights in their respective rows.

The original earlier-source inputs, M=LT, plane amalgam and independent
LargeDistanceInput remain explicit. Universal escaping-weight comparison,
13.4.15, product 13.4.16 and the final graph contradiction remain with this
nonsolvable assembly. Source: Aschbacher–Smith 13.4.14, printed p.911,
refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Representation.BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- Exhaust all three linear models and transfer their weight and socle
conclusions to the original full actor and its literal residual. -/
theorem original_linear_weight_socle_alternatives
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hAM : ¬ A ≤ normalizer (L : Set G))
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B)) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z (A ⊔ B)
    let F := V ⊓ centralizer (L : Set G)
    let R := ⁅Z,(pResidual 2 A).map A.subtype⁆
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
      let Soc := (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule
      Nat.card U = 64 ∧
      ((m.weight z = 4 ∧ F ≤ R) ∨
       (m.weight z = 2 ∧ F ≤ R ∧ binarySpace (F.subgroupOf U) ≤ Soc) ∨
       (m.weight z = 4 ∧ ¬ F ≤ R ∧ ¬ binarySpace (F.subgroupOf U) ≤ Soc)) := by
  let X := A ⊔ B
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨he,q,hqA,hqB,hqT,hm,hcard⟩ := Amalgam.original_pair_linear_whole_module
    h₀ h structural D m hTA hTB eA eB hne (fun hx => hAM (le_sup_left.trans hx))
    hindex hiA hiB hres h1332 K hC.2 eK
  refine ⟨he,hcard,?_⟩
  rcases hm with hm | hm | hm
  · exact Or.inl (original_semisimple_weight_and_commutator h₀ D m h1332 hTA hTB eA eB
      hne hiA hiB K hC.2 eK he q hqA hqB hqT hm.some h structural hM hZV W hW hTW hB
      z hzT hzL hAz)
  · exact Or.inr (Or.inl (original_point_core_weight_and_socle h₀ D m h1332 hTA hTB
      eA eB hne hiA hiB K hC.2 eK he q hqA hqB hqT hm.some h structural hM hZV W hW hTW hB
      z hzT hzL hAz hAM))
  · exact Or.inr (Or.inr (original_line_core_weight_and_socle h₀ D m h1332 hTA hTB
      eA eB hne hiA hiB K hC.2 eK he q hqA hqB hqT hm.some h structural hM hZV W hW hTW hB
      z hzT hzL hAz))

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
/-- Construct the original pair in either recognized component row and
discharge the model selection and omega-containment premises. -/
theorem small_component_original_weight_socle_amalgam
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
            let Z := omegaOneCenterAmbient (T : Subgroup G)
            let U₀ := conjugateSpanBy Z X
            let F := V ⊓ centralizer (L : Set G)
            let R := ⁅Z,K₂⁆
            ∃ he : IsElementaryAbelian 2 U₀, let := he
              let ρ := elementaryRepresentation (p := 2)
                (U₀.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
              let Soc := (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule
              Nat.card U₀ = 64 ∧
              ((m.weight z = 4 ∧ F ≤ R) ∨
               (m.weight z = 2 ∧ F ≤ R ∧ binarySpace (F.subgroupOf U₀) ≤ Soc) ∨
               (m.weight z = 4 ∧ ¬ F ≤ R ∧ ¬ binarySpace (F.subgroupOf U₀) ≤ Soc)))) := by
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
  · have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V := by
      rcases model with he | he <;> obtain ⟨eK⟩ := he
      · obtain ⟨_,_,_,_,_,_,_,_,_,hZ,_⟩ := linear_component_geometry
          hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hHN hKM hfK eK
        exact hZ.le.trans inf_le_left
      · obtain ⟨_,_,_,_,_,_,hZ,_⟩ := ordinary_six_component_geometry
          h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hHN hKM hfK eK
        exact hZ.le.trans inf_le_left
    refine Or.inr ⟨hc,?_⟩
    exact original_linear_weight_socle_alternatives h₀ D m h1332 hP.1.1.2 hTB eP eB
      hne hiP hiB h structural hM hZV W hW hT rfl z hzT hzL hPH.le hP.1.2
      hindex (hcentral' hlocal).2.2 hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
