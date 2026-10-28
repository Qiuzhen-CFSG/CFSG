module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterOrthogonal
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAffineModel
import Theory.GroupTheory.SylowNormalizedResidual
import Theory.GroupTheory.PCoreSurjective
import Theory.GroupTheory.ResidualGeneratedFourSymmetricFour
import Theory.GroupTheory.SubgroupTransport
public import Theory.SpecificGroups.SymmetricFourSylow

/-!
# The actual local image inside the central-closure group

The original local J T acts on U with full weight-four stabilizer image
and entire kernel U. Its two-core is the literal product U W. This gives
the order and core needed to recognize the same local modulo W.

Source: Aschbacher--Smith, following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource ChapterE Atlas.Codes
open Section04.SLThreeCommutatorSource.ConjugateExistence
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original point local has order3072, with two-core U W and
full weight-four action image retaining kernel U and every U vector. -/
theorem original_tripleSix_central_closure_local_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let J := tripleSixWeightFourResidual K z
    let L := J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    let v := (tripleSixPointCoordinates D a z).toAdd
    Nat.card L = 3072 ∧ L.pCoreIn 2 = U ⊔ W ∧
      ∃ q : L →* Hexacode.fullVectorStabilizer v,
        Function.Surjective q ∧ q.ker = U.subgroupOf L ∧
        (∀ (g : L) (u : U),
          ((tripleSixPointCoordinates D a).symm (Multiplicative.ofAdd
            (Hexacode.action (q g).val (tripleSixPointCoordinates D a u).toAdd)) : G) =
            (g:G) * (u:G) * (g:G)⁻¹) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let L := J ⊔ (T : Subgroup G)
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let M := normalizer (K : Set G)
  let A := K ⊓ C
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  let S := Hexacode.fullVectorStabilizer v
  have hv := tripleSix_sylow_fixed_weightFour D a z hz hzT
  obtain ⟨hKcore, _, _, hNU, _, hMT⟩ := original_tripleSix_central_closure_core_recovery
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  obtain ⟨hMU, f, hf, _, hfk, _, hformula, _⟩ := original_tripleSix_central_closure_local_model
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  have hTM : (T : Subgroup G) ≤ M := by
    change (T : Subgroup G) ≤ normalizer (K : Set G)
    rw [hMT]
    exact le_sup_right
  have hJK : J ≤ K := (map_subtype_le _).trans inf_le_left
  have hJC : J ≤ C := (map_subtype_le _).trans inf_le_right
  have hLM : L ≤ M := sup_le (hJK.trans K.le_normalizer) hTM
  have hLC : L ≤ C := sup_le hJC hzT
  have hUL : U ≤ L := D.le_sylow.trans le_sup_right
  have hAL : A ≤ L := le_embedded_pResidual_sup_sylow_of_normalizes T A
    ((le_inf D.sylow_normalizes_component (hzT.trans C.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf)
  have hUA : U ≤ A := le_inf D.le_component (D.le_sylow.trans hzT)
  have hUc : Nat.card U = 64 := (Nat.card_congr c.toEquiv).trans hexacode_card
  let π := f.comp (inclusion hLM)
  have hπS (g : L) : π g ∈ S := by
    have hh := hformula (inclusion hLM g) z
    have hcz : (g:G) * (z:G) * (g:G)⁻¹ = z :=
      mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp (hLC g.property))
    change (c.symm (Multiplicative.ofAdd (Hexacode.action (π g) v)) : G) =
      (g:G) * (z:G) * (g:G)⁻¹ at hh
    rw [hcz] at hh
    have he : c.symm (Multiplicative.ofAdd (Hexacode.action (π g) v)) = z := Subtype.ext hh
    have he' := congrArg c he
    rw [c.apply_symm_apply] at he'
    exact congrArg Multiplicative.toAdd he'
  let q : L →* S := π.codRestrict S hπS
  have hqk : q.ker = U.subgroupOf L := by
    ext g
    change (⟨π g, hπS g⟩ : S) = 1 ↔ (g:G) ∈ U
    rw [Subtype.ext_iff]
    change inclusion hLM g ∈ f.ker ↔ _
    rw [hfk]
    rfl
  have hqkc : Nat.card q.ker = 64 := by
    rw [hqk, Nat.card_congr (subgroupOfEquivOfLe hUL).toEquiv, hUc]
  have hS : Nat.card S = 48 := Hexacode.fullWeightFourVectorStabilizer_card v hv
  have hcount := q.ker.card_mul_index
  rw [index_ker, hqkc] at hcount
  have hbound : Nat.card L ≤ 3072 := by
    have hr : Nat.card q.range ≤ 48 := (card_le_of_le (show q.range ≤ ⊤ from le_top)).trans_eq
      ((card_top (G := S)).trans hS)
    omega
  let p := tripleSixPointCentralizerProjection D a z
  have hpk : p.ker = U.subgroupOf A := by
    rw [tripleSixPointCentralizerProjection_ker]
    have hk : pCore 2 K = U.subgroupOf K := by
      apply map_injective K.subtype_injective
      rw [map_subgroupOf_eq_of_le D.le_component]
      exact hKcore
    rw [hk]
    rfl
  have hAc : Nat.card A = 1536 := by
    have hh := p.ker.card_mul_index
    rw [index_ker, MonoidHom.range_eq_top.mpr (tripleSixPointCentralizerProjection_surjective D a z),
      card_top, Hexacode.weightFourVectorStabilizer_card v hv, hpk,
      Nat.card_congr (subgroupOfEquivOfLe hUA).toEquiv, hUc] at hh
    exact hh.symm
  have hTc : Nat.card T = 1024 :=
    (original_tripleSix_central_closure_affine_model
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter).1
  have hd : 3072 ∣ Nat.card L := by
    have ha : 1536 ∣ Nat.card L := hAc ▸ card_dvd_of_le hAL
    have ht' : 1024 ∣ Nat.card L := hTc ▸ card_dvd_of_le (show (T : Subgroup G) ≤ L from le_sup_right)
    have hh := Nat.lcm_dvd ha ht'
    norm_num at hh ⊢
    exact hh
  have hLc : Nat.card L = 3072 := le_antisymm hbound (Nat.le_of_dvd Nat.card_pos hd)
  have hq : Function.Surjective q := by
    apply MonoidHom.range_eq_top.mp
    apply eq_of_le_of_card_ge le_top
    rw [card_top, hS]
    omega
  have hqkp : IsPGroup 2 q.ker := by
    rw [hqk]
    exact (T.isPGroup'.to_le D.le_sylow).of_injective
      (subgroupOfEquivOfLe hUL).toMonoidHom (subgroupOfEquivOfLe hUL).injective
  have hcoreS : Nat.card (pCore 2 S) = 8 := by
    obtain ⟨e, _, _, _⟩ := Hexacode.fullWeightFourVectorStabilizer_model v hv
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, pCore_map_iso]
    exact Theory.SpecificGroups.SymmetricSix.DuadCalculation.productCore_eq ▸
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.productCore_card
  have hcorec : Nat.card (L.pCoreIn 2) = 512 := by
    rw [pCoreIn, card_map_of_injective L.subtype_injective,
      q.card_pCore_of_ker_isPGroup hq hqkp, hqkc, hcoreS]
  obtain ⟨hWT, hHW, hWc, hIc, _⟩ := original_tripleSix_central_closure_outer_extraspecial
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  have hLH : L ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hWL : W ≤ L := hWT.trans le_sup_right
  have hLU : L ≤ normalizer (U : Set G) := hLM.trans hMU
  have hUWcore : U ⊔ W ≤ L.pCoreIn 2 := sup_le
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le D.le_sylow) hUL hLU)
    (le_pCoreIn_of_normalizes (T.isPGroup'.to_le hWT) hWL (hLH.trans hHW))
  have hUWc : Nat.card (U ⊔ W : Subgroup G) = 512 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes U W (hWL.trans hLU)
    rw [hUc, hWc, hIc] at hh
    omega
  have hcore : L.pCoreIn 2 = U ⊔ W :=
    (eq_of_le_of_card_ge hUWcore (by rw [hcorec, hUWc])).symm
  exact ⟨hLc, hcore, q, hq, hqk, fun g u => hformula (inclusion hLM g) u⟩

/-- The literal J T quotient by W is S4. The complete kernel is W and
the image of the original U is its entire two-core. -/
theorem original_tripleSix_central_closure_local_symmetric_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let J := tripleSixWeightFourResidual K z
    let L := J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    ∃ hLW : L ≤ normalizer (W : Set G),
      letI := normal_subgroupOf_of_le_normalizer hLW
      ∃ e : (L ⧸ W.subgroupOf L) ≃* Equiv.Perm (Fin 4),
        ((U.subgroupOf L).map (QuotientGroup.mk' (W.subgroupOf L))).map e.toMonoidHom =
          pCore 2 (Equiv.Perm (Fin 4)) ∧
        ∃ q : L →* Equiv.Perm (Fin 4), Function.Surjective q ∧
          q.ker = W.subgroupOf L ∧ (U.subgroupOf L).map q = pCore 2 (Equiv.Perm (Fin 4)) ∧
          ∀ g : L, e (QuotientGroup.mk' (W.subgroupOf L) g) = q g := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let L := J ⊔ (T : Subgroup G)
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let V := tripleSixPoint D a z
  obtain ⟨hLc, hcore, _⟩ := original_tripleSix_central_closure_local_core
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  obtain ⟨hWT, hHW, hWc, hIc, _⟩ := original_tripleSix_central_closure_outer_extraspecial
    h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  have hLH : L ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  have hLW : L ≤ normalizer (W : Set G) := hLH.trans hHW
  have hWL : W ≤ L := hWT.trans le_sup_right
  have hUL : U ≤ L := D.le_sylow.trans le_sup_right
  have hJL : J ≤ L := le_sup_left
  have hVU : V ≤ U := (tripleSixPoint_properties D a z hz).2.1
  have hVW : V ≤ W := le_conjugateSpanBy V R
  have hLU : L ≤ normalizer (U : Set G) := sup_le
    (((map_subtype_le _).trans inf_le_left).trans D.normalizes)
    (((structural K h).2.2 U D).1)
  let W0 := W.subgroupOf L
  let U0 := U.subgroupOf L
  let J0 := J.subgroupOf L
  let : W0.Normal := normal_subgroupOf_of_le_normalizer hLW
  let : U0.Normal := normal_subgroupOf_of_le_normalizer hLU
  let X := L ⧸ W0
  let p : L →* X := QuotientGroup.mk' W0
  have hp : Function.Surjective p := QuotientGroup.mk'_surjective W0
  let B := U0.map p
  let := D.elementary
  let : IsElementaryAbelian 2 U0 := IsElementaryAbelian.subgroupOf hUL
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map p
  let : B.Normal := Normal.map inferInstance p hp
  have hW0c : Nat.card W0 = 128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv).trans hWc
  have hXc : Nat.card X = 24 := by
    have hh := W0.index_mul_card
    change Nat.card X * Nat.card W0 = Nat.card L at hh
    rw [hLc, hW0c] at hh
    omega
  have hU0c : Nat.card U0 = 64 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUL).toEquiv]
    exact (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
  have hindex : W.relIndex U = 4 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ W) U bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hIc,
      (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card] at hh
    omega
  have hBc : Nat.card B = 4 := by
    rw [show B = U0.map p from rfl, ←relIndex_ker, QuotientGroup.ker_mk']
    exact (relIndex_subgroupOf hUL).trans hindex
  have hpkp : IsPGroup 2 p.ker := by
    rw [QuotientGroup.ker_mk']
    exact (T.isPGroup'.to_le hWT).of_injective
      (subgroupOfEquivOfLe hWL).toMonoidHom (subgroupOfEquivOfLe hWL).injective
  have hcoreL : pCore 2 L = U0 ⊔ W0 := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUL, map_subgroupOf_eq_of_le hWL]
    exact hcore
  have hBcore : pCore 2 X = B := by
    have he := p.comap_pCore_of_ker_isPGroup hp hpkp
    have hh := congrArg (Subgroup.map p) he
    rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hp]; exact le_top),
      hcoreL, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at hh
    exact hh
  obtain ⟨_, _, hJperfect, _, hUJ, _⟩ := original_tripleSix_weightFour_cubic_residual D a z hz hzT
  have hJ0perfect : IsPPerfect 2 J0 := hJperfect.of_surjective
    (subgroupOfEquivOfLe hJL).symm.toMonoidHom (subgroupOfEquivOfLe hJL).symm.surjective
  have hJres : J0.map p ≤ pResidual 2 X := le_pResidual_of_isPPerfect _
    (hJ0perfect.of_surjective (p.subgroupMap J0) (p.subgroupMap_surjective J0))
  have hVzero : (V.subgroupOf L).map p = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [QuotientGroup.ker_mk']
    exact fun _ hx => hVW hx
  have hcomm : ⁅B, J0.map p⁆ = B := by
    have he := congrArg (fun A : Subgroup G => (A.subgroupOf L).map p) hUJ
    rw [subgroupOf_sup
      ((Subgroup.commutator_le_sup U J).trans (sup_le hUL hJL)) (hVU.trans hUL),
      Subgroup.map_sup, Theory.GroupTheory.SubgroupTransport.subgroupOf_commutator U J hUL hJL,
      map_commutator, hVzero, sup_bot_eq] at he
    exact he.symm
  have hcommres : ⁅B, pResidual 2 X⁆ = B := le_antisymm (commutator_le_left _ _)
    (hcomm.ge.trans (commutator_mono le_rfl hJres))
  obtain ⟨e⟩ := symmetricFour_of_residual_generated_four B hBc hXc hBcore.le hcommres
  let q := e.toMonoidHom.comp p
  have hqk : q.ker = W0 := by
    ext x
    change e (p x) = 1 ↔ x ∈ W0
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hUimage : U0.map q = pCore 2 (Equiv.Perm (Fin 4)) := by
    rw [show U0.map q = B.map e.toMonoidHom from (map_map _ _ _).symm,
      ←hBcore, pCore_map_iso]
  refine ⟨hLW, e, ?_, q, e.surjective.comp hp, hqk, hUimage, ?_⟩
  · rw [map_map]
    exact hUimage
  · intro g
    rfl

/-- Every action with the frozen full kernel W has the same original local
S4 image and original dihedral Sylow image; the local quotient map retains
exactly the restriction of that action kernel. -/
theorem original_tripleSix_central_closure_local_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G))
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (seven : ∀ Y : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T Y →
      ¬ Nonempty ((Y ⧸ centralPreimage (pCore 2 Y)) ≃* alternatingGroup (Fin 7)))
    (exits : ∀ H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃* alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧ RankOneModule.SmallExit T (localResidual H))
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let L := J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    ∃ hLH : L ≤ H, ∀ {Y : Type*} [Group Y] (r : H →* Y), r.ker = W.subgroupOf H →
      ∃ q : L →* Equiv.Perm (Fin 4), Function.Surjective q ∧
        q.ker = W.subgroupOf L ∧ q.ker = (r.comp (inclusion hLH)).ker ∧
        (U.subgroupOf L).map q = pCore 2 (Equiv.Perm (Fin 4)) ∧
        Nonempty (((L.subgroupOf H).map r) ≃* Equiv.Perm (Fin 4)) ∧
        Nonempty ((((T : Subgroup G).subgroupOf H).map r) ≃* DihedralGroup 4) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let L := J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  have hLH : L ≤ H := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  refine ⟨hLH, ?_⟩
  intro Y _ r hr
  obtain ⟨hLW, e, _, q, hq, hqk, hUq, _⟩ :=
    original_tripleSix_central_closure_local_symmetric_four
      h structural modules D a t ht heven contained hmany seven exits z hz hzT hnot houter
  have hsame : q.ker = (r.comp (inclusion hLH)).ker := by
    rw [hqk]
    ext g
    change (g:G) ∈ W ↔ inclusion hLH g ∈ r.ker
    rw [hr]
    rfl
  let f := r.comp (inclusion hLH)
  let E : f.range ≃* Equiv.Perm (Fin 4) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hsame.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective q hq))
  have hfrange : f.range = (L.subgroupOf H).map r := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨inclusion hLH g, g.property, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g.val, hg⟩, rfl⟩
  have hTL : (T : Subgroup G) ≤ L := le_sup_right
  let S := T.subtype hTL
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := S.mapSurjective hq
  obtain ⟨d⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  let F : L →* f.range := f.rangeRestrict
  have hEF : E.toMonoidHom.comp F = q := by
    apply MonoidHom.ext
    intro g
    have he : (QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict g) =
        QuotientGroup.mk' f.ker g := by
      apply (QuotientGroup.quotientKerEquivRange f).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    change (QuotientGroup.quotientKerEquivOfSurjective q hq)
      ((QuotientGroup.quotientMulEquivOfEq hsame.symm)
        ((QuotientGroup.quotientKerEquivRange f).symm (f.rangeRestrict g))) = q g
    rw [he]
    rfl
  have hSP : ((S : Subgroup L).map F).map E.toMonoidHom = (P : Subgroup (Equiv.Perm (Fin 4))) := by
    rw [map_map, hEF]
    rfl
  let eS : (S : Subgroup L).map F ≃* P :=
    (((S : Subgroup L).map F).equivMapOfInjective E.toMonoidHom E.injective).trans
      (MulEquiv.subgroupCongr hSP)
  let eF : (S : Subgroup L).map F ≃* (S : Subgroup L).map f :=
    (((S : Subgroup L).map F).equivMapOfInjective f.range.subtype f.range.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [map_map]; rfl))
  have hTmap : (S : Subgroup L).map f = ((T : Subgroup G).subgroupOf H).map r := by
    change ((T : Subgroup G).subgroupOf L).map (r.comp (inclusion hLH)) = _
    rw [←map_map]
    congr 1
    apply map_injective H.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (hTL.trans hLH)]
    change ((T : Subgroup G).subgroupOf L).map L.subtype = _
    exact map_subgroupOf_eq_of_le hTL
  refine ⟨q, hq, hqk, hsame, hUq, ?_, ?_⟩
  · exact ⟨(MulEquiv.subgroupCongr hfrange.symm).trans E⟩
  · exact ⟨(MulEquiv.subgroupCongr hTmap.symm).trans (eF.symm.trans (eS.trans d))⟩

end CFSG.Quasithin.Chapter12.Section07
