module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAxes
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureFixedPoint
import Theory.GroupTheory.QuotientActionCentralizer

/-!
# The actual four-group and residual in the dual closure branch

The outer branch gives a whole U-image of order four. The original full
commutator kernel transports the residual generation identity to the
same linear action. Its literal J image remains two-perfect with cubic
core quotient, and the original T normalizes both images. The original
point remains cyclic and fixed by J*T; the actual common axis is retained.

Source: Aschbacher--Smith12.7.17--18, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- All original actors needed by the dual common-axis exclusion are
constructed on the same whole quotient and exact action kernel. -/
theorem original_tripleSix_central_closure_axis_data
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    (hsmall : Nat.card (inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))) = 2) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    let Z := zpowers (z:G)
    ∃ (hHW : H ≤ normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g ∈ φ.ker ↔ ∀ w ∈ W, ⁅w,(g:G)⁆ ∈ Z) ∧ pCore 2 φ.range = ⊥ ∧
          Nat.card ((U.subgroupOf H).map φ) = 4 ∧
          (U.subgroupOf H).map φ = ⁅(U.subgroupOf H).map φ,(J.subgroupOf H).map φ⁆ ∧
          IsPPerfect 2 ((J.subgroupOf H).map φ) ∧
          Nat.card (((J.subgroupOf H).map φ) ⧸ pCore 2 ((J.subgroupOf H).map φ)) = 3 ∧
          (J.subgroupOf H).map φ ≤ normalizer ((U.subgroupOf H).map φ : Set _) ∧
          ((T : Subgroup G).subgroupOf H).map φ ≤
            normalizer ((U.subgroupOf H).map φ : Set _) ⊓ normalizer ((J.subgroupOf H).map φ : Set _) ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            (∀ g : H, (g:G) ∈ J ⊔ (T : Subgroup G) → φ g x = x) ∧
            ∃ f : Module.Dual (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)), f ≠ 0 ∧
              f.ker = AddSubgroup.toZModSubmodule 2
                (Subgroup.toAddSubgroup (((W ⊓ centralizer (U : Set G)).subgroupOf W).map
                  (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
              (∀ g ∈ (U.subgroupOf H).map φ, ∀ v ∈ f.ker, g v = v) ∧
              ChapterG.Section03.FullAction (BinaryTransvectionGroups.dualGroup φ.range)
                (MulAction.orbit (BinaryTransvectionGroups.dualGroup φ.range) f) ∧
              ChapterG.Section03.Decomposition (BinaryTransvectionGroups.dualGroup φ.range)
                (MulAction.orbit (BinaryTransvectionGroups.dualGroup φ.range) f) ∧
              ChapterG.Section03.LocalStructure (BinaryTransvectionGroups.dualGroup φ.range)
                (MulAction.orbit (BinaryTransvectionGroups.dualGroup φ.range) f) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_axes h structural D a z hz hzT hnot hsmall
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,_,x,hx,hpoint,horbit,f,hf,haxis,hfix,hfull,hdec,hlocal⟩ := hrest
  let := he
  obtain ⟨N,hN,hmem,_,_,_,_,_,hgen,_,hcase⟩ :=
    original_tripleSix_central_closure_outer_rank h structural D a z hz hzT hnot
  let : N.Normal := hN
  have hk : φ.ker = N := by ext g; exact (hker g).trans (hmem g).symm
  have heq : Nat.card ((U.subgroupOf H).map φ) =
      Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N)) := by
    apply le_antisymm
    · apply card_map_le_card_map_of_ker_le
      rw [QuotientGroup.ker_mk',hk]
    · apply card_map_le_card_map_of_ker_le
      rw [QuotientGroup.ker_mk',hk]
  have hcard : Nat.card ((U.subgroupOf H).map φ) = 4 :=
    heq.trans (hcase.resolve_left houter)
  let q := QuotientGroup.lift N φ hk.ge
  have hq : q.comp (QuotientGroup.mk' N) = φ := by ext g; rfl
  have hgen' : (U.subgroupOf H).map φ = ⁅(U.subgroupOf H).map φ,(J.subgroupOf H).map φ⁆ := by
    have hh := congrArg (fun B => Subgroup.map q B) hgen
    simpa only [map_commutator,map_map,hq] using hh
  have hJ := original_tripleSix_weightFour_cubic_residual D a z hz hzT
  have hJH : J ≤ H := le_sup_right.trans le_sup_left
  let Jstar := (J.subgroupOf H).map φ
  let jmap : J →* Jstar := (φ.subgroupMap (J.subgroupOf H)).comp
    (subgroupOfEquivOfLe hJH).symm.toMonoidHom
  have hjmap : Function.Surjective jmap :=
    (φ.subgroupMap_surjective (J.subgroupOf H)).comp (subgroupOfEquivOfLe hJH).symm.surjective
  have hpJ : IsPPerfect 2 Jstar := hJ.2.2.1.of_surjective jmap hjmap
  have hJne : Jstar ≠ ⊥ := by
    intro hb
    have hAb : (U.subgroupOf H).map φ = ⊥ := by
      simpa only [show (J.subgroupOf H).map φ = ⊥ from hb,commutator_bot_right] using hgen'
    rw [hAb,card_bot] at hcard
    omega
  have hjne : jmap ≠ 1 := by
    intro hh
    apply hJne
    apply bot_unique
    intro j hj
    obtain ⟨y,hy⟩ := hjmap ⟨j,hj⟩
    have h1 : (⟨j,hj⟩ : Jstar) = 1 := hy.symm.trans (congrArg (fun k : J →* Jstar => k y) hh)
    exact congrArg Subtype.val h1
  have hcubic : Nat.card (Jstar ⧸ pCore 2 Jstar) = 3 :=
    cubic_core_quotient_of_twoPerfect_image hJ.2.2.1 hJ.2.2.2.1 jmap hjmap hjne
  have hnU (B : Subgroup G) (hB : B ≤ normalizer (U : Set G)) :
      (B.subgroupOf H).map φ ≤ normalizer ((U.subgroupOf H).map φ : Set _) :=
    (map_mono ((comap_mono hB).trans (le_normalizer_comap H.subtype))).trans (le_normalizer_map φ)
  have hJN : (J.subgroupOf H).map φ ≤ normalizer ((U.subgroupOf H).map φ : Set _) :=
    hnU J ((hJ.1.trans inf_le_left).trans D.normalizes)
  have hTN : ((T : Subgroup G).subgroupOf H).map φ ≤
      normalizer ((U.subgroupOf H).map φ : Set _) ⊓ normalizer (Jstar : Set _) := by
    refine le_inf (hnU _ (((structural K h).2.2 U D).1)) ?_
    exact (map_mono ((comap_mono hJ.2.1).trans (le_normalizer_comap H.subtype))).trans
      (le_normalizer_map φ)
  obtain ⟨hHW',hZN',he',φ',hformula',_,_,x',hx',hpoint',_,hfixed⟩ :=
    original_tripleSix_central_closure_fixed_point h structural D a z hz hzT hnot
  have hφ : φ = φ' := by
    apply MonoidHom.ext
    intro g
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,hw⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) v.toMul
    have hv : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w) = v := congrArg Additive.ofMul hw
    rw [←hv,hformula,hformula']
  have hxx : x = x' := by
    have hm : x ∈ Submodule.span (ZMod 2) {x'} := by
      rw [hpoint',←hpoint]
      exact Submodule.mem_span_singleton_self x
    exact ((BinaryTransvectionGroups.mem_centerLine_iff x' x).mp hm).resolve_left hx
  have hfixed' : ∀ g : H, (g:G) ∈ J ⊔ (T : Subgroup G) → φ g x = x := by
    intro g hg
    rw [hφ,hxx]
    exact hfixed g hg
  exact ⟨hHW,hZN,he,φ,hformula,hker,hcore,hcard,hgen',hpJ,hcubic,hJN,hTN,
    x,hx,hpoint,horbit,hfixed',f,hf,haxis,hfix,hfull,hdec,hlocal⟩

end CFSG.Quasithin.Chapter12.Section07
