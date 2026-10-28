module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureBlocks
public import CFSG.Quasithin.ChapterG.Section03.SQTKTwoBlocks
public import CFSG.Quasithin.ChapterG.Section03.SpanningTwoBlockWreath
import Theory.SpecificGroups.PSL3Two.WreathCubicSylowObstruction

/-!
# The single block in the original inner central-closure action

The two-block case gives the whole marked SL₃(2) wreath actor. The unchanged
original cubic residual maps to a two-perfect subgroup with cubic core
quotient, normalized by the image of the original Sylow two-subgroup.
The intrinsic wreath obstruction excludes that case. The action, full kernel,
point and original central closures are retained throughout.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original inner-automizer branch has exactly one full binary block. -/
theorem original_tripleSix_central_closure_one_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
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
          (Nat.card ((U.subgroupOf H).map φ) = 4 ∨ Nat.card ((U.subgroupOf H).map φ) = 16) ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x ≠ 0 ∧
            Submodule.span (ZMod 2) {x} = AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            Submodule.span (ZMod 2) (Set.range (fun g : φ.range => g.val x)) = ⊤ ∧
            (∀ g ∈ (U.subgroupOf H).map φ, g x = x) ∧
            (∀ g ∈ (U.subgroupOf H).map φ, ∀ y, g y-y ∈ BinaryTransvectionGroups.centerLine x) ∧
            ChapterG.Section03.FullAction φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.Decomposition φ.range (MulAction.orbit φ.range x) ∧
            ChapterG.Section03.LocalStructure φ.range (MulAction.orbit φ.range x) ∧
            (∀ i : ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x),
              (3 ≤ Module.finrank (ZMod 2) (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i) ∧
                Module.finrank (ZMod 2) (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i) ≤ 5) ∧
              ∃ B : Subgroup H, B.IsCComponent ∧ B.map φ.rangeRestrict =
                (ChapterG.Section03.blockGroup φ.range (MulAction.orbit φ.range x) i).subgroupOf φ.range) ∧
            Nat.card (ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x)) = 1 := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_blocks
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hcore,hcard,x,hx,hpoint,horbit,hfix,hmove,hfull,hdecomp,hlocal,hlifts,hcount⟩ := hrest
  let := he
  have hHC : H ≤ C :=
    (original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot).1
  let := D.elementary
  have hz1 : (z:G) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hzorder : orderOf (z:G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHC)).mp
      ((h.simpleQTKE.involution_centralizer_sqtk hzorder).subgroup (H.subgroupOf C))
  have hspan : Submodule.span (ZMod 2) (MulAction.orbit φ.range x) = ⊤ := by
    have heq : MulAction.orbit φ.range x = Set.range (fun g : φ.range => g.val x) := by
      ext y
      exact MulAction.mem_orbit_iff
    rwa [heq]
  have hone : Nat.card (ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x)) = 1 := by
    classical
    let I := ChapterG.Section03.OrbitBlock φ.range (MulAction.orbit φ.range x)
    let i : I := ⟨MulAction.orbit (BinaryTransvectionGroups.generated φ.range
      (MulAction.orbit φ.range x)) x,x,MulAction.mem_orbit_self x,rfl⟩
    let : Nonempty I := ⟨i⟩
    let : Finite I := Finite.of_injective (fun k : I => k.val) Subtype.val_injective
    have hpos : 0 < Nat.card I := Nat.card_pos
    by_contra hne
    have htwo : Nat.card I = 2 := by
      change Nat.card I ≤ 2 at hcount
      change Nat.card I ≠ 1 at hne
      omega
    have hthree (i : I) : Module.finrank (ZMod 2)
        (ChapterG.Section03.blockSpace φ.range (MulAction.orbit φ.range x) i)=3 := by
      obtain ⟨j,hji,_⟩ := (Nat.card_eq_two_iff' i).mp htwo
      exact ChapterG.Section03.sqtk_spanning_block_dimension_three hH φ.range
        φ.rangeRestrict φ.rangeRestrict_surjective x hfull hdecomp hlocal hspan i j hji.symm
    obtain ⟨_,_,_,_,_,_,e,_⟩ := ChapterG.Section03.spanning_two_block_wreath
      φ.range x hfull hdecomp hspan htwo hthree
    let r := e.toMonoidHom.comp φ.rangeRestrict
    have hr : Function.Surjective r := e.surjective.comp φ.rangeRestrict_surjective
    obtain ⟨N,hN,hmem,_,_,_,_,_,_,hJcard⟩ :=
      original_tripleSix_central_closure_rank h structural D a z hz hzT hnot
    let : N.Normal := hN
    have hk : r.ker=N := by
      ext g
      change e (φ.rangeRestrict g)=1 ↔ g∈N
      rw [e.map_eq_one_iff,Subtype.ext_iff]
      change φ g=1 ↔ g∈N
      exact (hker g).trans (hmem g).symm
    let Jbar := (J.subgroupOf H).map (QuotientGroup.mk' N)
    let Jmodel := (J.subgroupOf H).map r
    have hJne : Jmodel≠⊥ := by
      intro hb
      have hJN : J.subgroupOf H≤N := hk ▸ ((J.subgroupOf H).map_eq_bot_iff.mp hb)
      have hb' : Jbar=⊥ := (J.subgroupOf H).map_eq_bot_iff.mpr (by rwa [QuotientGroup.ker_mk'])
      have hbound := Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 Jbar))
        (QuotientGroup.mk'_surjective _)
      change Nat.card (Jbar ⧸ pCore 2 Jbar)=3 at hJcard
      rw [hJcard,hb',card_bot] at hbound
      omega
    have hJH : J≤H := le_sup_right.trans le_sup_left
    let f : J →* Jmodel := (r.subgroupMap (J.subgroupOf H)).comp
      (subgroupOfEquivOfLe hJH).symm.toMonoidHom
    have hf : Function.Surjective f := (r.subgroupMap_surjective (J.subgroupOf H)).comp
      (subgroupOfEquivOfLe hJH).symm.surjective
    have hfn : f≠1 := by
      intro he
      apply hJne
      apply _root_.eq_bot_iff.mpr
      intro y hy
      obtain ⟨b,hb⟩ := hf ⟨y,hy⟩
      have hy1 : (⟨y,hy⟩ : Jmodel)=1 := hb.symm.trans (congrArg (fun k : J →* Jmodel => k b) he)
      exact congrArg Subtype.val hy1
    have hJ := original_tripleSix_weightFour_cubic_residual D a z hz hzT
    have hperfect : IsPPerfect 2 Jmodel := hJ.2.2.1.of_surjective f hf
    have hcubic : Nat.card (Jmodel ⧸ pCore 2 Jmodel)=3 :=
      cubic_core_quotient_of_twoPerfect_image hJ.2.2.1 hJ.2.2.2.1 f hf hfn
    let S := (T.subtype (show (T : Subgroup G)≤H from le_sup_right)).mapSurjective hr
    have hnorm : ((T : Subgroup G).subgroupOf H)≤normalizer (J.subgroupOf H : Set H) :=
      (comap_mono hJ.2.1).trans (le_normalizer_comap H.subtype)
    have hS : (S : Subgroup Matrix.PSL3Two.WreathPair.Actor)≤normalizer (Jmodel : Set _) := by
      change ((T : Subgroup G).subgroupOf H).map r≤normalizer (Jmodel : Set _)
      exact (map_mono hnorm).trans (le_normalizer_map r)
    exact Matrix.PSL3Two.WreathPair.not_sylow_normalized_cubic_residual Jmodel S
      hperfect hcubic hS
  exact ⟨hHW,hZN,he,φ,hformula,hker,hcore,hcard,x,hx,hpoint,horbit,hfix,hmove,
    hfull,hdecomp,hlocal,hlifts,hone⟩

end CFSG.Quasithin.Chapter12.Section07
