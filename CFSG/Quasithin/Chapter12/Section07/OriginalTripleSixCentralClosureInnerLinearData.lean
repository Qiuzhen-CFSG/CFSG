module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerIntersections
public import CFSG.Quasithin.ChapterG.Section03.LocalRank.PointRadical

/-!
# Exact low-dimensional linear data for the original inner closure

The original whole closure has order 16 or32, so the binary quotient has
dimension three or four. Its original U-image lies in the point radical,
of order at most eight; the proved rank parity therefore makes its order
exactly four. The same full conjugation representation and complete kernel
are retained, together with the unchanged R-image equality.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The same literal original action is full linear of degree three or four,
and the unchanged original U has precisely four elements in that action. -/
theorem original_tripleSix_central_closure_inner_linear_data
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
    ∃ (hHW : H≤normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ φ : H →* (Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] Additive (W ⧸ Z.subgroupOf W)),
          (∀ (g : H) (w : W), φ g (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)) =
            Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) ∧
          (∀ g : H, g∈φ.ker ↔ ∀ w∈W, ⁅w,(g:G)⁆∈Z) ∧
          φ.range=⊤ ∧ (R.subgroupOf H).map φ=⊤ ∧
          (Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W))=3 ∨
            Module.finrank (ZMod 2) (Additive (W ⧸ Z.subgroupOf W))=4) ∧
          Nat.card ((U.subgroupOf H).map φ)=4 ∧
          ∃ x : Additive (W ⧸ Z.subgroupOf W), x≠0 ∧
            Submodule.span (ZMod 2) {x}=AddSubgroup.toZModSubmodule 2
              (Subgroup.toAddSubgroup ((V1.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)))) ∧
            (U.subgroupOf H).map φ≤BinaryLinear.radical (BinaryTransvectionGroups.centerLine x) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hr⟩ := original_tripleSix_central_closure_full_actor
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,_,hcard,x,hx,hpoint,_,hfix,hmove,_,_,_,_,_,_,hwhole,hRimage,hdim⟩ := hr
  let := he
  let V := Additive (W ⧸ Z.subgroupOf W)
  let A := (U.subgroupOf H).map φ
  have hp := tripleSixPoint_properties D a z hz
  let : IsElementaryAbelian 2 U := D.elementary
  have hzorder : orderOf (z:G)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property)
    (fun hh => hz (Subtype.ext hh))
  have hZW : Z≤W := (zpowers_le.mpr hp.1).trans (le_conjugateSpanBy V1 R)
  have hZcard : Nat.card Z=2 := by rw [Nat.card_zpowers,hzorder]
  have hc := (Z.subgroupOf W).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,hZcard] at hc
  change Nat.card (W ⧸ Z.subgroupOf W)*2=Nat.card W at hc
  have hv := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V)
  rw [Nat.card_zmod] at hv
  change Nat.card (W ⧸ Z.subgroupOf W)=_ at hv
  have hne := original_tripleSix_central_closure_not_card_sixtyFour h structural D a z hz hzT hnot hinner
  change Nat.card W≠64 at hne
  have hd : Module.finrank (ZMod 2) V=3 ∨ Module.finrank (ZMod 2) V=4 := by
    rcases hdim with hh | hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
    · rw [hh] at hv
      norm_num at hv
      omega
  have hAR : A≤BinaryLinear.radical (BinaryTransvectionGroups.centerLine x) := by
    intro g hg
    refine ⟨?_,hmove g hg⟩
    intro v hv
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul,hfix g hg]
  have hbound := card_le_of_le hAR
  rw [ChapterG.Section03.LocalRank.point_radical_card hx] at hbound
  have hfour : Nat.card A=4 := by
    change Nat.card A=4 ∨ Nat.card A=16 at hcard
    rcases hd with hd | hd <;> rw [hd] at hbound <;> norm_num at hbound <;> omega
  exact ⟨hHW,hZN,he,φ,hformula,hker,hwhole,hRimage.trans hwhole,hd,hfour,x,hx,hpoint,hAR⟩

end CFSG.Quasithin.Chapter12.Section07
