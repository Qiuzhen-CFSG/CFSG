module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryClosure
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointFixed
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterRank
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointOrdinaryCenterCover
public import Theory.SpecificGroups.PSL3Even.TwoRank

/-!
# The original field point is the whole ordinary center

Once the ordinary central quotient is identified with PSL₃(4), its two-rank
forces the intersection of the original U with the component center to be
the original field point Vt. The elementary full-plane cover calculation
then shows that this intersection is the entire center. Both subgroups
remain the original embedded subgroups of G throughout.

Source: Aschbacher--Smith, 12.7.5, printed p.840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- For the literal ordinary closure, a PSL₃(4) central quotient determines
the center as exactly the original hexacode field point Vt. -/
theorem original_tripleSix_point_ordinary_center_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (J : Subgroup (centralizer ({(t : G)} : Set G)))
    (hJ : IsComponent (centralizer ({(t : G)} : Set G)) J) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    (B ⧸ center B ≃* Matrix.PSL3Four.PSL) →
      centerIn B = tripleSixPoint D a t := by
  dsimp only
  intro e
  let H := centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
  let B := conjugateSpanBy Lt H
  let V := tripleSixPoint D a t
  change B ⧸ center B ≃* Matrix.PSL3Four.PSL at e
  change centerIn B = V
  have hOrd := original_tripleSix_point_ordinary_closure_at h structural D a t ht heven J hJ
  have hBH : B ≤ H := conjugateSpanBy_le_self ((map_subtype_le _).trans inf_le_right)
  let : IsQuasisimple (B.subgroupOf H) := hOrd.2.1.2
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hBH)
  have hZ : center B = pCore 2 B := by
    apply map_injective B.subtype_injective
    simpa only [centerIn_eq_map_center,pCoreIn] using hOrd.2.2.2
  have hk : IsPGroup 2 (center B) := by rw [hZ]; exact pCore_isPGroup
  have hLB : Lt ≤ B := le_conjugateSpanBy Lt H
  have hUB : U ≤ B :=
    (tripleSixPointCentralizerResidual_commutator D a t ht heven).2.trans hLB
  have hV := tripleSixPoint_properties D a t ht
  have hVB : V ≤ B := hV.2.1.trans hUB
  let : IsElementaryAbelian 2 U := D.elementary
  let : IsElementaryAbelian 2 (U.subgroupOf B) := IsElementaryAbelian.subgroupOf hUB
  have hUc : Nat.card (U.subgroupOf B) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUB).toEquiv).trans
      ((Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card)
  have hVc : Nat.card (V.subgroupOf B) = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVB).toEquiv).trans hV.2.2.1
  have hUV : U.subgroupOf B ⊓ center B ≤ V.subgroupOf B := by
    intro x hx
    change (x : G) ∈ V
    rw [show V = U ⊓ centralizer (Lt : Set G) from
      (tripleSixPoint_residual_fixed D a t ht heven).symm]
    refine ⟨hx.1,?_⟩
    apply mem_centralizer_iff.mpr
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hx.2 ⟨l,hLB hl⟩)
  have hr : primeRank 2 Matrix.PSL3Four.PSL ≤ 4 := by
    rw [Matrix.PSL3Even.two_rank Matrix.PSL3Four.F (n := 2) (by decide)
      (by simpa using Matrix.PSL3Four.card_F)]
  have hI := original_point_inf_center_eq_of_rank_four
    (U.subgroupOf B) (V.subgroupOf B) hUc hVc e hr hUV
  have hcenter := original_point_psl_three_four_center_eq_inf
    (U.subgroupOf B) hUc e hk (by rw [hI]; exact hVc)
  rw [centerIn_eq_map_center,hcenter,hI,map_subgroupOf_eq_of_le hVB]

end CFSG.Quasithin.Chapter12.Section07
