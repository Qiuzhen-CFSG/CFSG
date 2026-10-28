module
public import ABG.ChapterII.Section2.QDCharacterization
public import ABG.ChapterII.Section2.WreathedFrameRestriction
public import ABG.ChapterII.Section2.AutomizerRestriction
public import ABG.ChapterII.Section1.WreathedVNormalizerRestriction

/-!
# Involution centralizers in wreathed QD-groups

For a finite group with a wreathed QD fusion frame, every involution
centralizer satisfies the complete original Q-group definition. The actual
restricted Sylow subgroup, base, and quaternion central product are retained.

The canonical central-product normalizer fixes the Sylow center pointwise.
Restricting its fusion frame to the centralizer of a central involution
therefore preserves outer automizer index six. The central involution cannot
be conjugate to both distinct base involutions, ruling out the QD pattern.
The D and normal-complement patterns have outer index two, so only Q remains.
The unique ambient involution class conjugates a central Sylow involution
to the specified one. Choosing a canonical frame on the conjugate Sylow and
using the proved no-index-two characterization recovers its full QD pattern.

This is the wreathed branch of ABG Chapter II, Section 2, Proposition 1,
article p.15 (`refs/latex/alperin-brauer-gorenstein-pages/page-016.tex`).
The companion quasi-dihedral branch and final shape assembly are separate.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem not_one_class_of_central_involution
    (S : Sylow 2 G) {n : ℕ} (P : Wreathed.Presentation S n)
    (z : G) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center G) :
    ¬ HasElementConjugacyClassCount G 2 1 := by
  intro hc
  obtain ⟨r, _, _, hcov⟩ := hc
  obtain ⟨i, hzi⟩ := hcov z hz
  have hall (x : G) (hx : orderOf x = 2) : x = z := by
    obtain ⟨j, hxj⟩ := hcov x hx
    have hzx : IsConj z x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
    obtain ⟨g, hg⟩ := isConj_iff.mp hzx
    symm
    simpa only [Subgroup.mem_center_iff.mp hzc g, mul_assoc,
      mul_inv_cancel, mul_one] using hg
  have hx : (P.x : G) = z := hall P.x ((Subgroup.orderOf_coe P.x).trans P.x_orderOf)
  have hx₂ : (P.x₂ : G) = z := hall P.x₂ ((Subgroup.orderOf_coe P.x₂).trans P.x₂_orderOf)
  exact P.x_not_isConj_x₂ ((Subtype.ext (hx.trans hx₂.symm)) ▸ IsConj.refl P.x)

private theorem central_case
    (S : Sylow 2 G) {n : ℕ} (P : Wreathed.Presentation S n)
    (hV : outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) = 6)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ Subgroup.center S) :
    IsFullSylowQGroup (Subgroup.centralizer {(z : G)}) := by
  let C := Subgroup.centralizer {(z : G)}
  let U := P.U.map (S : Subgroup G).subtype
  let V := P.V.map (S : Subgroup G).subtype
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc (⟨s, hs⟩ : S)))
  have hfC := wreathedFusionFrame_subtype S n U V C hSC (P.fusionFrame S)
  have hNV : Subgroup.normalizer (V : Set G) ≤ C := by
    have hN := (Wreathed.canonical_v_normalizer_structure S P).2.1
    intro g hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (hN hg z ⟨z, hzc, rfl⟩).symm
  have hVC : outerAutomizerIndex (V.subgroupOf C) = 6 :=
    (outerAutomizerIndex_subgroupOf C V hNV).trans hV
  have hzC : (z : G) ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let zC : C := ⟨z, hzC⟩
  have hzCcent : zC ∈ Subgroup.center C := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp g.property
  obtain ⟨PC⟩ := Wreathed.nonempty_presentation hfC.1
  have hnot := not_one_class_of_central_involution (S.subtype hSC) PC zC
    ((Subgroup.orderOf_coe zC).symm.trans ((Subgroup.orderOf_coe z).trans hz)) hzCcent
  rcases Wreathed.proposition_two (S.subtype hSC) n
    (U.subgroupOf C) (V.subgroupOf C) hfC with h | h | h | h
  · exact (hnot h.2.1).elim
  · exact Or.inr ⟨S.subtype hSC, n, U.subgroupOf C, V.subgroupOf C, hfC, h⟩
  · have hbad := h.2.2.2
    omega
  · have hbad := h.2.2.2
    omega

public theorem wreathedQD_involutionCentralizer_isFullSylowQGroup
    (S : Sylow 2 G) (n : ℕ) (U V : Subgroup G)
    (hframe : WreathedFusionFrame S n U V) (hQD : WreathedQDPattern U V)
    (x : G) (hx : orderOf x = 2) :
    IsFullSylowQGroup (Subgroup.centralizer {x}) := by
  obtain ⟨P⟩ := Wreathed.nonempty_presentation hframe.1
  obtain ⟨r, _, _, hcov⟩ := hQD.2.1
  obtain ⟨i, hzi⟩ := hcov P.x ((Subgroup.orderOf_coe P.x).trans P.x_orderOf)
  obtain ⟨j, hxj⟩ := hcov x hx
  have hzx : IsConj (P.x : G) x := hzi.trans ((Subsingleton.elim i j) ▸ hxj.symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp hzx
  let e := S.equivSMul g
  have hS' : IsWreathedOfHeight (g • S : Sylow 2 G) n :=
    wreathed_equiv e hframe.1
  obtain ⟨P'⟩ := Wreathed.nonempty_presentation hS'
  have hQD' := wreathed_qdPattern_of_no_normal_index_two (g • S) n _ _
    (P'.fusionFrame (g • S)) hQD.1
  have hz' : orderOf (e P.x) = 2 := (e.orderOf_eq P.x).trans P.x_orderOf
  have hzc' : e P.x ∈ Subgroup.center (g • S : Sylow 2 G) := by
    apply Subgroup.mem_center_iff.mpr
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp P.x_mem_center v)
  have hh := central_case (g • S) P' hQD'.2.2.2 (e P.x) hz' hzc'
  have he : ((e P.x : (g • S : Sylow 2 G)) : G) = x := hg
  rw [he] at hh
  exact hh

end ABG

