module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Construction
public import CFSG.Quasithin.Chapter15.Section01.ChosenCoreIntersection
public import Theory.GroupTheory.PResidual.PrimeConjugateLift
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.Representation.BinaryOffender.FixedSpaceFaithfulness

/-!
# The moving central cubic lift in the exact source residual

The actual module centralizer lies in M ∩ Mc, so its commutator with
R = O₂(M ∩ Mc) lies in O₂(M). The prepared module kills that two-core.
If R moves the center of the extraspecial action residual, the relative
prime-lift theorem constructs an actual order-three subgroup in
O²(⟨R^{X₀}⟩), where X₀ is the literal central preimage in M.

The extraspecial center has zero fixed space in the faithful binary
six-space. Its lift normalizes the original marked four-group and moves
all of it by coprime action. The existing component consumer in the
parent Extraspecial module keeps that same marking and selected component.

Existence of ImageMarking and nontrivial action of R on the center remain
source obligations of qt-e-1515-exchanged-component-selection. This module
proves the lifting and movement implication, not those source premises.
The quotient is the actual action quotient, and the source residual is
not replaced by O²(R ∨ X₀).

Source: Aschbacher--Smith 14.1.17(3), 15.1.16(c), and 15.1.24,
printed pp.980,1092,1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The source kernel commutator is contained in the original local two-core. -/
theorem kernel_intersection_core_commutator
    {M Mc V : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) :
    ⁅(actionHom M V hn).ker, ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M := by
  let H := (M ⊓ Mc).subgroupOf M
  have hCH : (actionHom M V hn).ker ≤ H := by
    intro x hx
    rw [actionHom_ker] at hx
    exact ⟨x.property, hC ⟨x.property, hx⟩⟩
  have he : H.pCoreIn 2 = ((M ⊓ Mc).pCoreIn 2).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_pCoreIn_of_injective 2 H M.subtype M.subtype_injective,
      show H.map M.subtype = M ⊓ Mc from map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)]
  exact he ▸ commutator_pCoreIn_le_of_normal (p := 2) (actionHom M V hn).ker H hCH

/-- Transport of the exact source residual through M's subtype. -/
theorem sourceCentralLiftResidual_eq_map
    (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) :
    sourceCentralLiftResidual M Mc V hn =
      ((pResidual 2 (conjugateSpanBy (((M ⊓ Mc).pCoreIn 2).subgroupOf M)
        (((center (pResidual 2 (internalActionImage M V hn))).map
          (pResidual 2 (internalActionImage M V hn)).subtype).comap
            (actionHom M V hn).rangeRestrict))).map
        (conjugateSpanBy (((M ⊓ Mc).pCoreIn 2).subgroupOf M)
          (((center (pResidual 2 (internalActionImage M V hn))).map
            (pResidual 2 (internalActionImage M V hn)).subtype).comap
              (actionHom M V hn).rangeRestrict)).subtype).map M.subtype := by
  rw [map_embedded_pResidual,map_conjugateSpanBy,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)]
  rfl

/-- The ambient prepared module discharges the source kernel bound. Only
movement of the actual residual center remains explicit. -/
theorem sourceCentralLiftResidual_prime_lift
    (T : Sylow 2 G) {M Mc V : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hmove : letI := h.elementary
      ¬ (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
        centralizer (((center (pResidual 2 (internalActionImage M V h.normalized))).map
          (pResidual 2 (internalActionImage M V h.normalized)).subtype) : Set
            (internalActionImage M V h.normalized))) :
    letI := h.elementary
    ∃ X : Subgroup M, Nat.card X = 3 ∧
      X.map M.subtype ≤ sourceCentralLiftResidual M Mc V h.normalized ∧
      X.map (actionHom M V h.normalized).rangeRestrict =
        (center (pResidual 2 (internalActionImage M V h.normalized))).map
          (pResidual 2 (internalActionImage M V h.normalized)).subtype := by
  let := h.elementary
  let f : M →* internalActionImage M V h.normalized :=
    (actionHom M V h.normalized).rangeRestrict
  let P := pResidual 2 (internalActionImage M V h.normalized)
  let Z := (center P).map P.subtype
  let : P.Normal := by dsimp only [P]; infer_instance
  let : Z.Normal := by dsimp only [Z]; infer_instance
  obtain ⟨_,_,_,hP,_,_,_,_⟩ := hex
  let := hP
  have hZ : Nat.card Z = 3 := by
    rw [card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 3 P
  have hker : f.ker = (actionHom M V h.normalized).ker := by
    ext m
    exact ⟨fun hm => congrArg Subtype.val hm,fun hm => Subtype.ext hm⟩
  have hcore : pCore 2 M ≤ f.ker := by
    rw [hker,actionHom_ker]
    have hi := le_centralizer_iff.mp (h.reduced T hTM).le_centralizer_pCore
    intro x hx v hv
    exact congrArg M.subtype (hi hx ⟨v,h.le_selected hv⟩ hv)
  have hcomm : ⁅f.ker, ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M := by
    rw [hker]
    exact kernel_intersection_core_commutator h.normalized
      (inf_le_right.trans (h.centralizer_le_partner T hu))
  obtain ⟨X,hX,hcard,himage⟩ := exists_prime_lift_in_twoResidual_conjugateSpan f
    (actionHom M V h.normalized).rangeRestrict_surjective Z
    (by rw [hZ]; decide) (by rw [hZ]; decide)
    (pCore 2 M) (((M ⊓ Mc).pCoreIn 2).subgroupOf M) pCore_isPGroup hcore
    (isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype hcomm hmove
  refine ⟨X,hcard.trans hZ,?_,himage⟩
  rw [sourceCentralLiftResidual_eq_map]
  exact map_mono hX

/-- A lift of the original central cubic moves the same marked four-group. -/
theorem ImageMarking.central_lift_moves
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (c : ImageMarking T M V hn) (X : Subgroup M) (hX : Nat.card X = 3)
    (himage : X.map (actionHom M V hn).rangeRestrict =
      (center (pResidual 2 (internalActionImage M V hn))).map
        (pResidual 2 (internalActionImage M V hn)).subtype) :
    ⁅fixedSubgroup M V hn c.X, X.map M.subtype⁆ = fixedSubgroup M V hn c.X := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let P := pResidual 2 D
  let ZP := (center P).map P.subtype
  let A := c.X.map P.subtype
  let W := fixedSpace ρ A
  let Z := fixedSubgroup M V hn c.X
  let Y := X.map M.subtype
  have hplanes := source_image_planes T hn hex c.X c.card_X c.noncentral
  change X.map f = ZP at himage
  obtain ⟨_,_,_,hP,hcard,_,hdim,_⟩ := hex
  let := hP
  let σ := ρ.comp P.subtype
  have hfaith : Function.Injective σ :=
    (imageRepresentation_injective M V hn).comp P.subtype_injective
  let : IsIrreducible σ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six σ
    hfaith hcard hdim
  have hzero : fixedSpace ρ ZP = ⊥ := by
    rw [←fixedSpace_comp_map]
    change invariants (σ.comp (center P).subtype) = ⊥
    by_contra hh
    have hh' := Representation.le_ker_of_normal_invariants_ne_bot σ (center P) hh
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff σ).mpr hfaith] using hh')
    have hc := IsExtraspecial.center_order_p 3 P
    rw [hb,card_bot] at hc
    omega
  have hcom : ⁅ZP,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro z ⟨z,hz,rfl⟩ a ⟨a,ha,rfl⟩
    exact congrArg Subtype.val (mem_center_iff.mp hz a)
  have hnormW : ZP ≤ subspaceStabilizer ρ W :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ ZP A hcom
  have hZV : Z ≤ V := map_subtype_le _
  have hnorm : Y ≤ normalizer (Z : Set G) := by
    apply le_normalizer_iff.mpr
    rintro y ⟨x,hx,rfl⟩ z ⟨v,hv,rfl⟩
    refine ⟨(actionHom M V hn x) v,?_,rfl⟩
    have hfx : f x ∈ ZP := himage ▸ mem_map_of_mem f hx
    exact (hnormW hfx (Additive.ofMul v)).mpr hv
  have hfixed : Z ⊓ centralizer (Y : Set G) = ⊥ := by
    apply bot_unique
    intro z hz
    obtain ⟨v,hv,rfl⟩ := hz.1
    have hvfix : Additive.ofMul v ∈ fixedSpace ρ ZP := by
      rw [←himage]
      rintro ⟨a,⟨x,hx,rfl⟩⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change (x : G) * (v : G) * (x : G)⁻¹ = v
      have hc : (x : G) * (v : G) = (v : G) * x :=
        hz.2 x (mem_map_of_mem M.subtype hx)
      rw [hc,mul_inv_cancel_right]
    rw [hzero,Submodule.mem_bot] at hvfix
    exact congrArg (fun w : Additive V => (w.toMul : G)) hvfix
  have hZcard : Nat.card Z = 4 := by
    change Nat.card ((binarySubgroup W).map V.subtype) = 4
    rw [card_map_of_injective V.subtype_injective,binarySubgroup_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      hplanes.1]
    norm_num
  let : IsMulCommutative Z := .of_setLike_mul_comm fun a ha b hb =>
    setLike_mul_comm (hZV ha) (hZV hb)
  have hs : Group.IsSolvable Z := Group.isSolvable_of_comm fun x y => mul_comm x y
  have hc : Nat.Coprime (Nat.card Y) (Nat.card Z) := by
    rw [card_map_of_injective M.subtype_injective,hX,hZcard]
    decide
  have he := eq_commutator_sup_centralizer_of_solvable_coprime Z Y hnorm hs hc
  rw [hfixed,sup_bot_eq] at he
  exact he.symm

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker

namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The same marking has a moving cubic lift in the exact printed residual,
once the intersection core moves the original residual center. The source
assembly in ExchangedSelection retains discharge of that movement premise. -/
theorem ImageMarking.source_cubic_lift_of_center_moved
    (T : Sylow 2 G) {M Mc V : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (c : letI := h.elementary; ImageMarking T M V h.normalized)
    (hmove : letI := h.elementary
      ¬ (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict ≤
        centralizer (((center (pResidual 2 (internalActionImage M V h.normalized))).map
          (pResidual 2 (internalActionImage M V h.normalized)).subtype) : Set
            (internalActionImage M V h.normalized))) :
    letI := h.elementary
    ∃ X₂ : Subgroup G, Nat.card X₂ = 3 ∧
      X₂ ≤ sourceCentralLiftResidual M Mc V h.normalized ∧
      X₂ ≤ centralLiftResidual M Mc V h.normalized ∧
      ⁅fixedSubgroup M V h.normalized c.X,X₂⁆ = fixedSubgroup M V h.normalized c.X := by
  let := h.elementary
  obtain ⟨X,hX,hXY,himage⟩ := sourceCentralLiftResidual_prime_lift T hTM hu h hex hmove
  exact ⟨X.map M.subtype,(card_map_of_injective M.subtype_injective).trans hX,
    hXY,hXY.trans (sourceCentralLiftResidual_le M Mc V h.normalized),
    c.central_lift_moves T h.normalized hex X hX himage⟩

end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
