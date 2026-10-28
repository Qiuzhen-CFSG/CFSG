module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Quotient

/-!
# The moving-radius action and its actual fixed codimension

The derived radius is fixed, so the moving radius has an elementary
central quotient. Residual commutator generation survives on this quotient.
The intersection with a midpoint kernel acts trivially modulo the center:
its endpoint commutators lie in X, and X centralizes the entire radius.
The proved radius-image bound therefore gives fixed codimension at most
two for the actual critical endpoint actor.

This is the binary A₆ instance of the fixed-index step in MS93 (3.8),
printed p.878. No trivial action of the two-core on this quotient is
assumed. The action and quotient are those constructed in
Exclusion.MovingAbelian.Quotient; the index transport adapts its companion
Displacement.Transfer with the sufficient X-centralization bound.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (m : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h m hz)
  (r : Replacement L R)

/-- The literal moving radius has an elementary central quotient. -/
theorem moving_quotient_elementary
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false) :
    IsElementaryAbelian 2 ((Vcirc r.radical a) ⧸ center (Vcirc r.radical a)) :=
  moving_central_quotient_elementary (replacementGeometry h r) (replacementDistance_pos h r)
    a ha (radius_derived_le_fixed h m hz hn r himage fg a ha)


set_option backward.isDefEq.respectTransparency false in
private theorem moving_full_of_commutator {M : Type*} [Group M] {T : Subgroup M}
    (a : Vertex T) [IsElementaryAbelian 2 ((Vcirc T a) ⧸ center (Vcirc T a))]
    (hfull : ⁅Vcirc T a,Ltilde T a⁆ = Vcirc T a) :
    subspaceCommutator (Offenders.linearize (movingQuotientAction a))
      ⊤ (pResidual 2 (stabilizer T a)) = ⊤ := by
  let P := Vcirc T a
  let q := QuotientGroup.mk' (center P)
  let ρ := Offenders.linearize (movingQuotientAction a)
  let W := subspaceCommutator ρ ⊤ (pResidual 2 (stabilizer T a))
  let J : Subgroup (P ⧸ center P) := Subgroup.toAddSubgroup.symm W.toAddSubgroup
  have hP : P ≤ (J.comap q).map P.subtype := by
    change Vcirc T a ≤ _
    conv_lhs => rw [← hfull, commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    obtain ⟨g, hg, rfl⟩ := hl
    let vP : P := ⟨v, hv⟩
    refine ⟨movingAction a g vP * vP⁻¹, ?_, ?_⟩
    · change Additive.ofMul (q (movingAction a g vP * vP⁻¹)) ∈ W
      have hh : ρ g (Additive.ofMul (q vP)) - Additive.ofMul (q vP) ∈ W :=
        Submodule.subset_span ⟨g, hg, Additive.ofMul (q vP), Submodule.mem_top, rfl⟩
      simp only [ρ, Offenders.linearize, sub_eq_add_neg] at hh
      change Additive.ofMul (movingQuotientAction a g (q vP) * (q vP)⁻¹) ∈ W at hh
      rw [movingQuotientAction_apply] at hh
      simpa only [map_mul, map_inv] using hh
    · change (movingAction a g vP : FreeAmalgam T) * v⁻¹ = _
      rw [movingAction_apply]
      rfl
  apply top_unique
  intro v _
  obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective (center P) v.toMul
  obtain ⟨w, hw, he⟩ := hP p.property
  have hpJ : p ∈ J.comap q := (Subtype.ext he : w = p) ▸ hw
  change Additive.ofMul (q p) ∈ W at hpJ
  change v ∈ W
  have hv : Additive.ofMul (q p) = v := congrArg Additive.ofMul hp
  exact hv ▸ hpJ

set_option backward.isDefEq.respectTransparency false in
/-- The original residual generates the entire moving central quotient by commutators. -/
theorem moving_quotient_full (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) :
    letI := moving_quotient_elementary h m hz hn r himage fg a ha
    subspaceCommutator (Offenders.linearize (movingQuotientAction a))
      ⊤ (pResidual 2 (stabilizer r.radical a)) = ⊤ := by
  let := moving_quotient_elementary h m hz hn r himage fg a ha
  exact moving_full_of_commutator a (moving_full_commutation h r
    (show 2 < replacementDistance h r by rw [fg.distance]; decide) a ha)

private theorem fixedSpace_subgroup_index {G T : Type*} [Group G] [Group T]
    [IsElementaryAbelian 2 T] [Finite T] (action : G →* MulAut T) (A : Subgroup G) :
    (Subgroup.toAddSubgroup.symm
      (fixedSpace (Offenders.linearize action) A).toAddSubgroup).index =
      2 ^ fixedCodim (Offenders.linearize action) A := by
  let ρ := Offenders.linearize action
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  let e : fixedSpace ρ A ≃ C := {
    toFun := fun v => ⟨v.val.toMul, v.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (fixedSpace ρ A) := by
    have hf := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A)
    rw [Nat.card_zmod] at hf
    exact (Nat.card_congr e).symm.trans hf
  have hT : Nat.card T = 2 ^ Module.finrank (ZMod 2) (Additive T) :=
    (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive T)).trans (by rw [Nat.card_zmod])
  have hdim := fixedCodim_add_finrank ρ A
  have hmul := C.card_mul_index
  rw [hC, hT, ← hdim, pow_add, Nat.mul_comm (2 ^ fixedCodim ρ A)] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul


/-- X-centralization suffices for the exact central-quotient fixed-index transport. -/
theorem moving_fixedCodim_pow_le_radius_index (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r) (a : Vertex r.radical) (ha : color r.radical a = false)
    (E K : Subgroup (FreeAmalgam r.radical))
    (hcomm : ⁅V r.radical a ⊓ K, E⁆ ≤ X r.radical a) :
    letI := moving_quotient_elementary h m hz hn r himage fg a ha
    2 ^ fixedCodim (Offenders.linearize (movingQuotientAction a))
      (E.subgroupOf (stabilizer r.radical a)) ≤ K.relIndex (V r.radical a) := by
  let := moving_quotient_elementary h m hz hn r himage fg a ha
  let geometry := replacementGeometry h r
  have hb : 2 < geometry.b r.radical := by
    change 2 < replacementDistance h r
    rw [fg.distance]
    decide
  let := finite_moving geometry hb a ha
  let P := Vcirc r.radical a
  let q := QuotientGroup.mk' (center P)
  let ρ := Offenders.linearize (movingQuotientAction a)
  let A := E.subgroupOf (stabilizer r.radical a)
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  have hPV : P ≤ V r.radical a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hVQ := geometry.V_le_Q hb a ha
  let := finite_stabilizer r.radical a
  let : Finite (V r.radical a) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hZC : X r.radical a ≤ centralizer (P : Set (FreeAmalgam r.radical)) :=
    (le_centralizer_iff.mp (Q_le_centralizer_X r.radical a)).trans
      (centralizer_le (hPV.trans hVQ))
  have hKC : K.subgroupOf P ≤ C.comap q := by
    intro p hp e
    have he : (e.val : FreeAmalgam r.radical) ∈ E := e.property
    let d : P := movingAction a e.val p * p⁻¹
    have hd : (d : FreeAmalgam r.radical) ∈ X r.radical a := by
      have hcomm' : ⁅E, V r.radical a ⊓ K⁆ ≤ X r.radical a := by rwa [commutator_comm]
      exact hcomm' (commutator_mem_commutator he ⟨hPV p.property, hp⟩)
    have hdC : d ∈ center P := by
      apply mem_center_iff.mpr
      intro v
      apply Subtype.ext
      exact hZC hd v v.property
    change Additive.ofMul (movingQuotientAction a e.val (q p)) = Additive.ofMul (q p)
    apply congrArg Additive.ofMul
    rw [movingQuotientAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [div_eq_mul_inv] using hdC
  have hindex : C.index ≤ (K.subgroupOf P).index := by
    rw [← C.index_comap_of_surjective (QuotientGroup.mk'_surjective (center P))]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (K.subgroupOf P).index_ne_zero_of_finite)
      (index_dvd_of_le hKC)
  rw [fixedSpace_subgroup_index] at hindex
  exact hindex.trans (relIndex_le_of_le_right hPV (K.subgroupOf (V r.radical a)).index_ne_zero_of_finite)


/-- The actual critical endpoint has fixed codimension at most two on the
moving central quotient; all radius-index and intersection premises are discharged. -/
theorem critical_moving_fixedCodim_le_two
    (himage : (projection h m hz hn r).range = alternatingGroup (Fin 6))
    (fg : FourGeometry h r)
    (a : Vertex r.radical) (ha : color r.radical a = false) (a' : Vertex r.radical)
    (hc : CriticalPair r.radical a a' ((replacementGeometry h r).exists_critical a ha))
    (c : Vertex r.radical) (hcColor : color r.radical c = false)
    (hac : (cosetGraph r.radical).dist a c = 2)
    (hca' : (cosetGraph r.radical).dist c a' = 2) :
    letI := moving_quotient_elementary h m hz hn r himage fg a ha
    fixedCodim (Offenders.linearize (movingQuotientAction a))
      ((X r.radical a').subgroupOf (stabilizer r.radical a)) ≤ 2 := by
  let := moving_quotient_elementary h m hz hn r himage fg a ha
  have hcomm : ⁅V r.radical a ⊓ Q r.radical c,X r.radical a'⁆ ≤ X r.radical a :=
    (radius_intersection_X h m hz hn r himage fg a ha a' hc c hca').trans
      ((Estimates.critical_X_commutator h r m hz hn himage a ha a' hc).1.trans inf_le_left)
  have hpow := (moving_fixedCodim_pow_le_radius_index h m hz hn r himage fg a ha
    (X r.radical a') (Q r.radical c) hcomm).trans
      (radius_index_le_four h m hz hn r himage fg a ha a' hc c hcColor hac hca')
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (show _ ≤ 2 ^ 2 from hpow)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
