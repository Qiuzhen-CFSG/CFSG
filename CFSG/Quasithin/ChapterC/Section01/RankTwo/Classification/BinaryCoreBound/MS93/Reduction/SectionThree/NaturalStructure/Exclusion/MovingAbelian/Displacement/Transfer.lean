module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Quotient

/-!
# Passing radius displacement to the moving central quotient

A radius intersection whose critical-actor commutators lie in Z maps to
fixed vectors in the actual quotient P/Z(P), where P = Vcirc. Its index
therefore bounds fixed codimension. A genuine local frame gives the marked
projection and its exact kernel; the endpoint actor is elementary and has
nontrivial image. The image order, rather than the actor order, supplies the
rank in the final inequality.

The last theorem is a conditional transfer: the geometric intersection and
index estimates must both be proved before it gives the source displacement
result. All three bad branches enter the proof that the auxiliary commutator
lies in Z. No descent of the two-core action is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.8), printed p.878, from
“Therefore V_alpha prime” through the displayed fixed-index inequality.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives
variable {M : Type*} [Group M] {L R : Subgroup M}

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

variable [Finite M]

/-- A subgroup of the radius that is fixed modulo Z gives a bound on
fixed codimension on the actual moving central quotient. -/
theorem moving_fixedCodim_pow_le_radius_index (geometry : Geometry R)
    (hb : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a)
    (E K : Subgroup (FreeAmalgam R))
    (hcomm : ⁅V R a ⊓ K, E⁆ ≤ Z R a) :
    letI := moving_central_quotient_elementary geometry (by omega) a ha hfixed
    2 ^ fixedCodim (Offenders.linearize (movingQuotientAction a))
      (E.subgroupOf (stabilizer R a)) ≤ K.relIndex (V R a) := by
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  let := finite_moving geometry hb a ha
  let P := Vcirc R a
  let q := QuotientGroup.mk' (center P)
  let ρ := Offenders.linearize (movingQuotientAction a)
  let A := E.subgroupOf (stabilizer R a)
  let C := Subgroup.toAddSubgroup.symm (fixedSpace ρ A).toAddSubgroup
  have hPV : P ≤ V R a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (V_normalized a))
  have hVQ := geometry.V_le_Q hb a ha
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hZC : Z R a ≤ centralizer (P : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
      (centralizer_le (hPV.trans hVQ))
  have hKC : K.subgroupOf P ≤ C.comap q := by
    intro p hp e
    have he : (e.val : FreeAmalgam R) ∈ E := e.property
    let d : P := movingAction a e.val p * p⁻¹
    have hd : (d : FreeAmalgam R) ∈ Z R a := by
      have hcomm' : ⁅E, V R a ⊓ K⁆ ≤ Z R a := by rwa [commutator_comm]
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
  exact hindex.trans (relIndex_le_of_le_right hPV (K.subgroupOf (V R a)).index_ne_zero_of_finite)

/-- In all three bad branches the critical auxiliary commutator lies in
Z at the starting endpoint, including the outer branch where X differs from Z. -/
theorem bad_critical_commutator_le_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅X R a, X R a'⁆ ≤ Z R a := by
  have hle := (critical_commutator_le_intersection source geometry hb a ha a' hc).trans inf_le_left
  rcases hbad with h | h | h
  · exact hle.trans_eq (SourceCalculation.splitDouble_X_eq_Z source geometry hb h a ha)
  · exact hle.trans_eq (SourceCalculation.centralExtension_X_eq_Z source geometry hb h a ha)
  · have ha' := critical_endpoint_color R a ha _ hc
    have hr := source.critical_reverse geometry a ha a' ha' hc
    exact (commutator_mono le_rfl
      (critical_X_le_stabilizer source geometry hb a' ha' a hr)).trans
      ((SourceCalculation.Outer.X_commutator_le_U source geometry hb h a ha).trans (U_le_Z a))

/-- The exact marked projection and the genuine critical endpoint actor. -/
theorem critical_projected_actor (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ∃ π : stabilizer R a →* SL, Function.Surjective π ∧
      π.ker = (Q R a).subgroupOf (stabilizer R a) ∧
      IsElementaryAbelian 2 ((X R a').subgroupOf (stabilizer R a)) ∧
      ((X R a').subgroupOf (stabilizer R a)).map π ≠ ⊥ ∧
      Nat.card (((X R a').subgroupOf (stabilizer R a)).map π) =
        (Q R a).relIndex (X R a') := by
  obtain ⟨frame⟩ := SourceCalculation.exists_frame a ha
  let π := frame.projection source
  have ha' := critical_endpoint_color R a ha _ hc
  have hr := source.critical_reverse geometry a ha a' ha' hc
  have hES := critical_X_le_stabilizer source geometry hb a' ha' a hr
  let := X_elementary R a'
  let := IsElementaryAbelian.subgroupOf (p := 2) hES
  refine ⟨π, frame.projection_surjective source, frame.projection_kernel source,
    inferInstance, ?_, ?_⟩
  · intro hz
    have hh := (Subgroup.map_eq_bot_iff _).mp hz
    rw [frame.projection_kernel source] at hh
    exact (critical_endpoint_choice source geometry hb a ha a' hc).2
      (fun z hz => hh (show (⟨z, hES ((critical_endpoint_choice source geometry hb a ha a' hc).1 hz)⟩ :
        stabilizer R a) ∈ (X R a').subgroupOf (stabilizer R a) from
          (critical_endpoint_choice source geometry hb a ha a' hc).1 hz))
  · rw [← relIndex_ker, frame.projection_kernel source, subgroupOf, relIndex_comap,
      map_subgroupOf_eq_of_le hES]


/-- The source radius estimates imply the projected-actor inequality on
P/Z(P). The two geometric estimates remain explicit in this transfer lemma. -/
theorem moving_projected_offender_of_radius_bounds
    (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false)
    (hfixed : ⁅V R a, V R a⁆ ≤ fixedCore R a)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R)
    (hintersection : ⁅V R a ⊓ Q R c, X R a'⁆ ≤ ⁅X R a, X R a'⁆)
    (hindex : (Q R c).relIndex (V R a) ≤ (Q R a).relIndex (X R a')) :
    letI := moving_central_quotient_elementary geometry (by omega) a ha hfixed
    ∃ (π : stabilizer R a →* SL) (A : Subgroup (stabilizer R a)),
      Function.Surjective π ∧ π.ker = (Q R a).subgroupOf (stabilizer R a) ∧
      IsElementaryAbelian 2 A ∧ A.map π ≠ ⊥ ∧
      fixedCodim (Offenders.linearize (movingQuotientAction a)) A ≤ rank (A.map π) := by
  let := moving_central_quotient_elementary geometry (by omega) a ha hfixed
  obtain ⟨π, hπ, hker, hA, hne, hcard⟩ :=
    critical_projected_actor source geometry (by omega) a ha a' hc
  let A := (X R a').subgroupOf (stabilizer R a)
  let : IsElementaryAbelian 2 A := hA
  have hAI : IsElementaryTwo (A.map π) := ⟨hne, IsElementaryAbelian.map π⟩
  refine ⟨π, A, hπ, hker, hA, hne, ?_⟩
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hAI.card_eq_two_pow_rank, hcard]
  exact (moving_fixedCodim_pow_le_radius_index geometry hb a ha hfixed (X R a') (Q R c)
    (hintersection.trans (bad_critical_commutator_le_Z source geometry (by omega) hbad a ha a' hc))).trans hindex

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
