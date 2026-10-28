module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLongImages
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSourceGeneration
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCoreAction

/-!
# Original plane radius-index-two conjugate kernels

A radius image of order two makes every escaping seed give the same
commutator line. The two actual edge kernels then centralize that line.
The original cubic critical-kernel equivalence transports the full kernel,
including the central attachment, through the same component element.
Neither a quotient by Q identified with S6 nor an order-three lift is needed.
Source: MS93 (5.11)(1), printed p.923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

private theorem index_two_sup_kernel {F : Type*} [Group F]
    (V Q A : Subgroup F) [Finite V] (hA : A ≤ V)
    (hi : Q.relIndex V = 2) (hne : ¬ A ≤ Q) :
    (V ⊓ Q) ⊔ A = V := by
  let K := V ⊓ Q
  let E := K ⊔ A
  have hEV : E ≤ V := sup_le inf_le_left hA
  let : Finite E := Finite.of_injective (inclusion hEV) (inclusion_injective _)
  have hKV : K.relIndex V = 2 := by simpa only [K,inf_relIndex_left] using hi
  have hne' : K.relIndex E ≠ 1 := by
    intro hh
    exact hne ((le_sup_right.trans (relIndex_eq_one.mp hh)).trans inf_le_right)
  have hpos : 0 < K.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hp : 0 < E.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have ht := relIndex_mul_relIndex K E V le_sup_left hEV
  rw [hKV] at ht
  have htwo : 2 ≤ K.relIndex E := by omega
  have he : E.relIndex V = 1 := by nlinarith
  exact le_antisymm hEV (relIndex_eq_one.mp he)

private theorem index_two_commutator {F : Type*} [Group F]
    (V Q A Z : Subgroup F) [Finite V]
    (hA : A ≤ V) (hi : Q.relIndex V = 2) (hne : ¬ A ≤ Q)
    (hQ : Q ≤ centralizer (Z : Set F)) (hN : V ≤ normalizer (Z : Set F)) :
    ⁅Z,A⁆ = ⁅Z,V⁆ := by
  have he := index_two_sup_kernel V Q A hA hi hne
  exact commutator_eq_of_centralizing_sup he
    (inf_le_right.trans hQ) (hA.trans hN)

include h in
private theorem radius_le_stabilizer_of_dist
    {a c : Vertex Rg} (ha : color Rg a = false)
    (hd : (cosetGraph Rg).dist a c + 2 ≤ sourceDistance h) :
    V Rg a ≤ stabilizer Rg c := by
  apply (V_le_iff Rg ha _).mpr
  intro w hw hwa
  apply Z_le_stabilizer_of_dist_le w _
  rw [(sourceGeometry h).distance_constant w hw]
  have ht : (cosetGraph Rg).dist w c ≤
      (cosetGraph Rg).dist w a + (cosetGraph Rg).dist a c :=
    (cosetGraph_connected Rg).dist_triangle
  change _ ≤ sourceDistance h
  omega

/-- Two escaping seeds in the same radius image produce a line fixed by
the actual generating edge kernels. All groups are original source groups. -/
theorem plane_radius_two_common_line
    (hb : 2 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a c d t : Vertex Rg} (ha : color Rg a = false)
    (hac : (cosetGraph Rg).dist a c + 2 ≤ sourceDistance h)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (x : FreeAmalgam Rg) (hxL : x ∈ Ltilde Rg a)
    (hgen : Q Rg t ⊔ (Q Rg t).map (MulAut.conj x).toMonoidHom = stabilizer Rg a)
    (hfixed : ⁅Z Rg d,Z Rg c⁆ ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)))
    (hi : (Q Rg c).relIndex (V Rg a) = 2)
    (hout : ¬ Z Rg (act Rg x⁻¹ d) ≤ Q Rg c) :
    ⁅Z Rg d,Z Rg c⁆ = ⁅Z Rg (act Rg x⁻¹ d),Z Rg c⁆ ∧
      ⁅Z Rg d,Z Rg c⁆ ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  have hnear : (cosetGraph Rg).dist d a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hdt)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr
      (adjacent_symm Rg hat))
    have ht : (cosetGraph Rg).dist d a ≤
        (cosetGraph Rg).dist d t + (cosetGraph Rg).dist t a :=
      (cosetGraph_connected Rg).dist_triangle
    simpa only [h₁,h₂] using ht
  have hZV : Z Rg d ≤ V Rg a :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hnear)
  have hVG := radius_le_stabilizer_of_dist h ha hac
  have hVQ := (sourceGeometry h).V_le_Q hb a ha
  let := finite_stabilizer Rg a
  let : Finite (V Rg a) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hx : x ∈ stabilizer Rg a := Ltilde_le_stabilizer _ hxL
  have hVmap : (V Rg a).map (MulAut.conj x).toMonoidHom = V Rg a := by
    rw [←inv_inv x,←V_act]
    rw [show act Rg x⁻¹ a = a from (stabilizer Rg a).inv_mem hx]
  have hZV' : Z Rg (act Rg x⁻¹ d) ≤ V Rg a := by
    rw [Z_act,inv_inv,←hVmap]
    exact map_mono hZV
  have hQC : Q Rg c ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c q.end_color))
  have heq : ⁅Z Rg d,Z Rg c⁆ = ⁅Z Rg (act Rg x⁻¹ d),Z Rg c⁆ := by
    rw [commutator_comm (Z Rg d),commutator_comm (Z Rg (act Rg x⁻¹ d))]
    exact (index_two_commutator _ _ _ _ hZV hi q.critical.2 hQC
      (hVG.trans (Z_normalized Rg c))).trans
        (index_two_commutator _ _ _ _ hZV' hi hout hQC
          (hVG.trans (Z_normalized Rg c))).symm
  refine ⟨heq,?_⟩
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [ha] at hh
    cases he : color Rg t <;> simp_all
  have hZcQa : Z Rg c ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c q.end_color)
    rw [(sourceGeometry h).distance_constant c q.end_color,SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist a c < sourceDistance h
    omega
  have hQmap : (Q Rg a).map (MulAut.conj x).toMonoidHom = Q Rg a :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized Rg a) hx)
  have hZcEdge : Z Rg c ≤ Q Rg (act Rg x⁻¹ t) := by
    rw [Q_act,inv_inv]
    exact hZcQa.trans (hQmap ▸ map_mono (Q_le_adjacent_h Rg ht hat))
  have hEdge := plane_edge_seed_commutator h e hz hk u hR
    ((action_preserves_color Rg _ _).trans q.start_color)
    ((adjacent_act_iff Rg x⁻¹ _ _).mpr hdt)
  have hlineEdge : ⁅Z Rg d,Z Rg c⁆ ≤ Z Rg (act Rg x⁻¹ t) := by
    rw [heq]
    exact (commutator_mono le_rfl hZcEdge).trans hEdge
  have hfixed' : ⁅Z Rg d,Z Rg c⁆ ≤ centralizer
      (Q Rg (act Rg x⁻¹ t) : Set (FreeAmalgam Rg)) := by
    intro v hv
    have hh := hlineEdge hv
    rw [Z,if_neg (by rw [action_preserves_color,ht]; decide)] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  apply le_centralizer_iff.mpr
  rw [←hgen]
  apply sup_le (le_centralizer_iff.mp hfixed)
  have hh := le_centralizer_iff.mp hfixed'
  rwa [Q_act,inv_inv] at hh

/-- The same component element transports the full critical kernel into
the conjugate core. Its order is not assumed, and E/Q stays cubic. -/
theorem plane_radius_two_conjugate_kernel
    (hb : 2 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ v w (_p : CriticalPath Rg (sourceGeometry h) v w),
      (Q Rg w).relIndex (Z Rg v) < 4)
    {a c d t : Vertex Rg} (ha : color Rg a = false)
    (hac : (cosetGraph Rg).dist a c + 2 ≤ sourceDistance h)
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (x : FreeAmalgam Rg) (hxL : x ∈ Ltilde Rg a)
    (hgen : Q Rg t ⊔ (Q Rg t).map (MulAut.conj x).toMonoidHom = stabilizer Rg a)
    (hfixed : ⁅Z Rg d,Z Rg c⁆ ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)))
    (hi : (Q Rg c).relIndex (V Rg a) = 2) :
    Z Rg d ⊓ Q Rg c ≤ Q Rg (act Rg x c) := by
  let w := act Rg x⁻¹ d
  have hcancel : act Rg x w = d := by
    dsimp only [w]
    rw [←act_mul,inv_mul_cancel,act_one]
  by_cases hout : Z Rg w ≤ Q Rg c
  · have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hout
    rw [←Z_act,←Q_act,hcancel] at hh
    exact inf_le_left.trans hh
  have hline := plane_radius_two_common_line h e hz hk hb u hR ha hac q hat hdt
    x hxL hgen hfixed hi hout
  have hnear : (cosetGraph Rg).dist d a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hdt)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr
      (adjacent_symm Rg hat))
    have ht : (cosetGraph Rg).dist d a ≤
        (cosetGraph Rg).dist d t + (cosetGraph Rg).dist t a :=
      (cosetGraph_connected Rg).dist_triangle
    simpa only [h₁,h₂] using ht
  have hx : x ∈ stabilizer Rg a := Ltilde_le_stabilizer _ hxL
  have hwa : (cosetGraph Rg).dist w a ≤ 2 := by
    conv_lhs => rhs; rw [←show act Rg x⁻¹ a = a from (stabilizer Rg a).inv_mem hx]
    rw [show w = act Rg x⁻¹ d from rfl,dist_act]
    exact hnear
  have hw : color Rg w = false := (action_preserves_color Rg _ _).trans q.start_color
  have hpair : CriticalPair Rg w c ((sourceGeometry h).exists_critical w hw) := by
    refine ⟨?_,hout⟩
    apply le_antisymm _ (criticalDistance_le Rg w _ hout)
    rw [(sourceGeometry h).distance_constant w hw]
    have ht : (cosetGraph Rg).dist w c ≤
        (cosetGraph Rg).dist w a + (cosetGraph Rg).dist a c :=
      (cosetGraph_connected Rg).dist_triangle
    change _ ≤ sourceDistance h
    omega
  let r := CriticalPath.ofPair (geometry := sourceGeometry h) hw hpair
  obtain ⟨q'⟩ : Nonempty (CriticalPath Rg (sourceGeometry h) d (act Rg x c)) := by
    rw [←hcancel]
    exact ⟨r.act x⟩
  let H := ⁅Z Rg d,Z Rg c⁆
  have hHmap : H.map (MulAut.conj x⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      (((le_centralizer_iff.mp hline.2).trans (Subgroup.centralizer_le_normalizer _))
        ((stabilizer Rg a).inv_mem hx))
  have heq : ⁅Z Rg d,Z Rg c⁆ = ⁅Z Rg d,Z Rg (act Rg x c)⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hline.1
    change H.map (MulAut.conj x⁻¹).toMonoidHom = _ at hh
    rw [hHmap,map_commutator,←Z_act,←Z_act,hcancel] at hh
    exact hh
  exact ((small_critical_kernel_eq_iff_line_eq h e hz hk q q'
    (hsmall _ _ q) (hsmall _ _ q')).mpr heq).le.trans inf_le_right

/-- A paired generating configuration with radius image two cannot have
the opposite-radius commutator controlled by the full starting seed. -/
theorem plane_paired_radius_two_control_false
    (hb : 4 < sourceDistance h) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z d t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hq : q.walk.getVert 1 = t)
    (x : FreeAmalgam Rg) (hxL : x ∈ Ltilde Rg a)
    (hgen : Q Rg t ⊔ (Q Rg t).map (MulAut.conj x).toMonoidHom = stabilizer Rg a)
    (hends : Q Rg t ⊔ Z Rg z ⊔ Z Rg (act Rg x z) = stabilizer Rg a)
    (hfixed : ⁅Z Rg d,Z Rg (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (Q Rg t : Set (FreeAmalgam Rg)))
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d))
    (hi : (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (V Rg a) = 2)
    (hcontrol : ⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),Z Rg z⁆ ≤
      Z Rg a) : False := by
  let c := p.walk.getVert (p.walk.length-2)
  let K := Z Rg d ⊓ Q Rg c
  let Y := K ⊔ Z Rg a
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hac : (cosetGraph Rg).dist a c + 2 ≤ sourceDistance h := by
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have hnear : (cosetGraph Rg).dist d a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hdt)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr
      (adjacent_symm Rg hat))
    have ht : (cosetGraph Rg).dist d a ≤
        (cosetGraph Rg).dist d t + (cosetGraph Rg).dist t a :=
      (cosetGraph_connected Rg).dist_triangle
    simpa only [h₁,h₂] using ht
  have hZV : Z Rg d ≤ V Rg a :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hnear)
  have hKV : K ≤ V Rg a := inf_le_left.trans hZV
  have hYV : Y ≤ V Rg a := sup_le hKV (Z_le_VBall Rg _ 2)
  have hVG : V Rg a ≤ stabilizer Rg a :=
    ((sourceGeometry h).V_le_Q hb2 a p.start_color).trans (fun _ hx => hx.1)
  have hsmall : ∀ v w (_p : CriticalPath Rg (sourceGeometry h) v w),
      (Q Rg w).relIndex (Z Rg v) < 4 :=
    fun _ _ r => plane_long_critical_image_small h e hz hk hb u hR r
  have hKN : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    have hh := plane_small_critical_first_edge_normalizes_kernel h e hz hk u hR q (hsmall _ _ q)
    change Q Rg t ≤ normalizer (Z Rg d ⊓ Q Rg c : Set (FreeAmalgam Rg))
    simpa only [c, hq] using hh
  have hKG : K ≤ stabilizer Rg a := hKV.trans hVG
  have hKmove : ⁅K,Z Rg z⁆ ≤ Z Rg a :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans hcontrol
  have hx : x ∈ stabilizer Rg a := Ltilde_le_stabilizer _ hxL
  have hZmap : (Z Rg a).map (MulAut.conj x⁻¹).toMonoidHom = Z Rg a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized Rg a) ((stabilizer Rg a).inv_mem hx))
  have hVmap : (V Rg a).map (MulAut.conj x⁻¹).toMonoidHom = V Rg a := by
    rw [←V_act,show act Rg x a = a from hx]
  have hKother := plane_radius_two_conjugate_kernel h e hz hk hb2 u hR hsmall
    p.start_color hac q hat hdt x hxL hgen hfixed hi
  have hKmove' : ⁅K,Z Rg (act Rg x z)⁆ ≤ Z Rg a := by
    have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hcontrol
    rw [map_commutator,map_inf _ _ _ (MulAut.conj x⁻¹).injective,hVmap,←Q_act,←Z_act,hZmap] at hm
    exact (commutator_mono (le_inf hKV hKother) le_rfl).trans hm
  have hAG := critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
    (by rw [(sourceGeometry h).distance_constant a p.start_color]
        exact sourceDistance_pos h) p.critical
  have hA'G : Z Rg (act Rg x z) ≤ stabilizer Rg a := by
    have hm := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hAG
    rw [←Z_act,←stabilizer_act,show act Rg x a = a from hx] at hm
    exact hm
  have hYmove (A : Subgroup (FreeAmalgam Rg))
      (hA : A ≤ stabilizer Rg a) (hK : ⁅K,A⁆ ≤ Z Rg a) : ⁅Y,A⁆ ≤ Z Rg a := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg a)
      K (Z Rg a) A (Z Rg a) (Z_normalized Rg a)
      hKG (Z_le_stabilizer Rg a) hK
    exact le_normalizer_iff_commutator_le_left.mp (hA.trans (Z_normalized Rg a))
  have hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hends]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_trans (le_inf hKN _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      exact (show Q Rg t ≤ stabilizer Rg a from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg a)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hAG hKmove).trans le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hA'G hKmove').trans le_sup_right)
  have hreverse := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]
      exact sourceDistance_pos h) z p.end_color p.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hKB : K ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_controlled_actor h e hz hb2 p.start_color
      Y (Z Rg z) hYV hYN hAG (IsElementaryAbelian.isPGroup 2 (Z Rg z))
      hreverse.2 (hYmove _ hAG hKmove))
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hupper : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
    have hh := (relIndex_le_of_le_left hKB (L := U Rg d) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (H := K) (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite)
    have hidx : K.relIndex (Z Rg d) = 2 := by
      dsimp only [K]
      rw [inf_relIndex_left]
      exact (plane_long_critical_indices_two h e hz hk hb u hR q).1
    exact hh.trans_eq hidx
  exact (Nat.not_le_of_gt hstrict) hupper

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
