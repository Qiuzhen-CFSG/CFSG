module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.OriginalContext
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.G2
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal.Parabolics.M12
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.CubicRecognition
public import Theory.GroupTheory.CentralInvolutionMarking

/-!
# Forced orientation of the original cubic amalgam

The original H contains a central involution. In every concrete second
parabolic, such an involution would generate the omega-center of the common
Sylow subgroup, but an explicit parabolic actor moves its generator. Thus the
marked source pair is oriented (H,YT). The same original intersection with M
identifies its whole overlap with the prescribed Sylow subgroup.

Source: Aschbacher--Smith, Lemma 14.2.21, printed p.988.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.SourceAssembly ChapterF.GreenBook
variable {G : Type*} [Group G] [Finite G]

private theorem no_central_involution_of_moving
    (T : Sylow 2 G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hc : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z a : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (ha : a ∈ H) (hm : a * z * a⁻¹ ≠ z) :
    ¬ ∃ t : H, t ∈ center H ∧ orderOf t = 2 := by
  rintro ⟨t,ht,ho⟩
  have he := central_involution_marking T H hTH hc t ht ho
  have htC : (t : G) ∈ centralizer (H : Set G) := by
    intro x hx
    exact congrArg H.subtype (mem_center_iff.mp ht ⟨x,hx⟩)
  have hzC : z ∈ centralizer (H : Set G) :=
    (zpowers_le.mpr htC) (he.symm ▸ hz)
  apply hm
  rw [hzC a ha,mul_inv_cancel_right]

private theorem second_g2_no_central_involution :
    ¬ ∃ t : Atlas.G2.BinaryCore.secondParabolic,
      t ∈ center _ ∧ orderOf t = 2 := by
  open Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair in
    apply no_central_involution_of_moving commonSylow secondParabolic commonSylow_le_second
      (by change Nat.card (((omega₁ (center unipotent) (p := 2)).map (center unipotent).subtype).map unipotent.subtype) = 2
          rw [commonSylow_omega_center]; exact card_distinguished)
      z movingActor ?_ movingActor_mem movingActor_moves
    change z ∈ ((omega₁ (center unipotent) (p := 2)).map (center unipotent).subtype).map unipotent.subtype
    rw [commonSylow_omega_center]
    exact mem_zpowers z

private theorem second_g2_derived_no_central_involution :
    ¬ ∃ t : Atlas.G2.BinaryParabolicPair.derivedSecond,
      t ∈ center _ ∧ orderOf t = 2 := by
  open Atlas.G2 Atlas.G2.BinaryCore Atlas.G2.BinaryParabolicPair in
    apply no_central_involution_of_moving derivedSylow derivedSecond derivedSylow_le_second
      (by change Nat.card (((omega₁ (center (derivedSylow : Subgroup DerivedModel)) (p := 2)).map _).map _) = 2
          rw [derivedSylow_omega_center_in_model]; exact card_derivedDistinguished)
      ⟨z,rootA_one_mem_commutator⟩ ⟨movingActor,movingActor_mem_derived⟩ ?_
      movingActor_mem_derivedSecond movingActor_derived_moves
    change (⟨z,rootA_one_mem_commutator⟩ : DerivedModel) ∈
      ((omega₁ (center (derivedSylow : Subgroup DerivedModel)) (p := 2)).map _).map _
    rw [derivedSylow_omega_center_in_model]
    exact mem_zpowers z

private theorem second_m12_no_central_involution :
    ¬ ∃ t : Sporadic.Mathieu.M12SmallPair.secondParabolic,
      t ∈ center _ ∧ orderOf t = 2 := by
  open Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair in
    apply no_central_involution_of_moving commonSylow secondParabolic inf_le_right
      (by change Nat.card (((omega₁ (center commonSylow) (p := 2)).map _).map _) = 2
          rw [commonSylow_omega_center]; exact card_distinguished)
      z movingActor ?_ movingActor_mem movingActor_moves
    change z ∈ ((omega₁ (center commonSylow) (p := 2)).map _).map _
    rw [commonSylow_omega_center]
    exact mem_zpowers z

private theorem second_autM12_no_central_involution :
    ¬ ∃ t : Sporadic.Mathieu.M12ExceptionalExtension.secondParabolic,
      t ∈ center _ ∧ orderOf t = 2 := by
  open Sporadic.Mathieu.M12ExceptionalExtension in
    have hω : omegaOneCenterAmbient overlap = distinguished := by
      exact (map_map _ _ _).trans VerifiedPair.source_Z
    apply no_central_involution_of_moving VerifiedPair.commonSylow secondParabolic inf_le_right
      (by change Nat.card (omegaOneCenterAmbient overlap) = 2
          rw [hω]; exact FirstParabolic.card_distinguished)
      z SecondCoordinates.secondActor (by
        change z ∈ omegaOneCenterAmbient overlap
        rw [hω]
        exact mem_zpowers z)
      SecondCoordinates.secondActor_mem_secondParabolic ?_
    have ha := SecondCoordinates.actor_action_two
    rw [SecondCoordinates.movement_bit_two, SecondCoordinates.movement_bit_one] at ha
    rw [ha]
    intro hv
    have he : SecondCoordinates.movement (QuaternionSwapModel.MarkedCubic.bit 1) =
        SecondCoordinates.movement (QuaternionSwapModel.MarkedCubic.bit 2) := by
      rw [SecondCoordinates.movement_bit_one,SecondCoordinates.movement_bit_two,hv]
    have hh := SecondCoordinates.movement_injective he
    have hb := QuaternionSwapModel.sixteenEmbedding_injective hh
    exact (by decide +kernel : QuaternionSwapModel.basisBit 1 ≠
      QuaternionSwapModel.basisBit 2) hb

private theorem transfer_central_involution {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ∃ z : A, z ∈ center A ∧ orderOf z = 2) :
    ∃ z : B, z ∈ center B ∧ orderOf z = 2 := by
  obtain ⟨z,hz,ho⟩ := h
  exact ⟨e z,(MulEquivClass.apply_mem_center_iff e).mpr hz,(e.orderOf_eq z).trans ho⟩

private theorem context_central_involution (T : Sylow 2 G) (M Mc H : Subgroup G)
    (c : CubicSourceContext T M Mc H) : ∃ z : H, z ∈ center H ∧ orderOf z = 2 := by
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := centralInvolutions T) 2
    (by rw [c.mark_card])
  let j : centralInvolutions T →* H := inclusion ((centralInvolutions_le_sylow T).trans c.sylow_le_H)
  refine ⟨j z,mem_center_iff.mpr (fun h => ?_),?_⟩
  · apply Subtype.ext
    exact ((c.Mc_centralizer ▸ c.H_le_Mc h.property) (z : G) z.property).symm
  · exact (orderOf_injective j (inclusion_injective _) z).trans hz

/-- The central involution fixes the source orientation of the marked pair. -/
theorem CubicSourceContext.not_swapped {T : Sylow 2 G} {M Mc H : Subgroup G}
    (c : CubicSourceContext T M Mc H) (X : Subgroup G) :
    ¬ ExceptionalMarkedAmalgam X H := by
  have hz := context_central_involution T M Mc H c
  intro hh
  rcases hh with h | h | h | h
  · obtain ⟨f⟩ := h
    exact second_g2_derived_no_central_involution (transfer_central_involution f.right hz)
  · obtain ⟨f⟩ := h
    exact second_g2_no_central_involution (transfer_central_involution f.right hz)
  · obtain ⟨f⟩ := h
    exact second_m12_no_central_involution
      (transfer_central_involution (f.trans MathieuTwelve.concreteIso).right hz)
  · obtain ⟨f⟩ := h
    exact second_autM12_no_central_involution (transfer_central_involution
      ((f.trans AutMathieuTwelve.ambientIso.symm).trans AutMathieuTwelve.concreteIso).right hz)

omit [Finite G] in
/-- The entire overlap in the source pair is the prescribed Sylow subgroup. -/
theorem CubicSourceContext.intersection {T : Sylow 2 G} {M Mc H : Subgroup G}
    (c : CubicSourceContext T M Mc H) :
    H ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)) = (T : Subgroup G) := by
  have hTM : (T : Subgroup G) ≤ M := c.H_inf_M ▸ (show H ⊓ M ≤ M from inf_le_right)
  apply le_antisymm
  · exact (inf_le_inf_left H (sup_le (sourceResidual_le _ _) hTM)).trans c.H_inf_M.le
  · exact le_inf c.sylow_le_H le_sup_right

/-- The original cubic recognition has its forced source orientation. -/
theorem source_cubic_oriented_amalgam
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eH : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    ExceptionalMarkedAmalgam H (sourceResidual M Mc ⊔ (T : Subgroup G)) := by
  have c := cubic_source_context hG T hempty hM hu hmany hcard e H hH eH
  exact (source_cubic_marked_amalgam hG T hempty hM hu hmany hcard e H hH eH).resolve_right
    (c.not_swapped _)

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
