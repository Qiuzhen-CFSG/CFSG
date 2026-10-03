module
public import Stellmacher.SectionEight.EightSixSelectedOrbitDoubleCommutator
public import Stellmacher.SectionFiveToSeven.NeighborCenterNormalizer

/-!
The selected orbit closure has a first commutator that spans the initial center
together with the terminal center line. The commutator lies in the predecessor
and terminal cores, while its second commutator vanishes; the exact core
centralizer therefore places it in the initial center. If it lay in the
terminal line, the selected residual conjugate and edge generation would
force the terminal stabilizer to normalize the neighboring center, contrary
to the critical-path normalizer theorem. This is the step preceding (12) in
Stellmacher's proof of Lemma 8.6.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem eight_six_selected_orbit_commutator_sup_line
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (hlength : ctx.criticalPath.length = 2)
    (hcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 4)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hprev : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a ∧
      previous ≠ ctx.criticalPath.firstStep)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hcore : conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E ≤
      QAt ctx.Γ ctx.criticalPath.a)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a)) :
    ⁅conjugateClosure (ZAt ctx.Γ ctx.criticalPath.a) E,
      VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep = ZAt ctx.Γ ctx.criticalPath.a := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let U := conjugateClosure (ZAt Γ cp.a) E
  let Z := ZAt Γ cp.firstStep
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ GAt Γ cp.firstStep := hAE.trans geom.group_le
  have hUprevNorm : U ≤ Subgroup.normalizer (QAt Γ previous : Set G) :=
    (hcore.trans ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.a previous
      hprev.1 default).2.2).trans (SevenSix.stabilizer_le_normalizer_q Γ previous)
  have hAprev : A ≤ QAt Γ previous := inf_le_left.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) previous)
  have hCprev : ⁅U,A⁆ ≤ QAt Γ previous :=
    (Subgroup.commutator_mono le_rfl hAprev).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hUprevNorm)
  have hUV : U ≤ VAt Γ cp.firstStep := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨e,z,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (stabilizer_le_normalizer_v Γ cp.firstStep (geom.group_le e.property)) z).mp
        ((lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1 z.property)
  have hUR : U ≤ QAt Γ cp.firstStep := hUV.trans
    (SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by exact hlength ▸ by decide) _)
  have hCnext : ⁅U,A⁆ ≤ QAt Γ cp.firstStep :=
    (Subgroup.commutator_mono hUR le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hAP.trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)))
  have hCD : ⁅U,A⁆ ≤ D := hD ▸ le_inf hCprev hCnext
  have hdouble := eight_six_selected_orbit_double_commutator_eq_bot ctx hcenter hquot hlength
    hcard previous D L Q hprev data E A0 actor geom hcore
  have hfull := eight_six_intersection_centralizer_of_rigidity
    ctx.sectionSeven Γ cp hcenter previous D L Q hD data (by
      intro K hK hKS
      have hKZa := eight_six_rigidity_le_initial_center ctx.sectionSeven Γ cp hcenter hquot
        previous D L Q hD hL data K (hK.trans inf_le_left) hKS
      exact eight_six_rigidity_le_first_center_of_le_initial ctx hcenter hlength hcard
        previous D L Q data K hKZa (hK.trans inf_le_right))
  have hfirstCentralizer := eight_six_first_core_part_centralizer_of_intersection_centralizer
    ctx.sectionSeven Γ cp hcenter hquot hcard previous D L Q hD data hfull
  have hpreviousCentralizer := eight_six_predecessor_core_part_centralizer_of_first_core_part
    ctx.sectionSeven Γ cp previous hprev.1 D L Q data hfirstCentralizer
  have hCZa : ⁅U,A⁆ ≤ ZAt Γ cp.a := (le_inf hCD
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hdouble)).trans_eq hpreviousCentralizer
  have hZ := eight_six_first_step_fixed_line_local ctx hcenter hcard
  have hseedU : ZAt Γ cp.a ≤ U := by
    intro z hz
    exact Subgroup.subset_closure ⟨(1:E),⟨z,hz⟩,by simp⟩
  have hUN : E ≤ Subgroup.normalizer (U : Set G) :=
    eight_six_conjugate_closure_normalizer _ _
  have hZN : E ≤ Subgroup.normalizer (Z : Set G) :=
    geom.group_le.trans (stabilizer_le_normalizer_z Γ cp.firstStep)
  have hnot : ¬ ⁅U,A⁆ ≤ Z := by
    intro hCZ
    have hx : geom.x ∈ E := SevenSix.twoResidualIn_le E geom.residual_mem
    have hUx : U.map (MulAut.conj geom.x).toMonoidHom = U :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUN hx)
    have hZx : Z.map (MulAut.conj geom.x).toMonoidHom = Z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZN hx)
    have hconj : ⁅U,A.conjBy geom.x⁆ ≤ Z := by
      have hh := Subgroup.map_mono (f := (MulAut.conj geom.x).toMonoidHom) hCZ
      rw [Subgroup.map_commutator] at hh
      rw [hUx,hZx] at hh
      exact hh
    have hEN : E ≤ Subgroup.normalizer (ZAt Γ cp.a : Set G) := by
      rw [geom.generated]
      apply sup_le
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
          ((Subgroup.commutator_mono hseedU le_rfl).trans (hCZ.trans hZ.2))
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mpr
          ((Subgroup.commutator_mono hseedU le_rfl).trans (hconj.trans hZ.2))
    apply neighbor_center_not_normalized ctx.sectionSeven Γ cp.firstStep cp.a
      ((SevenSix.mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    change GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (ZAt Γ cp.a : Set G)
    rw [← hedge]
    exact sup_le hEN (inf_le_left.trans (stabilizer_le_normalizer_z Γ cp.a))
  have hle : ⁅U,A⁆ ⊔ Z ≤ ZAt Γ cp.a := sup_le hCZa hZ.2
  have hcardZ : Nat.card Z = 2 := hZ.1
  have hmore : 2 < Nat.card (⁅U,A⁆ ⊔ Z : Subgroup G) := by
    have hb := Subgroup.card_le_of_le (show Z ≤ ⁅U,A⁆ ⊔ Z from le_sup_right)
    rw [hcardZ] at hb
    by_contra hn
    have heq : Z = ⁅U,A⁆ ⊔ Z := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
    exact hnot (le_sup_left.trans_eq heq.symm)
  have hdvd : Nat.card (⁅U,A⁆ ⊔ Z : Subgroup G) ∣ 4 := hcard ▸ Subgroup.card_dvd_of_le hle
  have hc : Nat.card (⁅U,A⁆ ⊔ Z : Subgroup G) = 4 := by
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2^2 from hdvd) with ⟨n,hn,heq⟩
    have hn2 : n = 2 := by
      by_contra hne
      have hnsmall : n = 0 ∨ n = 1 := by omega
      rcases hnsmall with hn0 | hn1
      · rw [hn0] at heq
        norm_num only [pow_zero, pow_one] at heq
        omega
      · rw [hn1] at heq
        norm_num only [pow_zero, pow_one] at heq
        omega
    subst n
    exact heq
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc]; exact hcard.le)

end Stellmacher.SectionEight
