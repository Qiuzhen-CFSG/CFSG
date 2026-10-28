module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.AlternatingExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.FullAction.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes

/-!
# The rank-one definite-plane reduction

The selected residual is the literal `Y₊ = O²(C_Y(V₁))`, with
`Y = O²(⟨O₂(M ∩ Mc)^M⟩)`. The cubic coordinate calculation in
`FullAction.Coordinates` gives `[V,Y₊] = [V₂,Y₊] = V₂` for the genuine
natural action. Thus the theta identity of 15.3.11(6) also makes `M ∩ I`
normalize V₂. The coordinate planes have order four, are elementary
abelian, and lie in `S = N_T(V₁)`.

The Sylow image in the coordinate-permutation group supplies an actual
`t ∈ T − S` interchanging the planes. Characteristic two in M puts
`O₂(M)` inside `O₂(YT)` and makes the latter self-centralizing in Y.
The equality `O₂(YT) = C_T(V)` gives its containment in S and both
plane containments in that core. Finally the range of the restricted
natural actor has order nine, with kernel exactly `C_Y(V₁ ⊕ V₂)`.
These deductions discharge every geometric premise of
`RankOne.not_alternating_four_of_local_geometry`, which constructs the
forbidden actual A₄-square equivalence.

The remaining explicit inputs are earlier source conclusions: the natural
action from 15.3.2, characteristic two in M from the standing QTKE setup,
the residual image, core equality and quotient clauses of 15.3.7, the
A₄-square exclusion of 15.3.9, and 15.3.11(5),(6),(9). The final theorem
selects the second preliminary alternative itself. No rank-two shadow,
identity `Y = Y₊`, commutator conclusion, product decomposition, or
self-centralization hypothesis on YT is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(b),(d), printed p.1139, using the definite-plane construction
and 15.3.2--11, printed pp.1121--1124. The parent `RankOne.Reduction`
retains assembly of the complete `ReducedConfiguration`.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.PlaneGeometry
open RankTwo
variable {G : Type*} [Group G] [Finite G]

/-- Conjugation carries a plane to the coordinate selected by the actual actor. -/
theorem conjugate_plane {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (m : M) (i : OrthogonalPlaneIndex) :
    (d.plane i).map (MulAut.conj (m : G)).toMonoidHom =
      d.plane ((d.actor m).right * i) := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  apply eq_of_le_of_card_ge
  · rw [d.plane_eq_map i, d.plane_eq_map ((d.actor m).right * i)]
    rintro x ⟨v, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨d.actor m • w, ?_, d.vectorEmbedding_conjugate m w⟩
    intro k hk
    change (d.actor m).left k • w ((d.actor m).right⁻¹ * k) = 1
    rw [hw _ ?_, smul_one]
    intro he
    exact hk (by rw [← he, mul_inv_cancel_left])
  · rw [card_map_of_injective (MulAut.conj (m : G)).injective,
      d.card_plane, d.card_plane]

/-- Surjectivity of a Sylow image supplies an actual element of T outside S. -/
theorem exists_plane_interchanger {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    ∃ t ∈ (T : Subgroup G), t ∉ planeStabilizer T (d.plane i) ∧
      (d.plane i).map (MulAut.conj t).toMonoidHom = d.plane j ∧
      (d.plane j).map (MulAut.conj t).toMonoidHom = d.plane i := by
  have him := OrthogonalGeometry.sylow_right_image (d.sylowImage T hTM)
  have hmem : j * i⁻¹ ∈ (d.image T).map
      (RegularWreathProduct.rightHom : OrthogonalActor →* OrthogonalPlaneIndex) := by
    rw [← d.coe_sylowImage T hTM, him]
    trivial
  obtain ⟨a, ⟨m, hmT, hma⟩, ha⟩ := hmem
  have hr : (d.actor m).right = j * i⁻¹ := by rw [hma]; exact ha
  refine ⟨m, hmT, ?_, ?_, ?_⟩
  · intro hmS
    have he := plane_actor_shift_eq_one d m i hmS.2
    rw [hr, mul_inv_eq_one] at he
    exact hij he.symm
  · rw [conjugate_plane, hr, inv_mul_cancel_right]
  · rw [conjugate_plane, hr]
    have h : ∀ i j : OrthogonalPlaneIndex, j * i⁻¹ * j = i := by decide +kernel
    rw [h]

/-- The source choice gives both commutator identities on the moving plane. -/
theorem second_plane {M Mc V Yplus I : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hchoice : Yplus = Stellmacher.twoResidualAmbient
      (residualY M Mc ⊓ centralizer (d.plane i : Set G)))
    (htheta : theta (M ⊓ I) = Yplus) :
    d.plane j ≤ planeStabilizer T (d.plane i) ∧
      IsElementaryAbelian 2 (d.plane j) ∧ Nat.card (d.plane j) = 4 ∧
      ⁅d.plane j, Yplus⁆ = d.plane j ∧ ⁅V, Yplus⁆ = d.plane j ∧
      M ⊓ I ≤ normalizer (d.plane j : Set G) := by
  have hc := residualY_fullActionCoordinateFacts d h7
  have hA : Yplus = centralizingFactor (residualY M Mc) (d.plane i) := hchoice
  have hcomm : ⁅V, Yplus⁆ = d.plane j := by rw [hA]; exact hc.commutator i j hij
  refine ⟨(d.plane_le j).trans (d.le_planeStabilizer T hTM hVM i),
    d.elementary_of_le (d.plane_le j), d.card_plane j, ?_, hcomm, ?_⟩
  · rw [hA]; exact hc.commutator_self i j hij
  · have hnorm : M ⊓ I ≤ normalizer (Yplus : Set G) := by
      rw [← htheta]
      exact (M ⊓ I).le_normalizer.trans (normalizer_le_normalizer_theta _)
    intro x hx
    rw [← hcomm, mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.normalizes hx.1),
      mem_normalizer_iff_map_conj_eq.mp (hnorm hx)]

/-- Characteristic two in M gives the required self-centralization in YT.
The source equality O₂(YT)=C_T(V) supplies all the plane/core containments. -/
theorem core_geometry {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M) (hYM : Y ≤ M)
    (hM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hcore : (Y ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (i : OrthogonalPlaneIndex) :
    (Y ⊔ (T : Subgroup G)).pCoreIn 2 ≤ planeStabilizer T (d.plane i) ∧
      V ≤ (Y ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      Y ⊓ centralizer ((Y ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
        (Y ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hCT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    rintro x ⟨m, hm, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := M)).le_sylow_of_normal (T.subtype hTM) hm
  have hCQ : M.pCoreIn 2 ≤ (Y ⊔ (T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 M) (hCT.trans le_sup_right)
      ((sup_le hYM hTM).trans (M.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  have hselfM : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2 := by
    rintro x ⟨hxM, hxC⟩
    refine ⟨⟨x, hxM⟩, hM ?_, rfl⟩
    intro a ha
    exact Subtype.ext (hxC a ⟨a, ha, rfl⟩)
  refine ⟨?_, ?_, ?_⟩
  · rw [hcore]
    exact le_inf inf_le_left
      (inf_le_right.trans ((centralizer_le (d.plane_le i)).trans
        (Subgroup.centralizer_le_normalizer _)))
  · rw [hcore]
    refine le_inf (d.le_sylow T hTM hVM) ?_
    let _ := d.elementary
    intro v hv w hw
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : V) ⟨v, hv⟩)
  · exact (inf_le_inf hYM (centralizer_le hCQ)).trans (hselfM.trans hCQ)

/-- Only the genuine quotient and centralizer clauses of 15.3.7 are inputs.
In the elementary-nine case the action image already identifies the kernel. -/
def SourceQuotientAlternatives (Y V : Subgroup G) : Prop :=
  (IsElementaryAbelian 3 (Y ⧸ pCore 2 Y) ∧ Nat.card (Y ⧸ pCore 2 Y) = 9) ∨
  (IsExtraspecial 3 (Y ⧸ pCore 2 Y) ∧ Nat.card (Y ⧸ pCore 2 Y) = 27 ∧
    ((centralizer (V : Set G)).subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) =
      center (Y ⧸ pCore 2 Y))

/-- The action quotient is the range of the actual actor restricted to Y. -/
noncomputable def residualAction {M Mc V : Subgroup G} (d : NaturalOrthogonalAction M V) :=
  (d.actor.comp (inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))).rangeRestrict

/-- The range has order nine and its kernel is exactly the joint-plane centralizer.
The source quotient alternatives therefore supply those of the product theorem. -/
theorem residualAction_geometry {M Mc V : Subgroup G}
    (d : NaturalOrthogonalAction M V)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hquot : SourceQuotientAlternatives (residualY M Mc) V)
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    Nat.card (d.actor.comp (inclusion
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))).range = 9 ∧
    (residualAction (Mc := Mc) d).ker =
      (centralizer (d.plane i ⊔ d.plane j : Subgroup G)).subgroupOf (residualY M Mc) ∧
    RankTwo.ResidualProduct.QuotientAlternatives (residualY M Mc) (residualAction d) := by
  have hk : (residualAction (Mc := Mc) d).ker =
      (centralizer (V : Set G)).subgroupOf (residualY M Mc) := by
    rw [residualAction, MonoidHom.ker_rangeRestrict, natural_restricted_actor_ker]
  refine ⟨?_, ?_, ?_⟩
  · rw [natural_restricted_actor_range, h7]
    exact orthogonal_twoResidual_card
  · rw [natural_planes_sup d hij]
    exact hk
  · rcases hquot with ⟨he, hc⟩ | ⟨he, hc, hz⟩
    · refine Or.inl ⟨he, hc, ?_⟩
      rw [hk, residualY_centralizer_eq_twoCore d h7 hc]
      exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
    · exact Or.inr ⟨he, hc, hk ▸ hz⟩

/-- Clause (d) from the selected residual, the genuine earlier quotient clauses,
and 15.3.9. All plane, core, interchange and action-kernel premises are proved. -/
theorem not_alternating_four {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hquot : SourceQuotientAlternatives (residualY M Mc) V)
    (h9 : ¬ Nonempty (residualY M Mc ≃*
      (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hchoice : Yplus = Stellmacher.twoResidualAmbient
      (residualY M Mc ⊓ centralizer (d.plane i : Set G))) :
    ¬ Nonempty (Yplus ≃* alternatingGroup (Fin 4)) := by
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hMY : M ≤ normalizer (residualY M Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc)
  have hA : Yplus = centralizingFactor (residualY M Mc) (d.plane i) := hchoice
  have hAY : Yplus ≤ residualY M Mc := hA ▸ centralizingFactor_le_left _ _
  have hperfect : IsPPerfect 2 Yplus := hA ▸ centralizingFactor_isPPerfect _ _
  have hSA : planeStabilizer T (d.plane i) ≤ normalizer (Yplus : Set G) := by
    rw [hA]
    exact normalizes_centralizingFactor ((inf_le_left.trans hTM).trans hMY) inf_le_right
  have hAU : Yplus ≤ centralizer (d.plane i : Set G) := hA ▸ centralizingFactor_le _ _
  have hAW : ⁅d.plane j, Yplus⁆ = d.plane j := by
    rw [hA]
    exact (residualY_fullActionCoordinateFacts d h7).commutator_self i j hij
  obtain ⟨hRS, hVR, hself⟩ := core_geometry d T hTM hVM hYM hM hcore i
  obtain ⟨t, ht, _, hti, htj⟩ := exists_plane_interchanger d T hTM hij
  obtain ⟨hD, hk, hq⟩ := residualAction_geometry d h7 hquot hij
  exact RankOne.not_alternating_four_of_local_geometry (residualAction d) hD hk hq
    (residualY_isPPerfect M Mc) hperfect hAY (hTM.trans hMY) hRS hself
    ((d.plane_le i).trans hVR) ((d.plane_le j).trans hVR)
    (d.card_plane i) (d.card_plane j) (natural_planes_disjoint d hij)
    hSA hAU hAW h9 t ht hti htj

/-- The preliminary alternative selects the source residual. This gives all of
(b) and (d), both plane containments in S, and invariance of V₂ under M ∩ I. -/
theorem plane_reduction_of_preliminary_alternative {M Mc V Yplus I : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hVM : V ≤ M)
    (hM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (h7 : d.image (residualY M Mc) =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hquot : SourceQuotientAlternatives (residualY M Mc) V)
    (h9 : ¬ Nonempty (residualY M Mc ≃*
      (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))))
    {i j : OrthogonalPlaneIndex} (hij : i ≠ j)
    (hshadow : SymmetricThreeShadow Yplus (planeStabilizer T (d.plane i)))
    (htheta : theta (M ⊓ I) = Yplus) (hne : Yplus ≠ ⊥)
    (h11 : 3 < (pCore 2 Yplus).index ∨
      ((Chapter4.UniqueMaximalOvergroup
          (residualY M Mc ⊔ planeStabilizer T (d.plane i)) M ∧
        Yplus = Stellmacher.twoResidualAmbient
          (residualY M Mc ⊓ centralizer (d.plane i : Set G))) ∧
        Yplus = threeResidualIn (M ⊓ I))) :
    d.plane i ≤ planeStabilizer T (d.plane i) ∧
    d.plane j ≤ planeStabilizer T (d.plane i) ∧
    IsElementaryAbelian 2 (d.plane j) ∧ Nat.card (d.plane j) = 4 ∧
    ⁅d.plane i, Yplus⁆ = ⊥ ∧ ⁅d.plane j, Yplus⁆ = d.plane j ∧
    ⁅V, Yplus⁆ = d.plane j ∧ M ⊓ I ≤ normalizer (d.plane j : Set G) ∧
    ¬ Nonempty (Yplus ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨⟨_, hchoice⟩, _, _⟩ :=
    rank_one_choice_of_preliminary_alternative hshadow htheta hne h11
  obtain ⟨hVS, hel, hc, hcomm, hwhole, hnorm⟩ :=
    second_plane d T hTM hVM h7 hij hchoice htheta
  exact ⟨(d.plane_le i).trans (d.le_planeStabilizer T hTM hVM i), hVS, hel, hc,
    centralizes_first_plane_of_residual_choice hchoice, hcomm, hwhole, hnorm,
    not_alternating_four d T hTM hVM hM h7 hcore hquot h9 hij hchoice⟩

end CFSG.Quasithin.Chapter15.Section03.RankOne.PlaneGeometry
