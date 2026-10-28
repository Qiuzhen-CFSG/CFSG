module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Statements
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.LocalControl
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic

/-!
# Definite-plane normalization before the outside-overgroup argument

Two-perfect subgroups have trivial permutation action on the pair of definite
planes. The natural action therefore shows that YS normalizes both planes and
both choices of Y₊. The module and its planes lie in S and hence in every I in
H₊. These facts use only the constructions, not the conclusions of 15.3.11.

The shift-kernel proof is the early-boundary form of the argument in
`RankTwo/Containment/FactorGeometry/PlaneActors/Geometry.lean`.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the plane
decomposition on pp.1121–1122 and 15.3.10–11 on pp.1123–1124.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem perfect_normalizes_planes {M V X : Subgroup G}
    (a : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    (hX : IsPPerfect 2 X) (i : OrthogonalPlaneIndex) :
    X ≤ normalizer (a.plane i : Set G) := by
  let f : X →* OrthogonalPlaneIndex :=
    RegularWreathProduct.rightHom.comp (a.actor.comp (inclusion hXM))
  have hp : IsPGroup 2 OrthogonalPlaneIndex := IsPGroup.of_card (n := 1) (by
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card])
  have he := hX f.ker inferInstance
    ((hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm)
  intro x hx
  have hf : f ⟨x, hx⟩ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [he]
    trivial
  have ht : (⟨x, hXM hx⟩ : M) ∈ (normalizer (a.plane i : Set G)).subgroupOf M := by
    rw [a.plane_normalizer_eq_comap, OrthogonalGeometry.setwise_plane_eq_ker]
    exact hf
  exact ht

/-- Both definite planes are normalized by the actual source residual. -/
theorem y_normalizes_plane (d : CharacteristicTwo.LocalData G) (i : OrthogonalPlaneIndex) :
    d.Y ≤ normalizer (d.action.plane i : Set G) :=
  perfect_normalizes_planes d.action
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
    (residualY_isPPerfect d.M d.Mc) i

omit [Finite G] in
/-- The kernel of the coordinate permutation preserves either plane. -/
theorem s_normalizes_plane (d : CharacteristicTwo.LocalData G) (i : OrthogonalPlaneIndex) :
    d.S ≤ normalizer (d.action.plane i : Set G) := by
  intro s hs
  have hsm : s ∈ d.M := d.sylow_le hs.1
  have hn : (⟨s, hsm⟩ : d.M) ∈
      (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M := hs.2
  have he : (normalizer (d.action.plane 1 : Set G)).subgroupOf d.M =
      (normalizer (d.action.plane i : Set G)).subgroupOf d.M := by
    rw [d.action.plane_normalizer_eq_comap, d.action.plane_normalizer_eq_comap,
      OrthogonalGeometry.setwise_plane_eq_ker, OrthogonalGeometry.setwise_plane_eq_ker]
  rw [he] at hn
  exact hn

theorem ys_normalizes_plane (d : CharacteristicTwo.LocalData G) (i : OrthogonalPlaneIndex) :
    d.Y ⊔ d.S ≤ normalizer (d.action.plane i : Set G) :=
  sup_le (y_normalizes_plane d i) (s_normalizes_plane d i)

/-- The original residual is normal relative to M. -/
theorem m_normalizes_y (d : CharacteristicTwo.LocalData G) :
    d.M ≤ normalizer (d.Y : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)).mp
      (residualY_normal d.M d.Mc)

/-- YS normalizes the selected subgroup, including the residual-centralizer choice. -/
theorem ys_normalizes_yplus (d : CharacteristicTwo.LocalData G) :
    d.Y ⊔ d.S ≤ normalizer (d.Yplus : Set G) := by
  have hnY : d.Y ⊔ d.S ≤ normalizer (d.Y : Set G) :=
    (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc)
      (inf_le_left.trans d.sylow_le)).trans (m_normalizes_y d)
  rcases d.choice with h | ⟨_, h⟩
  · rwa [h]
  · rw [h]
    exact ((le_inf hnY ((ys_normalizes_plane d 1).trans
      (normalizer_le_normalizer_centralizer d.V₁))).trans
        inf_normalizer_le_normalizer_inf).trans (normalizer_le_normalizer_residual _)

/-- The coordinate module is already contained in the plane stabilizer. -/
theorem v_le_s (d : CharacteristicTwo.LocalData G) : d.V ≤ d.S :=
  d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1

theorem v_le_outside (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus) : d.V ≤ I :=
  (v_le_s d).trans (le_sup_right.trans hI.1.2)

theorem plane_le_outside (d : CharacteristicTwo.LocalData G) (I : Subgroup G)
    (hI : I ∈ d.Hplus) (i : OrthogonalPlaneIndex) : d.action.plane i ≤ I :=
  (d.action.plane_le i).trans (v_le_outside d I hI)

omit [Finite G] in
theorem v_ne_bot (d : CharacteristicTwo.LocalData G) : d.V ≠ ⊥ := by
  intro h
  have hc := d.action.card_vector
  change Nat.card d.V = 16 at hc
  rw [h] at hc
  norm_num at hc

omit [Finite G] in
theorem plane_ne_bot (d : CharacteristicTwo.LocalData G) (i : OrthogonalPlaneIndex) :
    d.action.plane i ≠ ⊥ := by
  intro h
  have hc := d.action.card_plane i
  rw [h] at hc
  norm_num at hc

/-- Both ambient plane normalizers are controlled in the second choice.
The Y₊ normalizer additionally needs its nontrivial two-core. -/
theorem second_choice_plane_normalizers (d : CharacteristicTwo.LocalData G)
    (h : SecondChoice d) :
    normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M := by
  have hp (i : OrthogonalPlaneIndex) : IsPGroup 2 (d.action.plane i) := by
    let _ := d.action.elementary_of_le (d.action.plane_le i)
    exact IsElementaryAbelian.isPGroup 2 _
  exact ⟨normalizer_le_of_unique_maximalTwoLocal h.1.2.2
      (hp _) (plane_ne_bot d _) (ys_normalizes_plane d _),
    normalizer_le_of_unique_maximalTwoLocal h.1.2.2
      (hp _) (plane_ne_bot d _) (ys_normalizes_plane d _)⟩

/-- Uniqueness of YS prevents an outside overgroup from containing all of Y. -/
theorem y_not_le_outside_of_second_choice (d : CharacteristicTwo.LocalData G)
    (I : Subgroup G) (hI : I ∈ d.Hplus) (h : SecondChoice d) : ¬ d.Y ≤ I := by
  intro hY
  have hcore : pCore 2 I ≠ ⊥ := by
    intro he
    apply hI.1.1
    change (pCore 2 I).map I.subtype = ⊥
    rw [he, Subgroup.map_bot]
  obtain ⟨N, hN, hIN⟩ :=
    Theory.GroupTheory.exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot I hcore
  exact hI.2 (h.1.2.2 N hN
    ((sup_le hY (le_sup_right.trans hI.1.2)).trans hIN) ▸ hIN)

end CFSG.Quasithin.Chapter15.Section03.OutsideStructure.LocalBranches
end
