module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.ActorData
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Stellmacher.TwoResidualIdentification

/-!
# Definite-plane geometry for the residual actors

Compatibility with the literal wreath action identifies the stabilizer of
one coordinate plane with the kernel of the permutation part. Consequently
it stabilizes both planes, and every two-perfect subgroup of M stabilizes
them. The planes are nontrivial, disjoint, and generate the original module.

For the source Y = O²(⟨O₂(M ∩ Mc)^M⟩), either choice of Y₊ in 15.3.10 is
two-perfect, contained in Y, and invariant under S = N_T(V₁). These facts
use the actual residual definitions and relative normality inside M.
No choice of a complementary actor or quotient splitting is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the plane
construction on printed pp.1121–1122, 15.3.7 and 15.3.10 on pp.1122–1123,
and the uses in 15.3.39–40 on pp.1137–1138.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
variable {G : Type*} [Group G]

private theorem coordinate_smul_mem_of_shift_one
    (a : OrthogonalActor) (ha : a.right = 1)
    (i : OrthogonalPlaneIndex) (v : OrthogonalVector)
    (hv : v ∈ orthogonalCoordinatePlane i) :
    letI := orthogonalAction
    a • v ∈ orthogonalCoordinatePlane i := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  intro j hj
  change a.left j • v (a.right⁻¹ * j) = 1
  rw [ha, inv_one, one_mul, hv j hj, smul_one]

private theorem plane_mem_iff (M V : Subgroup G)
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ d.plane i ↔ d.coordinates v ∈ orthogonalCoordinatePlane i := by
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = v := Subtype.ext he
    exact h ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem conjugate_mem_plane_of_shift_one {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (m : M)
    (hm : (d.actor m).right = 1) (i : OrthogonalPlaneIndex)
    {v : G} (hv : v ∈ d.plane i) :
    (m : G) * v * (m : G)⁻¹ ∈ d.plane i := by
  let v₀ : V := ⟨v, d.plane_le i hv⟩
  let w : V := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v₀
  change (w : G) ∈ d.plane i
  rw [plane_mem_iff]
  change d.coordinates (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v₀) ∈ _
  rw [d.compatible]
  exact coordinate_smul_mem_of_shift_one (d.actor m) hm i (d.coordinates v₀)
    ((plane_mem_iff M V d i v₀).mp hv)

/-- Distinct supported coordinate planes intersect trivially. -/
theorem natural_planes_disjoint {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    Disjoint (d.plane i) (d.plane j) := by
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro v hv
  let v₀ : V := ⟨v, d.plane_le i hv.1⟩
  have hi := (plane_mem_iff M V d i v₀).mp hv.1
  have hj := (plane_mem_iff M V d j v₀).mp hv.2
  have he : d.coordinates v₀ = 1 := by
    funext k
    by_cases hk : k = i
    · exact hj k (hk ▸ hij)
    · exact hi k hk
  have hv1 : v₀ = 1 := d.coordinates.injective (he.trans d.coordinates.map_one.symm)
  exact congrArg Subtype.val hv1

/-- The two supported planes generate the original module. -/
theorem natural_planes_sup {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) {i j : OrthogonalPlaneIndex} (hij : i ≠ j) :
    d.plane i ⊔ d.plane j = V := by
  apply le_antisymm (sup_le (d.plane_le i) (d.plane_le j))
  intro v hv
  let v₀ : V := ⟨v, hv⟩
  let a : OrthogonalVector := fun k => if k = i then d.coordinates v₀ k else 1
  let b : OrthogonalVector := fun k => if k = j then d.coordinates v₀ k else 1
  have ha : a ∈ orthogonalCoordinatePlane i := fun k hk => if_neg hk
  have hb : b ∈ orthogonalCoordinatePlane j := fun k hk => if_neg hk
  have hab : a * b = d.coordinates v₀ := by
    funext k
    have hcover : ∀ (i j k : OrthogonalPlaneIndex), i ≠ j → k = i ∨ k = j := by
      decide +kernel
    have hk : k = i ∨ k = j := hcover i j k hij
    rcases hk with rfl | rfl
    · simp [a, b, hij]
    · simp [a, b, hij.symm]
  have hai : ((d.coordinates.symm a : V) : G) ∈ d.plane i :=
    (plane_mem_iff M V d i (d.coordinates.symm a)).mpr (by simpa using ha)
  have hbj : ((d.coordinates.symm b : V) : G) ∈ d.plane j :=
    (plane_mem_iff M V d j (d.coordinates.symm b)).mpr (by simpa using hb)
  have hvab : ((d.coordinates.symm a : V) : G) * ((d.coordinates.symm b : V) : G) = v := by
    change ((d.coordinates.symm a * d.coordinates.symm b : V) : G) = v
    rw [← map_mul, hab, MulEquiv.symm_apply_apply]
  exact hvab ▸ (d.plane i ⊔ d.plane j).mul_mem (mem_sup_left hai) (mem_sup_right hbj)

/-- Stabilizing either coordinate plane forces the permutation part of the
actual orthogonal actor to be trivial. -/
theorem plane_actor_shift_eq_one {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (m : M) (i : OrthogonalPlaneIndex)
    (hm : (m : G) ∈ normalizer (d.plane i : Set G)) :
    (d.actor m).right = 1 := by
  classical
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  let a := d.actor m
  obtain ⟨u, hu⟩ := exists_ne (1 : OrthogonalPlaneVector)
  let v : OrthogonalVector := fun j => if j = i then u else 1
  have hv : v ∈ orthogonalCoordinatePlane i := by
    intro j hj
    exact if_neg hj
  let v₀ := d.coordinates.symm v
  have hv₀ : (v₀ : G) ∈ d.plane i :=
    (plane_mem_iff M V d i v₀).mpr (by simpa [v₀] using hv)
  have hw := (mem_normalizer_iff.mp hm (v₀ : G)).mp hv₀
  let w := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v₀
  have hw' : d.coordinates w ∈ orthogonalCoordinatePlane i :=
    (plane_mem_iff M V d i w).mp hw
  have hact : a • v ∈ orthogonalCoordinatePlane i := by
    simpa only [w, d.compatible, v₀, MulEquiv.apply_symm_apply] using hw'
  by_contra hne
  have hj : a.right * i ≠ i := by
    intro he
    apply hne
    exact mul_right_cancel (he.trans (one_mul i).symm)
  have hval := hact (a.right * i) hj
  change a.left (a.right * i) • v (a.right⁻¹ * (a.right * i)) = 1 at hval
  rw [inv_mul_cancel_left, show v i = u from if_pos rfl] at hval
  exact hu ((MulAction.injective (a.left (a.right * i)))
    (hval.trans (smul_one _).symm))

/-- A subgroup stabilizing one definite plane stabilizes the other as well. -/
theorem normalizes_all_planes_of_normalizes_plane {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    (i : OrthogonalPlaneIndex) (hXi : X ≤ normalizer (d.plane i : Set G))
    (j : OrthogonalPlaneIndex) : X ≤ normalizer (d.plane j : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx v hv
  exact conjugate_mem_plane_of_shift_one d ⟨x, hXM hx⟩
    (plane_actor_shift_eq_one d ⟨x, hXM hx⟩ i (hXi hx)) j hv

/-- Two-perfect subgroups cannot permute the two definite planes. -/
theorem perfect_normalizes_planes {M V X : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hXM : X ≤ M)
    (hX : IsPPerfect 2 X) (i : OrthogonalPlaneIndex) :
    X ≤ normalizer (d.plane i : Set G) := by
  let f : X →* OrthogonalPlaneIndex :=
    RegularWreathProduct.rightHom.comp (d.actor.comp (inclusion hXM))
  have hp : IsPGroup 2 OrthogonalPlaneIndex := IsPGroup.of_card (n := 1) (by
    norm_num [OrthogonalPlaneIndex, Nat.card_eq_fintype_card])
  have hk : IsPGroup 2 (X ⧸ f.ker) :=
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have he := hX f.ker inferInstance hk
  apply le_normalizer_iff.mpr
  intro x hx v hv
  have hf : f ⟨x, hx⟩ = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [he]
    trivial
  exact conjugate_mem_plane_of_shift_one d ⟨x, hXM hx⟩ hf i hv

/-- The coordinate planes are nontrivial, independently of actor selection. -/
theorem natural_plane_ne_bot {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (i : OrthogonalPlaneIndex) : d.plane i ≠ ⊥ := by
  intro h
  have hc := d.card_plane i
  rw [h] at hc
  norm_num at hc

/-- Both definite planes are invariant under the source S = N_T(V₁). -/
theorem planeStabilizer_normalizes_planes {M V : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (i j : OrthogonalPlaneIndex) :
    planeStabilizer T (d.plane i) ≤ normalizer (d.plane j : Set G) :=
  normalizes_all_planes_of_normalizes_plane d (inf_le_left.trans hTM) i inf_le_right j

/-- Either choice in Hypothesis 15.3.10 is contained in the original Y. -/
theorem yplus_le_residualY_of_choice {M Mc S V₁ Yplus : Subgroup G}
    (h : Hypothesis15310 M (residualY M Mc) S V₁ Yplus) :
    Yplus ≤ residualY M Mc := by
  rcases h with h | ⟨_, h⟩
  · exact h.le
  · rw [h]
    exact (map_subtype_le _).trans inf_le_left

/-- Two-perfectness follows from the source residual constructions in both cases. -/
theorem yplus_perfect_of_choice [Finite G] {M Mc S V₁ Yplus : Subgroup G}
    (h : Hypothesis15310 M (residualY M Mc) S V₁ Yplus) :
    IsPPerfect 2 Yplus := by
  rcases h with h | ⟨_, h⟩
  · rw [h]
    exact residualY_isPPerfect M Mc
  · change Yplus = centralizingFactor (residualY M Mc) V₁ at h
    rw [h]
    exact centralizingFactor_isPPerfect _ _

/-- S-invariance of Y₊ is a consequence of the source definitions. -/
theorem planeStabilizer_normalizes_yplus [Finite G] {M Mc V Yplus : Subgroup G}
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex)
    (h : Hypothesis15310 M (residualY M Mc) (planeStabilizer T (d.plane i))
      (d.plane i) Yplus) :
    planeStabilizer T (d.plane i) ≤ normalizer (Yplus : Set G) := by
  have hMY : M ≤ normalizer (residualY M Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).mp (residualY_normal M Mc)
  have hSY := (show planeStabilizer T (d.plane i) ≤ M from inf_le_left.trans hTM).trans hMY
  rcases h with h | ⟨_, h⟩
  · rwa [h]
  · change Yplus = centralizingFactor (residualY M Mc) (d.plane i) at h
    rw [h]
    exact normalizes_centralizingFactor hSY inf_le_right

/-- In CaseTwo, taking the full residual centralizer of V₁ returns Y₊
itself. The right actor must instead be selected from the rank-two quotient. -/
theorem caseTwo_full_plane_centralizer [Finite G] {M Y S V₁ Yplus : Subgroup G}
    (hcase : CaseTwo M Y S V₁ Yplus) :
    centralizingFactor Yplus V₁ = Yplus := by
  have hC : Yplus ≤ centralizer (V₁ : Set G) := by
    rw [hcase.2]
    exact (map_subtype_le _).trans inf_le_right
  rw [centralizingFactor, inf_eq_left.mpr hC, hcase.2]
  rw [Stellmacher.twoResidualAmbient,
    Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual',
    twoResidualAmbient_has_top_twoResidual, ← MonoidHom.range_eq_map,
    range_subtype]

end CFSG.Quasithin.Chapter15.Section03.RankTwo
