module
public import Theory.GroupTheory.Recognition.Brauer.RootConjugation
public import Theory.GroupTheory.Recognition.Brauer.ProjectivePlane
public import Theory.GroupTheory.Recognition.Brauer.SwappedIncidentPoints
public import Theory.GroupTheory.Recognition.Brauer.FlagTransitivity

/-!
# Nontrivial elations of Brauer's plane

For each incident point and line in the actual Brauer geometry, a
conjugating element fixes every point on that line and every line through
that point, and moves a line. This proves Brauer, *On finite Desarguesian
planes I*, (3C), article p. 122. In particular the conjugation action is
nonidentity; merely choosing a nonidentity group element would not suffice
because the action need not be faithful. These elations are the geometric
input to the subsequent Desarguesian recognition theorem.

Normalize the flag to `((j1), [j2])`. Choose a nonidentity element of
`M2`, which exists since its order is `q > 1`, and conjugate it by `y`.
The root identities `M1^y = Mstar2` and `Mstar1^y = M2`, including the
actual dual application, show that it centralizes `j`, `Mstar2`, and
`M1`. Here `y^3` centralizes the distinguished involutions and therefore
normalizes their fixed root subgroups. The element also fixes `(j1)`
and `[j2]` as a conjugate of a root-group element stabilizing a base block.
The exact distinguished incidence lists then prove pointwise fixation of
the axis and fixation of the center pencil.

If `[j1]` were fixed as well, its unique underlying involution in `(j1)`
would be fixed. Conjugating back would put the chosen nonidentity element
in `M` intersected with `C(j)`, a contradiction. Finally, conjugate the
same base elation back along the flag normalization, carrying its moved
line with it. No coordinate model or faithfulness assumption is used.
-/

open scoped Pointwise

namespace Theory.GroupTheory.BrauerPlaneSeed

private theorem dual_nondegenerate {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) [Configuration.Nondegenerate S.Point S.Line] :
    Configuration.Nondegenerate S.dual.Point S.dual.Line where
  exists_point := by
    intro p
    obtain ⟨l, hl⟩ := Configuration.Nondegenerate.exists_line (P := S.Point) (L := S.Line) p
    exact ⟨l, fun h => hl ((S.dual_incidence_iff p l).mp h)⟩
  exists_line := by
    intro l
    obtain ⟨p, hp⟩ := Configuration.Nondegenerate.exists_point (P := S.Point) (L := S.Line) l
    exact ⟨p, fun h => hp ((S.dual_incidence_iff p l).mp h)⟩
  eq_or_eq := by
    intro l1 l2 p1 p2 h11 h21 h12 h22
    exact (Configuration.Nondegenerate.eq_or_eq
      ((S.dual_incidence_iff p1 l1).mp h11) ((S.dual_incidence_iff p2 l1).mp h12)
      ((S.dual_incidence_iff p1 l2).mp h21) ((S.dual_incidence_iff p2 l2).mp h22)).symm

private theorem conj_y_cube_M1 {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) :
    S.M1.map (MulAut.conj (S.y⁻¹ * S.y⁻¹ * S.y⁻¹)).toMonoidHom = S.M1 := by
  let c := S.y⁻¹ * S.y⁻¹ * S.y⁻¹
  let f : MulAut G := MulAut.conj S.y⁻¹
  have hj : f S.j = S.j1 := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j
  have hj1 : f S.j1 = S.j2 := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j1
  have hj2 : f S.j2 = S.j := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j2
  have hc (x : G) : c * x * c⁻¹ = f (f (f x)) := by
    dsimp only [c, f, MulAut.conj_apply]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  have hcj : c * S.j * c⁻¹ = S.j := by rw [hc, hj, hj1, hj2]
  have hcj1 : c * S.j1 * c⁻¹ = S.j1 := by rw [hc, hj1, hj2, hj]
  have hcC : c ∈ Subgroup.centralizer {S.j} :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcj)
  have hle : S.M1.map (MulAut.conj c).toMonoidHom ≤ S.M1 := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨(S.centralizer_le_normalizer_M hcC m).mp hm.1, ?_⟩
    have hcomm := (show Commute m S.j1 from Subgroup.mem_centralizer_singleton_iff.mp hm.2).map
      (MulAut.conj c)
    change Commute (c * m * c⁻¹) (c * S.j1 * c⁻¹) at hcomm
    rw [hcj1] at hcomm
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]

private theorem smul_pointOf_j_of_mem_M {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) (a : S.M) :
    (ConjAct.toConjAct (a : G)) • S.pointOf S.j S.j_order = S.pointOf S.j S.j_order := by
  let p0 := S.pointOf S.j S.j_order
  let g := ConjAct.toConjAct (a : G)
  have hp0 : (p0 : Set G) = S.basePoint := by
    let b : S.Point := ⟨S.basePoint, MulAction.mem_orbit_self _⟩
    have heq : p0 = b := (S.pointOf_eq_iff _ _ b).mpr
      (Set.mem_smul_set.mpr ⟨1, S.M.one_mem, mul_one S.j⟩)
    exact congrArg Subtype.val heq
  have hgj : g • S.j ∈ (p0 : Set G) := by
    rw [hp0]
    change g • S.j ∈ S.j • (S.M : Set G)
    rw [← orbit_conjugate_eq_coset S.M S.j S.centralizer_le_normalizer_M S.disjoint_M_centralizer]
    exact ⟨⟨g, Subgroup.mem_map.mpr ⟨a, a.property, rfl⟩⟩, rfl⟩
  exact (S.existsUnique_blocks_of_involution (S.orderOf_mem_point p0 hgj)).1.unique
    (Set.smul_mem_smul_set (S.mem_pointOf S.j S.j_order)) hgj

private theorem base_root_action {G : Type*} [Group G] [Finite G]
    (S : BrauerPlaneSeed G) [Configuration.Nondegenerate S.Point S.Line]
    (h2 : orderOf S.j2 = 2) (a : S.M2) :
    let g := ConjAct.toConjAct (S.y⁻¹ * (a : G) * S.y)
    g • S.j = S.j ∧
    (∀ m : S.Mstar2, g • (m : G) = (m : G)) ∧
    (∀ m : S.M1, g • (m : G) = (m : G)) ∧
    g • S.pointOf S.j1 S.j1_order = S.pointOf S.j1 S.j1_order ∧
    g • S.lineOf S.j2 h2 = S.lineOf S.j2 h2 := by
  let f : MulAut G := MulAut.conj S.y⁻¹
  let y : ConjAct G := ConjAct.toConjAct S.y⁻¹
  let g := ConjAct.toConjAct (S.y⁻¹ * (a : G) * S.y)
  have hj : f S.j = S.j1 := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j
  have hj1 : f S.j1 = S.j2 := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j1
  have hj2 : f S.j2 = S.j := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j2
  have hfy (x : G) : f x = y • x := rfl
  have hfa : f (a : G) = S.y⁻¹ * (a : G) * S.y := by
    change S.y⁻¹ * (a : G) * (S.y⁻¹)⁻¹ = _
    rw [inv_inv]
  have hgj : g • S.j = S.j := by
    have hc := (show Commute (a : G) S.j2 from
      Subgroup.mem_centralizer_singleton_iff.mp a.property.2).map f
    rw [hj2, hfa] at hc
    exact mul_inv_eq_iff_eq_mul.mpr hc.eq
  have hgmstar (m : S.Mstar2) : g • (m : G) = (m : G) := by
    have hm : (m : G) ∈ S.M1.map f.toMonoidHom := S.map_M1_conj_y.symm ▸ m.property
    obtain ⟨b, hb, hbm⟩ := Subgroup.mem_map.mp hm
    change f b = (m : G) at hbm
    have hc := (S.fixed_factors.2.2.1 ⟨a, a.property.1⟩ ⟨b, hb.1⟩)
    have hc' : Commute (f (a : G)) (f b) := (hc.map S.M.subtype).map f
    rw [hfa, hbm] at hc'
    exact mul_inv_eq_iff_eq_mul.mpr hc'.eq
  let : Configuration.Nondegenerate S.dual.Point S.dual.Line := S.dual_nondegenerate
  have ha : (a : G) ∈ S.Mstar1.map f.toMonoidHom := S.dual.map_M1_conj_y.symm ▸ a.property
  obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp ha
  change f c = (a : G) at hca
  have hfc : f (f c) = S.y⁻¹ * (a : G) * S.y := by rw [hca, hfa]
  have hgm (m : S.M1) : g • (m : G) = (m : G) := by
    have hm : (m : G) ∈ S.M1.map (MulAut.conj (S.y⁻¹ * S.y⁻¹ * S.y⁻¹)).toMonoidHom :=
      S.conj_y_cube_M1.symm ▸ m.property
    obtain ⟨b, hb, hbm⟩ := Subgroup.mem_map.mp hm
    have hbm' : f (f (f b)) = (m : G) := by
      rw [← hbm]
      dsimp only [f, MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    have hfb : f b ∈ S.Mstar2 := S.map_M1_conj_y ▸ Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
    have hcomm := (S.fixed_factors.2.2.2.1 ⟨c, hc.1⟩ ⟨f b, hfb.1⟩)
    have hcomm' := (hcomm.map S.Mstar.subtype).map f |>.map f
    change Commute (f (f c)) (f (f (f b))) at hcomm'
    rw [hfc, hbm'] at hcomm'
    exact mul_inv_eq_iff_eq_mul.mpr hcomm'.eq
  have hyp : y • S.pointOf S.j S.j_order = S.pointOf S.j1 S.j1_order := by
    have he := S.pointOf_smul y S.j S.j_order (by simpa only [← hfy, hj] using S.j1_order)
    simpa only [← hfy, hj] using he.symm
  have hgp : g • S.pointOf S.j1 S.j1_order = S.pointOf S.j1 S.j1_order := by
    have hge : g = y * (ConjAct.toConjAct (a : G)) * y⁻¹ := by
      apply ConjAct.ofConjAct.injective
      change S.y⁻¹ * (a : G) * S.y = S.y⁻¹ * (a : G) * (S.y⁻¹)⁻¹
      rw [inv_inv]
    rw [hge, ← hyp, mul_smul, mul_smul, inv_smul_smul,
      S.smul_pointOf_j_of_mem_M ⟨a, a.property.1⟩]
  have hyl : (y * y) • S.lineOf S.j S.j_order = S.lineOf S.j2 h2 := by
    have hyy : (y * y) • S.j = S.j2 := by
      rw [mul_smul]
      change f (f S.j) = S.j2
      rw [hj, hj1]
    have he := S.lineOf_smul (y * y) S.j S.j_order (hyy.symm ▸ h2)
    simpa only [hyy] using he.symm
  have hgl : g • S.lineOf S.j2 h2 = S.lineOf S.j2 h2 := by
    have hge : g = (y * y) * ConjAct.toConjAct c * (y * y)⁻¹ := by
      apply ConjAct.ofConjAct.injective
      change S.y⁻¹ * (a : G) * S.y = _
      rw [← hfc]
      dsimp only [f, y, MulAut.conj_apply]
      change S.y⁻¹ * (S.y⁻¹ * c * (S.y⁻¹)⁻¹) * (S.y⁻¹)⁻¹ =
        (S.y⁻¹ * S.y⁻¹) * c * (S.y⁻¹ * S.y⁻¹)⁻¹
      simp only [mul_inv_rev, inv_inv, mul_assoc]
    have hcl := S.dual.smul_pointOf_j_of_mem_M ⟨c, hc.1⟩
    change ConjAct.toConjAct c • S.dual.pointOf S.j S.j_order = S.dual.pointOf S.j S.j_order at hcl
    have hdual : S.dual.pointOf S.j S.j_order = S.lineOf S.j S.j_order := by
      exact (S.lineOf_eq_iff _ _ _).mpr (S.dual.mem_pointOf _ _) |>.symm
    rw [hdual] at hcl
    rw [hge, ← hyl, mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (fun l : S.Line => (y * y) • l) hcl
  exact ⟨hgj, hgmstar, hgm, hgp, hgl⟩

end Theory.GroupTheory.BrauerPlaneSeed

namespace Theory.GroupTheory.BrauerPlaneData

private theorem pencil_iff {G : Type*} [Group G] [Finite G] (D : BrauerPlaneData G)
    (h2 : orderOf D.j2 = 2) (l : D.Line) :
    D.pointOf D.j1 D.j1_order ∈ l ↔
      l = D.lineOf D.j2 h2 ∨ ∃ a : D.M1, D.j * (a : G) ∈ (l : Set G) := by
  let S := D.toBrauerPlaneSeed
  have hdual_line : S.dual.lineOf S.j1 S.j1_order = S.pointOf S.j1 S.j1_order :=
    (S.dual.lineOf_eq_iff _ _ _).mpr (S.mem_pointOf _ _)
  have hdual_point : S.dual.pointOf S.j2 h2 = S.lineOf S.j2 h2 :=
    (S.dual.pointOf_eq_iff _ _ _).mpr (S.mem_lineOf _ _)
  have hcount : Nat.card {p : S.dual.Point // p ∈ S.dual.lineOf S.dual.j2 h2} =
      S.dual.q + 1 := by
    let p2 := S.dual.lineOf S.dual.j2 h2
    have heq : Nat.card {l : S.dual.Point // l ∈ p2} =
        Nat.card {l : S.Line // (show S.Point from p2) ∈ l} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun l => S.dual_incidence_iff p2 l)
    exact heq.trans ((D.plane_counts.2.2.2.2 p2).trans
      (congrArg (fun q => q + 1) S.dual_q.symm))
  have h := S.dual.incident_iff_swapped_distinguished_point h2 hcount l
  change l ∈ S.dual.lineOf S.j1 S.j1_order ↔
    l = S.dual.pointOf S.j2 h2 ∨ ∃ a : S.M1, S.j * (a : G) ∈ (l : Set G) at h
  rw [hdual_line, hdual_point] at h
  exact (S.dual_incidence_iff (S.pointOf S.j1 S.j1_order) l).symm.trans h

private theorem exists_base_elation {G : Type*} [Group G] [Finite G] (D : BrauerPlaneData G)
    (h2 : orderOf D.j2 = 2) :
    ∃ g : ConjAct G,
      (∀ p : D.Point, p ∈ D.lineOf D.j2 h2 → g • p = p) ∧
      (∀ l : D.Line, D.pointOf D.j1 D.j1_order ∈ l → g • l = l) ∧
      g • D.lineOf D.j1 D.j1_order ≠ D.lineOf D.j1 D.j1_order := by
  classical
  let S := D.toBrauerPlaneSeed
  let := D.projectivePlane
  let : Fintype S.M2 := Fintype.ofFinite _
  have hcard : 1 < Fintype.card S.M2 := by
    rw [← Nat.card_eq_fintype_card, S.fixed_factors.2.2.2.2.2.1]
    exact D.plane_counts.1
  have : Nontrivial S.M2 := Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : S.M2)
  let g := ConjAct.toConjAct (S.y⁻¹ * (a : G) * S.y)
  obtain ⟨hgj, hgstar, hgm, hgp1, hgl2⟩ := S.base_root_action h2 a
  refine ⟨g, ?_, ?_, ?_⟩
  · intro p hp
    rcases (S.incident_iff_distinguished_point h2 (D.plane_counts.2.2.2.1 _) p).mp hp with
      rfl | ⟨m, hm⟩
    · exact hgp1
    · have hfix : g • (S.j * (m : G)) = S.j * (m : G) := by rw [smul_mul', hgj, hgstar]
      exact (S.existsUnique_blocks_of_involution (S.orderOf_mem_point p hm)).1.unique
        (hfix ▸ Set.smul_mem_smul_set hm) hm
  · intro l hl
    rcases (D.pencil_iff h2 l).mp hl with rfl | ⟨m, hm⟩
    · exact hgl2
    · have hfix : g • (S.j * (m : G)) = S.j * (m : G) := by rw [smul_mul', hgj, hgm]
      exact (S.existsUnique_blocks_of_involution (S.orderOf_mem_line l hm)).2.unique
        (hfix ▸ Set.smul_mem_smul_set hm) hm
  · intro hgl1
    have hjp : g • S.j1 ∈ (S.pointOf S.j1 S.j1_order : Set G) := by
      have hm := Set.smul_mem_smul_set (a := g) (S.mem_pointOf S.j1 S.j1_order)
      change g • S.j1 ∈ ((g • S.pointOf S.j1 S.j1_order : S.Point) : Set G) at hm
      rwa [hgp1] at hm
    have hjl : g • S.j1 ∈ (S.lineOf S.j1 S.j1_order : Set G) := by
      have hm := Set.smul_mem_smul_set (a := g) (S.mem_lineOf S.j1 S.j1_order)
      change g • S.j1 ∈ ((g • S.lineOf S.j1 S.j1_order : S.Line) : Set G) at hm
      rwa [hgl1] at hm
    have hgj1 : g • S.j1 = S.j1 := S.point_line_intersection_subsingleton _ _
      ⟨hjp, hjl⟩ ⟨S.mem_pointOf _ _, S.mem_lineOf _ _⟩
    let f : MulAut G := MulAut.conj S.y⁻¹
    have hj1 : f S.j = S.j1 := by simpa only [f, MulAut.conj_apply, inv_inv] using S.y_conj_j
    have hfa : f (a : G) = S.y⁻¹ * (a : G) * S.y := by
      change S.y⁻¹ * (a : G) * (S.y⁻¹)⁻¹ = _
      rw [inv_inv]
    have hcomm : Commute (a : G) S.j := by
      apply f.injective
      rw [map_mul, map_mul, hj1, hfa]
      exact mul_inv_eq_iff_eq_mul.mp hgj1
    have haone : (a : G) = 1 := by
      have hmem : (a : G) ∈ S.M ⊓ Subgroup.centralizer {S.j} :=
        ⟨a.property.1, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq⟩
      simpa only [S.disjoint_M_centralizer.eq_bot, Subgroup.mem_bot] using hmem
    exact ha (Subtype.ext haone)

/-- Brauer I (3C): every incident flag admits an elation which moves a line. -/
public theorem exists_nontrivial_elation {G : Type*} [Group G] [Finite G]
    (D : BrauerPlaneData G) (p : D.Point) (l : D.Line) (hp : p ∈ l) :
    ∃ g : ConjAct G,
      (∀ p' : D.Point, p' ∈ l → g • p' = p') ∧
      (∀ l' : D.Line, p ∈ l' → g • l' = l') ∧
      (∃ l' : D.Line, g • l' ≠ l') := by
  let S := D.toBrauerPlaneSeed
  have h2 : orderOf S.j2 = 2 := by
    have h := (MulAut.conj S.y⁻¹).orderOf_eq S.j1
    change orderOf (S.y⁻¹ * S.j1 * (S.y⁻¹)⁻¹) = orderOf S.j1 at h
    simpa only [inv_inv, S.y_conj_j1, S.j1_order] using h
  obtain ⟨a, hap, hal⟩ := D.exists_smul_flag_eq_base p l hp h2
  obtain ⟨g, hgp, hgl, hmove⟩ := D.exists_base_elation h2
  refine ⟨a⁻¹ * g * a, ?_, ?_, a⁻¹ • S.lineOf S.j1 S.j1_order, ?_⟩
  · intro p' hp'
    have hinc : a • p' ∈ S.lineOf S.j2 h2 := by
      rw [← hal]
      exact (Set.disjoint_smul_set (a := a)).mpr hp'
    rw [mul_smul, mul_smul, hgp _ hinc, inv_smul_smul]
  · intro l' hl'
    have hinc : S.pointOf S.j1 S.j1_order ∈ a • l' := by
      rw [← hap]
      exact (Set.disjoint_smul_set (a := a)).mpr hl'
    rw [mul_smul, mul_smul, hgl _ hinc, inv_smul_smul]
  · intro heq
    apply hmove
    have hh := congrArg (a • ·) heq
    simpa only [mul_smul, smul_inv_smul] using hh

end Theory.GroupTheory.BrauerPlaneData
