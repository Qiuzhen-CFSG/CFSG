module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.CommonNeighbors
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Actors.Source
public import Theory.SpecificGroups.MinusExtraspecial.FivePointLifts

/-!
# The SL₂(3) common-neighbor square in the arbitrary source group

The already constructed A₅ complement in C_G(z) acts faithfully on the
minus-extraspecial core. Mark its action by the five singular central cosets.
For X = (012), conjugate X by a lift of point 0. The cubics U = (123) and
V = (124) are common neighbors. Conjugating U by a lift of point 3 and V
by a lift of point 4 completes a square. Cubic actors fix both lifts of
fixed points; interchanging lifts retains the central factor, which fixes
the complement vertices. Order-four commutators distinguish the opposite
vertices and identify the source pair as SL₂(3).

The four-neighbor count exhausts this square. Source suborbit transitivity
and the existing A₅ branch then prove connectivity for every nonedge.
All vertices and conjugations occur in the original source group, through
its actual core and complement embeddings; no target-model calculation or
local-comparison assumption is used.

Source: Aschbacher, *Sporadic Groups* (1994), 47.8, p.265. This discharges
the common-neighbor premise of source square contraction and recognition;
pentagon contraction and compatible local maps remain separate obligations.
-/

open Subgroup MulAction
open MinusExtraspecial.FivePointLifts
open MinusExtraspecial.FixedFourCalculation.Outside (fivePointAction)
open alternatingGroup.FiveLocalGeometry.CubicEdges
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.CommonNeighbors
variable {G : Type*} [Group G] [Finite G]

private structure Coordinates (D : Seed G) where
  f : alternatingGroup (Fin 5) →* G
  f_inj : Function.Injective f
  f_le : f.range ≤ involutionCentralizer D.z
  c : MinusExtraspecial.Model →* G
  c_inj : Function.Injective c
  φ : alternatingGroup (Fin 5) →* MulAut MinusExtraspecial.Model
  action : ∀ a q, c (φ a q) = f a * c q * (f a)⁻¹
  points : ∀ a, fivePointAction (φ a) = (a : Equiv.Perm (Fin 5))

private theorem nonempty_coordinates [IsSimpleGroup G] (D : Seed G) : Nonempty (Coordinates D) := by
  obtain ⟨S, hfive, _⟩ := InvolutionGeometry.Applications.source_prime_local D
  let E : PrimeNormalizers.ThreeLocal.EarlierConclusions D :=
    ⟨InvolutionGeometry.card_eq D, S, hfive⟩
  obtain ⟨f, hf⟩ := E.exists_alternating_embedding
  let e := D.localType.core_equiv.some
  let φ : alternatingGroup (Fin 5) →* MulAut MinusExtraspecial.Model :=
    (MulAut.congr e).toMonoidHom.comp
      ((MulAut.conjNormal : involutionCentralizer D.z →* MulAut (localCore D.z)).comp f)
  have hφ : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hfix (q : localCore D.z) : MulAut.conjNormal (f a) q = q := by
      apply e.injective
      have h := DFunLike.congr_fun ha (e q)
      simpa only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply, MulAut.one_apply] using h
    have hc : f a ∈ centralizer (localCore D.z : Set (involutionCentralizer D.z)) := by
      intro q hq
      have h := congrArg Subtype.val (hfix ⟨q, hq⟩)
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    have hq := Theory.GroupTheory.centralizer_generalizedFitting_le
      (involutionCentralizer D.z) hc
    have hbot := (PrimeNormalizers.ThreeLocal.alternating_complement D f hf).disjoint
    have he : f a = 1 := (disjoint_iff.mp hbot).le ⟨⟨a, rfl⟩, hq⟩
    exact hf (he.trans f.map_one.symm)
  obtain ⟨m, hm⟩ := exists_marking φ hφ
  let f' := (involutionCentralizer D.z).subtype.comp (f.comp m.symm.toMonoidHom)
  let c := (involutionCentralizer D.z).subtype.comp
    ((localCore D.z).subtype.comp e.symm.toMonoidHom)
  refine ⟨⟨f', (involutionCentralizer D.z).subtype_injective.comp (hf.comp m.symm.injective),
    ?_, c, (involutionCentralizer D.z).subtype_injective.comp
      ((localCore D.z).subtype_injective.comp e.symm.injective),
    φ.comp m.symm.toMonoidHom, ?_, ?_⟩⟩
  · rintro _ ⟨a, rfl⟩
    exact (f (m.symm a)).property
  · intro a q
    change (((e.symm (e (MulAut.conjNormal (f (m.symm a)) (e.symm q)))) :
      localCore D.z) : G) = _
    rw [e.symm_apply_apply]
    rfl
  · intro a
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, m.apply_symm_apply] using
      hm (m.symm a)

namespace Coordinates
variable {D : Seed G} (T : Coordinates D)
private def vertex (j : Fin 10) : D.Vertex :=
  ⟨zpowers (T.f (cycle j)), D.mem_vertex_of_le_centralizer _
    (by rw [Nat.card_zpowers, orderOf_injective T.f T.f_inj, cycle_order])
    (zpowers_le.mpr (T.f_le ⟨cycle j, rfl⟩))⟩

private def r (i : Fin 5) : G := T.c (lift i)

private theorem r_inv (i : Fin 5) : (T.r i)⁻¹ = T.r i := by
  apply inv_eq_of_mul_eq_one_left
  change T.c (lift i) * T.c (lift i) = 1
  rw [← map_mul, ← pow_two, lift_sq, map_one]

private theorem fixed (i : Fin 5) (j : Fin 10) (hij : (cycle j : Equiv.Perm (Fin 5)) i = i) :
    T.r i • T.vertex j = T.vertex j := by
  have hφ : T.φ (cycle j) ^ 3 = 1 := by
    rw [← map_pow, ← cycle_order j, pow_orderOf_eq_one, map_one]
  have h := T.action (cycle j) (lift i)
  rw [cubic_fixed _ hφ i (by rw [T.points]; exact hij)] at h
  have hc : Commute (T.f (cycle j)) (T.r i) :=
    mul_inv_eq_iff_eq_mul.mp h.symm
  apply Subtype.ext
  rw [D.smul_val]
  change (zpowers (T.f (cycle j))).map (MulAut.conj (T.r i)).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  change zpowers (T.r i * T.f (cycle j) * (T.r i)⁻¹) = _
  rw [hc.symm.eq, mul_inv_cancel_right]
  rfl

private theorem central_fixes (j : Fin 10) :
    T.c (MinusExtraspecial.quaternion MinusExtraspecial.z) • T.vertex j = T.vertex j := by
  have h := T.action (cycle j) (MinusExtraspecial.quaternion MinusExtraspecial.z)
  rw [central_fixed] at h
  have hc : Commute (T.f (cycle j)) (T.c (MinusExtraspecial.quaternion MinusExtraspecial.z)) :=
    mul_inv_eq_iff_eq_mul.mp h.symm
  apply Subtype.ext
  rw [D.smul_val]
  change (zpowers (T.f (cycle j))).map (MulAut.conj _).toMonoidHom = _
  rw [MonoidHom.map_zpowers]
  change zpowers (_ * T.f (cycle j) * _) = _
  rw [hc.symm.eq, mul_inv_cancel_right]
  rfl

private theorem action_commutes (i j : Fin 5) (V : D.Vertex)
    (hz : T.c (MinusExtraspecial.quaternion MinusExtraspecial.z) • V = V) :
    T.r i • (T.r j • V) = T.r j • (T.r i • V) := by
  rcases lift_swap i j with h | h
  · have he := congrArg T.c h
    simp only [map_mul] at he
    rw [← mul_smul, ← mul_smul, show T.r i * T.r j = T.r j * T.r i from he]
  · have he := congrArg T.c h
    simp only [map_mul] at he
    rw [← mul_smul, show T.r i * T.r j =
      T.r j * T.r i * T.c (MinusExtraspecial.quaternion MinusExtraspecial.z) from he,
      mul_smul, hz, mul_smul]

private theorem four_in_join (i : Fin 5) (j : Fin 10)
    (hij : (cycle j : Equiv.Perm (Fin 5)) i ≠ i) :
    ∃ w ∈ (T.vertex j).val ⊔ (T.r i • T.vertex j).val, orderOf w = 4 := by
  let x := T.f (cycle j)
  let w := x * (T.r i * x * (T.r i)⁻¹)⁻¹
  have he : T.c (T.φ (cycle j) (lift i) * (lift i)⁻¹) = w := by
    rw [map_mul, map_inv, T.action]
    dsimp [w, x, r]
    group
  refine ⟨w, ?_, ?_⟩
  · apply mul_mem
    · exact (show (T.vertex j).val ≤ (T.vertex j).val ⊔
        (T.r i • T.vertex j).val from le_sup_left) (mem_zpowers x)
    · apply inv_mem
      apply (show (T.r i • T.vertex j).val ≤ (T.vertex j).val ⊔
        (T.r i • T.vertex j).val from le_sup_right)
      rw [D.smul_val]
      exact mem_map_of_mem (MulAut.conj (T.r i)).toMonoidHom (mem_zpowers x)
  · rw [← he, orderOf_injective T.c T.c_inj]
    exact moved_product_order _ i (by rw [T.points]; exact hij)

private theorem sl2_pair [IsSimpleGroup G] (i : Fin 5) (j : Fin 10)
    (hij : (cycle j : Equiv.Perm (Fin 5)) i ≠ i) :
    sl2Join D (T.vertex j) (T.r i • T.vertex j) := by
  obtain ⟨w, hw, ho⟩ := T.four_in_join i j hij
  have hn (n : ℕ) (e : ↥((T.vertex j).val ⊔ (T.r i • T.vertex j).val) ≃*
      alternatingGroup (Fin n))
      (h : ∀ a : alternatingGroup (Fin n), a ^ 4 = 1 → a ^ 2 = 1) : False := by
    let a := e ⟨w, hw⟩
    have ha : orderOf a = 4 := (e.orderOf_eq _).trans ((orderOf_coe _).symm.trans ho)
    have h4 : a ^ 4 = 1 := ha ▸ pow_orderOf_eq_one a
    have hd := orderOf_dvd_of_pow_eq_one (h a h4)
    rw [ha] at hd
    norm_num at hd
  rcases (InvolutionGeometry.Applications.fourSuborbits D).joins
    (T.vertex j) (T.r i • T.vertex j) with he | ha | hs | hf
  · have hd := ((T.vertex j).val ⊔ (T.r i • T.vertex j).val).orderOf_dvd_natCard hw
    rw [← he, sup_idem, D.vertex_card, ho] at hd
    norm_num at hd
  · exact (hn 4 ha.2.some (by decide +kernel)).elim
  · exact hs
  · exact (hn 5 hf.some (by decide +kernel)).elim

private theorem vertex_edges (i : Fin 3) :
    D.graph.Adj (T.vertex (![0,0,6] i)) (T.vertex (![6,7,7] i)) := by
  have ht : ∀ i : Fin 3, ∃ g : alternatingGroup (Fin 5),
      (g * cycle 0 * g⁻¹ = cycle (![0,0,6] i) ∨
        g * cycle 0 * g⁻¹ = (cycle (![0,0,6] i))⁻¹) ∧
      (g * cycle 1 * g⁻¹ = cycle (![6,7,7] i) ∨
        g * cycle 1 * g⁻¹ = (cycle (![6,7,7] i))⁻¹) := by decide +kernel
  obtain ⟨g, hg, hg'⟩ := ht i
  have he : (C 0 ⊔ C 1).map (MulAut.conj g).toMonoidHom =
      C (![0,0,6] i) ⊔ C (![6,7,7] i) := by
    rw [Subgroup.map_sup, map_C_of_cycle hg, map_C_of_cycle hg']
  let eJ : ↥(C (![0,0,6] i) ⊔ C (![6,7,7] i)) ≃* alternatingGroup (Fin 4) :=
    (MulEquiv.subgroupCongr he.symm).trans
      (((C 0 ⊔ C 1).equivMapOfInjective _ (MulAut.conj g).injective).symm.trans modelEquiv)
  have hf : (C (![0,0,6] i) ⊔ C (![6,7,7] i)).map T.f =
      (T.vertex (![0,0,6] i)).val ⊔ (T.vertex (![6,7,7] i)).val := by
    simp only [Subgroup.map_sup, C, MonoidHom.map_zpowers, vertex]
  apply (D.graph_adj_iff _ _).mpr
  exact ⟨(MulEquiv.subgroupCongr hf.symm).trans
    (((C (![0,0,6] i) ⊔ C (![6,7,7] i)).equivMapOfInjective T.f T.f_inj).symm.trans eJ)⟩

include T in
private theorem square [IsSimpleGroup G] :
    ∃ A B : D.Vertex, sl2Join D A B ∧ ∃ R : Fin 4 → D.Vertex,
      Function.Injective R ∧
      (∀ i, D.graph.Adj A (R i) ∧ D.graph.Adj B (R i)) ∧
      (∀ i, D.graph.Adj (R i) (R (i + 1))) := by
  let A := T.vertex 0
  let B := T.r 0 • A
  let U := T.vertex 6
  let V := T.vertex 7
  have haU : D.graph.Adj A U := T.vertex_edges 0
  have haV : D.graph.Adj A V := T.vertex_edges 1
  have hUV : D.graph.Adj U V := T.vertex_edges 2
  have h0U : T.r 0 • U = U := T.fixed 0 6 (by decide +kernel)
  have h0V : T.r 0 • V = V := T.fixed 0 7 (by decide +kernel)
  have h3A : T.r 3 • A = A := T.fixed 3 0 (by decide +kernel)
  have h4A : T.r 4 • A = A := T.fixed 4 0 (by decide +kernel)
  have h3V : T.r 3 • V = V := T.fixed 3 7 (by decide +kernel)
  have h4U : T.r 4 • U = U := T.fixed 4 6 (by decide +kernel)
  have h3B : T.r 3 • B = B := by
    dsimp [B]
    rw [T.action_commutes 3 0 A (T.central_fixes 0), h3A]
  have h4B : T.r 4 • B = B := by
    dsimp [B]
    rw [T.action_commutes 4 0 A (T.central_fixes 0), h4A]
  have hbU : D.graph.Adj B U := by simpa only [h0U] using D.preserves (T.r 0) haU
  have hbV : D.graph.Adj B V := by simpa only [h0V] using D.preserves (T.r 0) haV
  let R : Fin 4 → D.Vertex := ![U, V, T.r 3 • U, T.r 4 • V]
  have hadj (i : Fin 4) : D.graph.Adj A (R i) ∧ D.graph.Adj B (R i) := by
    fin_cases i
    · exact ⟨haU, hbU⟩
    · exact ⟨haV, hbV⟩
    · change D.graph.Adj A (T.r 3 • U) ∧ D.graph.Adj B (T.r 3 • U)
      exact ⟨by simpa only [h3A] using D.preserves (T.r 3) haU,
        by simpa only [h3B] using D.preserves (T.r 3) hbU⟩
    · change D.graph.Adj A (T.r 4 • V) ∧ D.graph.Adj B (T.r 4 • V)
      exact ⟨by simpa only [h4A] using D.preserves (T.r 4) haV,
        by simpa only [h4B] using D.preserves (T.r 4) hbV⟩
  have hedges (i : Fin 4) : D.graph.Adj (R i) (R (i + 1)) := by
    fin_cases i
    · exact hUV
    · change D.graph.Adj V (T.r 3 • U)
      simpa only [h3V] using D.preserves (T.r 3) hUV.symm
    · have h := D.preserves (T.r 3) (D.preserves (T.r 4) hUV)
      rw [h4U, T.action_commutes 3 4 V (T.central_fixes 7), h3V] at h
      exact h
    · change D.graph.Adj (T.r 4 • V) U
      simpa only [h4U] using D.preserves (T.r 4) hUV.symm
  have h02 : R 0 ≠ R 2 := by
    have h := card_join_of_sl2Join D (T.sl2_pair 3 6 (by decide +kernel))
    intro he
    change U = T.r 3 • U at he
    rw [← he, sup_idem, D.vertex_card] at h
    omega
  have h13 : R 1 ≠ R 3 := by
    have h := card_join_of_sl2Join D (T.sl2_pair 4 7 (by decide +kernel))
    intro he
    change V = T.r 4 • V at he
    rw [← he, sup_idem, D.vertex_card] at h
    omega
  have hinj : Function.Injective R := by
    have h01 := (hedges 0).ne
    have h12 := (hedges 1).ne
    have h23 := (hedges 2).ne
    have h30 := (hedges 3).ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨A, B, T.sl2_pair 0 0 (by decide +kernel), R, hinj, hadj, hedges⟩

end Coordinates
private theorem exists_base_square [IsSimpleGroup G] (D : Seed G) :
    ∃ Y : D.Vertex, sl2Join D D.base Y ∧ ∃ R : Fin 4 → D.Vertex,
      Function.Injective R ∧
      (∀ i, D.graph.Adj D.base (R i) ∧ D.graph.Adj Y (R i)) ∧
      (∀ i, D.graph.Adj (R i) (R (i + 1))) := by
  obtain ⟨T⟩ := nonempty_coordinates D
  obtain ⟨A, B, hAB, R, hinj, hadj, hedges⟩ := T.square
  obtain ⟨g, rfl⟩ := D.transitive A
  refine ⟨g⁻¹ • B, ?_, fun i => g⁻¹ • R i, ?_, ?_, ?_⟩
  · simpa only [inv_smul_smul] using
      (sl2Join_smul_iff D g⁻¹ (g • D.base) B).mpr hAB
  · intro i j hij
    apply hinj
    simpa only [smul_inv_smul] using congrArg (fun V : D.Vertex => g • V) hij
  · intro i
    exact ⟨by simpa only [inv_smul_smul] using D.preserves g⁻¹ (hadj i).1,
      D.preserves g⁻¹ (hadj i).2⟩
  · intro i
    exact D.preserves g⁻¹ (hedges i)

/-- Every distinct nonadjacent source pair has a connected common-neighbor
 graph. The SL₂(3) square is constructed in the actual involution centralizer;
 the four-neighbor count exhausts it, and source suborbit transitivity and
 the proved A₅ branch give the assertion for all pairs (47.7–47.8). -/
public theorem nonedge_connected [IsSimpleGroup G] (D : Seed G)
    (A B : D.Vertex) (hne : A ≠ B) (hn : ¬ D.graph.Adj A B) :
    (D.graph.commonNeighborGraph A B).Preconnected := by
  obtain ⟨Y, hY, R, hinj, hadj, hedges⟩ := exists_base_square D
  have hc := card_join_of_sl2Join D hY
  have hneY : Y ≠ D.base := by
    intro he
    rw [he, sup_idem, D.vertex_card] at hc
    omega
  have hnY : ¬ D.graph.Adj D.base Y := by
    intro ha
    have hc' := card_join_of_adj D ha
    omega
  have hcard : Nat.card {U : D.Vertex // D.graph.Adj D.base U ∧ D.graph.Adj Y U} = 4 := by
    change Nat.card ({U | D.graph.Adj D.base U ∧ D.graph.Adj Y U} : Set D.Vertex) = 4
    rw [Nat.card_coe_set_eq]
    exact EdgeConfigurations.Distances.common_neighbors_card D Y hneY hnY
  let f (i : Fin 4) : {U : D.Vertex // D.graph.Adj D.base U ∧ D.graph.Adj Y U} :=
    ⟨R i, hadj i⟩
  have hf : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨fun i j h =>
      hinj (congrArg Subtype.val h), by rw [Nat.card_fin, hcard]⟩).2
  have edge (i : Fin 4) : (D.graph.commonNeighborGraph D.base Y).Adj (f i) (f (i + 1)) :=
    hedges i
  have reach (i : Fin 4) : (D.graph.commonNeighborGraph D.base Y).Reachable (f 0) (f i) := by
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · exact (edge 0).reachable
    · exact (edge 0).reachable.trans (edge 1).reachable
    · exact (edge 3).reachable.symm
  apply connected_of_one_sl2 D Y hY _ A B hne hn
  intro U V
  obtain ⟨i, rfl⟩ := hf U
  obtain ⟨j, rfl⟩ := hf V
  exact (reach i).symm.trans (reach j)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.CommonNeighbors
