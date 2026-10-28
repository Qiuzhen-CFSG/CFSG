module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Transport

/-!
# Transporting the neighboring quotient-action estimate

The radius bounds put both the second-layer seed and its conjugates in Q_a.
A bound for [hat W_c,Q_a] in hat V_a joined with hat V_c therefore bounds
each pair of conjugates. Mapping this same estimate by the literal right
conjugation gives the second bound. Relative normalization turns the joins
into the two setwise products, in exactly the order used on printed p.899.

The neighboring quotient-action estimate remains a source obligation, owned
by qt-c01-ms93-z-geometry-neighbor-action. It is weaker than the final
[hat V_a^(6),Q_a] bound and is not deduced from (4.5.5) here. In particular,
this lemma does not assume a derived bound or drop the conjugated third vertex.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)--(4.5.5), pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {R : Subgroup M}

private theorem path_color {a : Vertex R} (p : Higher.SourcePath a)
    {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (RegularPaths.walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi14)).mpr hi

/-- A bound for the action of Q_a on the neighboring second layer gives both
ordered product bounds after conjugation. The moving layer retains all three
transported vertices. No global Q-commutator or derived bound is used. -/
theorem pair_commutator_products_of_neighbor_bound [Finite M]
    {geometry : Geometry R} (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a)
    (hneighbor : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R a⁆ ≤
      hatV R a (p.walk.getVert 6) ⊔ hatV R (p.walk.getVert 6) (p.walk.getVert 8))
    (g : stabilizer R a) :
    ((⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ⊆
      ((hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
        (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
      ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) : Set (FreeAmalgam R)) *
        (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R))) := by
  let A := hatV R a (p.walk.getVert 6)
  let B := hatV R (p.walk.getVert 6) (p.walk.getVert 8)
  let W := hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)
  let f := (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom
  have hA : A.map f = A := mem_normalizer_iff_map_conj_eq.mp
    (hatV_normalized R a _ ((stabilizer R a).inv_mem g.property))
  have hQ : (Q R a).map f = Q R a := mem_normalizer_iff_map_conj_eq.mp
    (Q_normalized R a ((stabilizer R a).inv_mem g.property))
  have hWQ : W ≤ Q R a := (hatW_seed_le_hatSix a _ _ _).trans (p.hatSix_le_Q earlier)
  have hgWQ : W.map f ≤ Q R a := (map_mono hWQ).trans hQ.le
  have hBQ : B ≤ Q R a :=
    (hatV_le_radius R p.two_step_distances.2.1.le).trans
      (V_le_Q_of_dist_add_two_lt R (path_color p (i := 6) (by decide) (by decide))
        (by rw [p.two_step_distances.1, earlier.distance]; decide))
  have hgBQ : B.map f ≤ Q R a := (map_mono hBQ).trans hQ.le
  have hBN : B ≤ normalizer A :=
    hBQ.trans ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (hatV_normalized R a _))
  have hgBN : B.map f ≤ normalizer A :=
    hgBQ.trans ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (hatV_normalized R a _))
  have hright : ⁅W.map f, Q R a⁆ ≤ A ⊔ B.map f := by
    change ⁅W, Q R a⁆ ≤ A ⊔ B at hneighbor
    have h := map_mono (f := f) hneighbor
    simpa only [map_commutator, hQ, Subgroup.map_sup, hA] using h
  have hb : ⁅W, W.map f⁆ ≤ A ⊔ B :=
    (commutator_mono le_rfl hgWQ).trans hneighbor
  have hc : ⁅W, W.map f⁆ ≤ B.map f ⊔ A := by
    rw [sup_comm, commutator_comm]
    exact (commutator_mono le_rfl hWQ).trans hright
  have hBmap : B.map f =
      hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) :=
    rightConjugate_hatV (R := R) (g : FreeAmalgam R) _ _
  intro x hx
  have hb' : x ∈ (A : Set (FreeAmalgam R)) * (B : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_right_le_normalizer_left A B hBN]
    exact hb hx
  have hc' : x ∈ (B.map f : Set (FreeAmalgam R)) * (A : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_left_le_normalizer_right (B.map f) A hgBN]
    exact hc hx
  rw [hBmap] at hc'
  exact ⟨hb', hc'⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry
