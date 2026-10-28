module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Path
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Moving

/-!
# The local Q decomposition in MS93 (4.5.4)(vi)

The turns at a and a+2 place the second orbit layers based at a-2 and a
in the third orbit layer based at a. Factoring twice with the preceding
(4.5.1)(iv) products then leaves precisely Q_a ∩ Q_(a+2) ∩ Q_(a+4).
This proves the literal setwise product used on printed p.899; it does not
assume the core containment or any marked quotient from (4.5.4).

The two product identities and the two (4.5.3)(i) identities are explicit
earlier-source inputs, owned by qt-c01-ms93-core-factors-early-layers.
The higher-layer assembly owner must discharge them.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.896--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}

private theorem seed_le_span {G : Type*} [Group G] (A P : Subgroup G) :
    A ≤ conjugatesIn A P := by
  intro x hx
  apply (le_iSup (fun g : P => rightConjugate A g) 1)
  exact ⟨x, hx, by simp⟩

private theorem span_le {G : Type*} [Group G] {A P N : Subgroup G}
    (hA : A ≤ N) (hN : P ≤ normalizer N) : conjugatesIn A P ≤ N := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hN (P.inv_mem g.property))).le

/-- The local turn at c places hat V_a inside hat W_c. Only the two
preceding (4.5.3)(i) identities at a and d are used. -/
theorem hatV_le_next_hatW {a c d e : Vertex R}
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a)
    (hVd : hatV R d e = Vcirc R d ⊔ Z R d)
    (hturn : ∃ g ∈ stabilizer R c, act R g d = a) :
    hatV R a c ≤ hatW R c d e := by
  obtain ⟨g, hg, ht⟩ := hturn
  have hmap : rightConjugate (hatV R d e) g = hatV R a c := by
    rw [rightConjugate, hVd, Subgroup.map_sup, ← Vcirc_act, ← Z_act, ht, ← hVa]
  exact hmap ▸ le_iSup (fun k : stabilizer R c => rightConjugate (hatV R d e) k)
    ⟨g, hg⟩

/-- The second layer at a lies in the third layer. The seed Z_d is already
in hat V_d by the actual common-edge generation theorem. -/
theorem hatW_le_hatSix [Finite M] {a c d e : Vertex R}
    (hd : color R d = false) (hde : (cosetGraph R).dist d e = 2) :
    hatW R a c d ≤ hatSix R a c d e := by
  have hZd : Z R d ≤ hatW R c d e :=
    (Early.Z_le_hatV hd hde).trans (seed_le_span _ _)
  have hVc : hatV R c d ≤ hatW R c d e := by
    rw [hatV_eq_conjugatesIn]
    exact span_le hZd (hatW_normalized R c d e)
  exact iSup_mono fun _ => map_mono hVc

/-- Transport the backward second layer with the turn at a. The ambient
third layer is only assumed normal in G_a, as in its definition. -/
theorem previous_hatW_le_hatSix {a b c d e : Vertex R}
    (hVa : hatV R a c ≤ hatW R c d e)
    (hturn : ∃ g ∈ stabilizer R a, act R g c = b) :
    hatW R b a c ≤ hatSix R a c d e := by
  obtain ⟨g, hg, ht⟩ := hturn
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have hA : (hatV R a c).map f = hatV R a c :=
    mem_normalizer_iff_map_conj_eq.mp
      (hatV_normalized R a c ((stabilizer R a).inv_mem hg))
  have hP : (stabilizer R c).map f = stabilizer R b := by
    rw [← stabilizer_act, ht]
  have hn : stabilizer R b ≤ normalizer ((hatW R c d e).map f) := by
    rw [← hP]
    exact (map_mono (hatW_normalized R c d e)).trans (le_normalizer_map f)
  have hseed : hatV R a c ≤ (hatW R c d e).map f := by
    rw [← hA]
    exact map_mono hVa
  have hs : (hatW R c d e).map f ≤ hatSix R a c d e :=
    (map_mono (hatW_seed_le_hatSix a c d e)).trans
      (mem_normalizer_iff_map_conj_eq.mp
        (hatSix_normalized R a c d e ((stabilizer R a).inv_mem hg))).le
  exact (span_le hseed hn).trans hs

private theorem factor_twice {G : Type*} [Group G]
    {Q₀ Q₁ Q₂ P₁ P₂ A B S : Subgroup G}
    (hS : S ≤ Q₀) (hA : A ≤ S) (hB : B ≤ S)
    (hBQ₁ : B ≤ Q₁) (hQ₀P₁ : Q₀ ≤ P₁) (hQ₁P₂ : Q₁ ≤ P₂)
    (h₁ : (A : Set G) * (Q₁ : Set G) = (P₁ : Set G))
    (h₂ : (B : Set G) * (Q₂ : Set G) = (P₂ : Set G)) :
    (Q₀ : Set G) = (S : Set G) * (Q₀ ⊓ Q₁ ⊓ Q₂ : Set G) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxP := hQ₀P₁ hx
    change x ∈ (P₁ : Set G) at hxP
    rw [← h₁] at hxP
    obtain ⟨u, hu, y, hy, rfl⟩ := hxP
    have hyQ₀ : y ∈ Q₀ := by
      simpa only [inv_mul_cancel_left] using Q₀.mul_mem (Q₀.inv_mem (hS (hA hu))) hx
    have hyP := hQ₁P₂ hy
    change y ∈ (P₂ : Set G) at hyP
    rw [← h₂] at hyP
    obtain ⟨v, hv, z, hz, rfl⟩ := hyP
    have hzQ₀ : z ∈ Q₀ := by
      simpa only [inv_mul_cancel_left] using Q₀.mul_mem (Q₀.inv_mem (hS (hB hv))) hyQ₀
    have hzQ₁ : z ∈ Q₁ := by
      simpa only [inv_mul_cancel_left] using Q₁.mul_mem (Q₁.inv_mem (hBQ₁ hv)) hy
    exact ⟨u * v, S.mul_mem (hA hu) (hB hv), z, ⟨⟨hzQ₀, hzQ₁⟩, hz⟩,
      mul_assoc _ _ _⟩
  · rintro _ ⟨s, hs, z, hz, rfl⟩
    exact Q₀.mul_mem (hS hs) hz.1.1

private theorem path_color {a : Vertex R} (p : Higher.SourcePath a)
    {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (RegularPaths.walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi14)).mpr hi

/-- The Q_a decomposition used in (4.5.4)(vi), obtained from the literal
preceding (4.5.1)(iv) products at a-2 and a and (4.5.3)(i) at a and a+4.
The remaining factor is the source triple intersection. -/
theorem SourcePath.Q_product [Finite M] {a : Vertex R} (p : Higher.SourcePath a)
    (earlier : Earlier R geometry)
    (hVa : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a)
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R a (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R))) :
    (Q R a : Set (FreeAmalgam R)) =
      (hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) : Set (FreeAmalgam R)) *
        (Q R a ⊓ Q R (p.walk.getVert 6) ⊓ Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) := by
  have hc := path_color p (i := 6) (by decide) (by decide)
  have hd := path_color p (i := 8) (by decide) (by decide)
  have hca := p.two_step_distances.1
  have hdc := p.two_step_distances.2.1
  have hde : (cosetGraph R).dist (p.walk.getVert 8) (p.walk.getVert 10) = 2 :=
    p.dist (by decide) (by decide)
  have hVaW : hatV R a (p.walk.getVert 6) ≤
      hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) := by
    apply hatV_le_next_hatW hVa hVd
    simpa only [p.center_eq] using p.turns 6 (by decide) (by decide) (by decide)
  have hprev : hatW R (p.walk.getVert 2) a (p.walk.getVert 6) ≤
      hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10) := by
    apply previous_hatW_le_hatSix hVaW
    simpa only [p.center_eq] using p.turns 4 (by decide) (by decide) (by decide)
  have hWQc : hatW R a (p.walk.getVert 6) (p.walk.getVert 8) ≤ Q R (p.walk.getVert 6) :=
    (hatW_le_radius R hca.le hdc.le).trans
      ((Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le (p.walk.getVert 6) a 4 6
        (by rw [SimpleGraph.dist_comm, hca])).trans
        (Escape.Propagation.RadiusFour.VBall_le_Q _ hc 6 (by rw [earlier.distance]; decide)))
  have hQaQt : Q R a ≤ Q R (p.walk.getVert 5) := by
    apply Q_le_adjacent_h R
    · have hn := adjacent_color_ne R ((cosetGraph_adj R _ _).mp
        (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 4) (j := 5) (by decide) (by decide))))
      have ha := path_color p (i := 4) (by decide) (by decide)
      cases ht : color R (p.walk.getVert 5) <;> simp_all
    · apply (cosetGraph_adj R _ _).mp
      apply SimpleGraph.dist_eq_one_iff_adj.mp
      simpa only [p.center_eq] using p.dist (i := 4) (j := 5) (by decide) (by decide)
  have hQcQu : Q R (p.walk.getVert 6) ≤ Q R (p.walk.getVert 7) := by
    apply Q_le_adjacent_h R
    · have hn := adjacent_color_ne R ((cosetGraph_adj R _ _).mp
        (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 6) (j := 7) (by decide) (by decide))))
      cases ht : color R (p.walk.getVert 7) <;> simp_all
    · exact (cosetGraph_adj R _ _).mp
        (SimpleGraph.dist_eq_one_iff_adj.mp (p.dist (i := 6) (j := 7) (by decide) (by decide)))
  exact factor_twice (p.hatSix_le_Q earlier) hprev (hatW_le_hatSix hd hde)
    hWQc hQaQt hQcQu hleft hright

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
