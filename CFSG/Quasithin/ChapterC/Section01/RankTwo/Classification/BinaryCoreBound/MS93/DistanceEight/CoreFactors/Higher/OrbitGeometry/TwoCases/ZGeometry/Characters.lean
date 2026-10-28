module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Transport

/-!
# Edge characters and the two MS93 product comparisons

A binary character of the literal Z_a is evaluated on its actual incident
edge subgroup. Distinct index-two edge subgroups generate Z_a, so no nontrivial
character vanishes on both. Two such character coordinates detect the
intersection of the ordered first-layer products. A single character coordinate
lifts equal edge images to the literal product Z_a Z_delta.

`CharacterComparisons` records exact kernels and the still unproved images of
the neighboring layers. It is an output contract for the missing source
comparison with the marked dual sections, not an additional source assumption
or a constructor from abstract quotient dimensions. Its producer belongs to
qt-c01-ms93-z-geometry-character-pairings. The geometric assembly remains in
qt-c01-ms93-higher-z-case-geometry until that producer is complete.

All transported layers use their actual transported path vertices; these
arguments do not require independence from a different forward choice.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.5), printed p.899.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {R : Subgroup M}

/-- Binary characters of the actual local Z-group vanishing on an edge. -/
def edgeCharacters (a t : Vertex R) :
    Subgroup (Z R a →* Multiplicative (ZMod 2)) where
  carrier := {f | ∀ z : Z R a, (z : FreeAmalgam R) ∈ Z R t → f z = 1}
  one_mem' := by intro z _; rfl
  mul_mem' := by intro f h hf hh z hz; simp only [MonoidHom.mul_apply, hf z hz, hh z hz, one_mul]
  inv_mem' := by intro f hf z hz; simp only [MonoidHom.inv_apply, hf z hz, inv_one]

/-- The missing comparisons with the literal edge character lines. Both maps
have exact relative kernels. This is an output contract, not a construction
from the marked sections. -/
structure CharacterComparisons {a : Vertex R} (p : Higher.SourcePath a) where
  first : hatV R a (p.walk.getVert 6) →* (Z R a →* Multiplicative (ZMod 2))
  first_kernel : first.ker = (Z R a).subgroupOf (hatV R a (p.walk.getVert 6))
  first_edge : ∀ g : stabilizer R a,
    ((Z R (act R g (p.walk.getVert 6))).subgroupOf
      (hatV R a (p.walk.getVert 6))).map first =
        edgeCharacters a (act R g (p.walk.getVert 5))
  second : hatW R a (p.walk.getVert 6) (p.walk.getVert 8) →*
    ((Z R a →* Multiplicative (ZMod 2)) × (Z R a →* Multiplicative (ZMod 2)))
  second_kernel : second.ker = (hatV R a (p.walk.getVert 6)).subgroupOf
    (hatW R a (p.walk.getVert 6) (p.walk.getVert 8))
  second_edge : ∀ (g : stabilizer R a)
    (x : hatW R a (p.walk.getVert 6) (p.walk.getVert 8)),
    (x : FreeAmalgam R) ∈ hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) →
    (second x).1 ∈ edgeCharacters a (act R g (p.walk.getVert 5)) ∧
      (second x).2 ∈ edgeCharacters a (act R g (p.walk.getVert 5))

private theorem index_two_coatom {G : Type*} [Group G] {A : Subgroup G}
    (hi : A.index = 2) : IsCoatom A := by
  refine ⟨fun ht => by simp [ht] at hi, fun B hAB => ?_⟩
  have hm := relIndex_mul_index hAB.le
  rw [hi] at hm
  have hp : (A.relIndex B * B.index).Prime := hm ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hB⟩ | ⟨_, hrel⟩
  · exact index_eq_one.mp hB
  · exact (hAB.not_ge (relIndex_eq_one.mp hrel)).elim

private theorem edgeCharacters_disjoint {a t u : Vertex R}
    (ht : Z R t ≤ Z R a) (hu : Z R u ≤ Z R a)
    (hit : (Z R t).relIndex (Z R a) = 2)
    (hiu : (Z R u).relIndex (Z R a) = 2)
    (hne : Z R t ≠ Z R u) : Disjoint (edgeCharacters a t) (edgeCharacters a u) := by
  have hne' : (Z R t).subgroupOf (Z R a) ≠ (Z R u).subgroupOf (Z R a) := by
    intro heq
    apply hne
    have h := congrArg (Subgroup.map (Z R a).subtype) heq
    simpa only [map_subgroupOf_eq_of_le ht, map_subgroupOf_eq_of_le hu] using h
  have hsup := (index_two_coatom hit).sup_eq_top_of_ne (index_two_coatom hiu) hne'
  rw [disjoint_iff_inf_le]
  intro f hf
  change f = 1
  apply MonoidHom.ext
  intro z
  have hker : (⊤ : Subgroup (Z R a)) ≤ f.ker := by
    rw [← hsup]
    exact sup_le (fun x hx => (hf.1 x hx)) (fun x hx => (hf.2 x hx))
  exact hker (mem_top z)

private theorem path_color {a : Vertex R} (p : Higher.SourcePath a)
    {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (RegularPaths.walk_vertex_color p.start_color p.walk (by rw [p.length_eq]; exact hi14)).mpr hi

private theorem first_le_second [Finite M] {a : Vertex R} (p : Higher.SourcePath a) :
    hatV R a (p.walk.getVert 6) ≤ hatW R a (p.walk.getVert 6) (p.walk.getVert 8) := by
  have hseed : hatV R (p.walk.getVert 6) (p.walk.getVert 8) ≤
      hatW R a (p.walk.getVert 6) (p.walk.getVert 8) := by
    intro x hx
    apply le_iSup (fun g : stabilizer R a =>
      rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) g) 1
    exact ⟨x, hx, by simp⟩
  have hZ := (Early.Z_le_hatV (path_color p (i := 6) (by decide) (by decide))
    (p.dist (i := 6) (j := 8) (by decide) (by decide))).trans hseed
  rw [hatV_eq_conjugatesIn]
  apply iSup_le
  intro g
  exact (map_mono hZ).trans
    (mem_normalizer_iff_map_conj_eq.mp
      (hatW_normalized R a _ _ ((stabilizer R a).inv_mem g.property))).le

private theorem conjugate_first_le_second {a : Vertex R} (p : Higher.SourcePath a)
    (g : stabilizer R a) :
    hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) ≤
      hatW R a (p.walk.getVert 6) (p.walk.getVert 8) := by
  rw [← rightConjugate_hatV]
  exact le_iSup (fun k : stabilizer R a =>
    rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k) g

/-- The equal-edge character line gives the literal ordered Z product. -/
theorem equal_Z_span_of_characters {a : Vertex R} (p : Higher.SourcePath a)
    (pairings : CharacterComparisons p) (g : stabilizer R a)
    (heq : Z R (p.walk.getVert 5) = Z R (act R g (p.walk.getVert 5))) :
    (Z R (p.walk.getVert 6) : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) *
        (Z R (act R g (p.walk.getVert 6)) : Set (FreeAmalgam R)) := by
  intro x hx
  let x₀ : hatV R a (p.walk.getVert 6) := ⟨x, Z_le_localZSpan R _ _ hx⟩
  have hχ : pairings.first x₀ ∈ edgeCharacters a (p.walk.getVert 5) := by
    have h := pairings.first_edge 1
    simp only [OneMemClass.coe_one, act_one] at h
    rw [← h]
    exact ⟨x₀, hx, rfl⟩
  have hAnn : edgeCharacters a (p.walk.getVert 5) =
      edgeCharacters a (act R g (p.walk.getVert 5)) := by
    unfold edgeCharacters
    simp only [heq]
  rw [hAnn, ← pairings.first_edge g] at hχ
  obtain ⟨y, hy, hxy⟩ := hχ
  have hk : x₀ * y⁻¹ ∈ pairings.first.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
  rw [pairings.first_kernel] at hk
  exact ⟨x * (y : FreeAmalgam R)⁻¹, hk, y, hy, inv_mul_cancel_right _ _⟩

/-- Distinct index-two edge groups separate the two second-layer character
coordinates, so the ordered products intersect exactly in the first layer. -/
theorem unequal_Z_intersection_of_characters [Finite M]
    {geometry : Geometry R} (earlier : Earlier R geometry)
    {a : Vertex R} (p : Higher.SourcePath a) (pairings : CharacterComparisons p)
    (g : stabilizer R a)
    (hne : Z R (p.walk.getVert 5) ≠ Z R (act R g (p.walk.getVert 5))) :
    ((hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (hatV R (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R))) ∩
    ((hatV R (act R g (p.walk.getVert 6)) (act R g (p.walk.getVert 8)) : Set (FreeAmalgam R)) *
      (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R))) =
    (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) := by
  have ha : color R a = false := p.center_eq ▸ path_color p (i := 4) (by decide) (by decide)
  have ht : Adjacent R a (p.walk.getVert 5) := by
    have h := (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i := 4)
      (by rw [p.length_eq]; decide))
    simpa only [p.center_eq] using h
  have hu : Adjacent R a (act R g (p.walk.getVert 5)) := by
    simpa only [show act R g a = a from g.property] using (adjacent_act_iff R g _ _).mpr ht
  have hdis := edgeCharacters_disjoint
    (Escape.EdgeTransfer.edge_Z_le a _ ha ht) (Escape.EdgeTransfer.edge_Z_le a _ ha hu)
    (earlier.edge_Z_index a _ ha ht) (earlier.edge_Z_index a _ ha hu) hne
  have hA := first_le_second p
  have hB := conjugate_first_le_second p (1 : stabilizer R a)
  simp only [OneMemClass.coe_one, act_one] at hB
  have hC := conjugate_first_le_second p g
  apply Set.Subset.antisymm
  · rintro x ⟨⟨v, hv, b, hb, hvb⟩, ⟨c, hc, w, hw, hcw⟩⟩
    let v₀ := (⟨v, hA hv⟩ : hatW R a (p.walk.getVert 6) (p.walk.getVert 8))
    let b₀ := (⟨b, hB hb⟩ : hatW R a (p.walk.getVert 6) (p.walk.getVert 8))
    let c₀ := (⟨c, hC hc⟩ : hatW R a (p.walk.getVert 6) (p.walk.getVert 8))
    let w₀ := (⟨w, hA hw⟩ : hatW R a (p.walk.getVert 6) (p.walk.getVert 8))
    have hvker : pairings.second v₀ = 1 := MonoidHom.mem_ker.mp (pairings.second_kernel.symm ▸ hv)
    have hwker : pairings.second w₀ = 1 := MonoidHom.mem_ker.mp (pairings.second_kernel.symm ▸ hw)
    have hbχ := pairings.second_edge 1 b₀ (by simpa only [OneMemClass.coe_one, act_one, b₀, SetLike.mem_coe] using hb)
    simp only [OneMemClass.coe_one, act_one] at hbχ
    have hcχ := pairings.second_edge g c₀ hc
    have hbc : pairings.second b₀ = pairings.second c₀ := by
      have h : v₀ * b₀ = c₀ * w₀ := Subtype.ext (hvb.trans hcw.symm)
      have hh := congrArg pairings.second h
      simpa only [map_mul, hvker, hwker, one_mul, mul_one] using hh
    have hbone : pairings.second b₀ = 1 := by
      apply Prod.ext
      · exact hdis.le_bot ⟨hbχ.1, hbc ▸ hcχ.1⟩
      · exact hdis.le_bot ⟨hbχ.2, hbc ▸ hcχ.2⟩
    have hbker : b₀ ∈ pairings.second.ker := MonoidHom.mem_ker.mpr hbone
    rw [pairings.second_kernel] at hbker
    exact hvb ▸ (hatV R a (p.walk.getVert 6)).mul_mem hv hbker
  · intro x hx
    exact ⟨⟨x, hx, 1, one_mem _, mul_one x⟩, ⟨1, one_mem _, x, hx, one_mul x⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry
