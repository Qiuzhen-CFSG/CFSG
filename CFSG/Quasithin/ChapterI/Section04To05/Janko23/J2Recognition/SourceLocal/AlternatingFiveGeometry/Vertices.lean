module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.Frame
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry

/-!
# Vertices and the dihedral marking in the local A₅

Sylow conjugacy identifies the K orbit of X with all order-three subgroups
contained in the actual subgroup K ≃ A₅. Normalizer restriction preserves
the literal ambient intersection and its embedding. An even permutation
inverting a three-cycle gives an element of that intersection which acts
nontrivially on X, supplying `hinverts` in `localDataOfCalculations`.

The pentagon embedding constructs the dihedral subgroup B inside an A₅
pointwise edge fixer. This gives an actual `EdgeFrame`; the identification
of its centralizer K with A₅ remains a separate prime-local input. The
frame applications below retain that explicit input and use `endpoints_le`.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

@[expose] public section

open scoped Pointwise
open Subgroup Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
open alternatingGroup.FiveLocalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- Construct the literal dihedral marking inside the actual pointwise edge fixer. -/
noncomputable def edgeFrameOfAlternatingFixer (D : Seed G) (Y : D.Vertex)
    (hY : D.graph.Adj D.base Y) (e : edgeFixer G D.base Y ≃* alternatingGroup (Fin 5)) :
    EdgeFrame D where
  y := Y
  adjacent := hY
  B := (dihedralEmbedding (edgeFixer G D.base Y) e).range
  B_le := dihedralEmbedding_range_le _ e
  dihedral := ⟨dihedralEmbedding_range_equiv _ e⟩

namespace AlternatingFiveGeometry
variable (D : Seed G) (K : Subgroup G)

/-- Every cubic subgroup of K is conjugate to the chosen X by an element of K. -/
theorem conjugate_of_card_three (e : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K)
    (A : Subgroup G) (hA : Nat.card A = 3) (hAK : A ≤ K) :
    ∃ g : K, D.X.map (MulAut.conj (g : G)).toMonoidHom = A := by
  have hc (P : Subgroup G) (hP : Nat.card P = 3) (hPK : P ≤ K) :
      Nat.card (P.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPK).toEquiv, hP]
  obtain ⟨g, hg⟩ := cubic_conjugate e (D.X.subgroupOf K) (A.subgroupOf K)
    (hc D.X D.card_X hX) (hc A hA hAK)
  refine ⟨g, ?_⟩
  change MulAut.conj g • D.X.subgroupOf K = A.subgroupOf K at hg
  rw [conj_smul_subgroupOf hX g] at hg
  have hm := congrArg (fun P : Subgroup K => P.map K.subtype) hg
  rw [map_subgroupOf_eq_of_le (conj_smul_le_of_le hX g),
    map_subgroupOf_eq_of_le hAK] at hm
  exact hm

/-- The K orbit of X is exactly the ambient cubic subgroups contained in K. -/
theorem subgroup_orbit_iff (e : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K)
    (A : Subgroup G) :
    (∃ g : K, D.X.map (MulAut.conj (g : G)).toMonoidHom = A) ↔
      Nat.card A = 3 ∧ A ≤ K := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨by rw [card_map_of_injective (MulAut.conj (g : G)).injective, D.card_X],
      conj_smul_le_of_le hX g⟩
  · rintro ⟨hc, hle⟩
    exact conjugate_of_card_three D K e hX A hc hle

/-- In particular every cubic subgroup of K is a vertex of the source graph. -/
theorem mem_vertex_of_card_three (e : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K)
    (A : Subgroup G) (hA : Nat.card A = 3) (hAK : A ≤ K) :
    A ∈ MulAction.orbit (ConjAct G) D.X := by
  obtain ⟨g, hg⟩ := conjugate_of_card_three D K e hX A hA hAK
  exact ⟨ConjAct.toConjAct (g : G), hg⟩

/-- Vertex form of the same orbit theorem, with the literal source action. -/
theorem vertex_orbit_iff (e : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K)
    (A : D.Vertex) : (∃ g : K, (g : G) • D.base = A) ↔ A.val ≤ K := by
  constructor
  · rintro ⟨g, rfl⟩
    exact conj_smul_le_of_le hX g
  · intro hA
    obtain ⟨g, hg⟩ := conjugate_of_card_three D K e hX A.val (D.vertex_card A) hA
    exact ⟨g, Subtype.ext hg⟩

/-- The vertex overlap retains the intrinsic normalizer's literal embedding. -/
theorem vertex_overlap (hX : D.X ≤ K) :
    K ⊓ normalizer (D.X : Set G) =
      (normalizer (D.X.subgroupOf K : Set K)).map K.subtype := by
  rw [← subgroupOf_normalizer_eq hX, subgroupOf_map_subtype, inf_comm]

/-- This equivalence transports the intrinsic normalizer, without losing its image. -/
def vertexOverlapEquiv (hX : D.X ≤ K) :
    ↥(K ⊓ normalizer (D.X : Set G)) ≃*
      normalizer (D.X.subgroupOf K : Set K) where
  toFun g := ⟨⟨g, g.property.1⟩, by
    rw [← subgroupOf_normalizer_eq hX]
    exact g.property.2⟩
  invFun g := ⟨g, ⟨g.val.property, by
    change (g : K) ∈ (normalizer (D.X : Set G)).subgroupOf K
    simpa only [subgroupOf_normalizer_eq hX] using g.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem vertexOverlapEquiv_coe (hX : D.X ≤ K)
    (g : ↥(K ⊓ normalizer (D.X : Set G))) :
    (((vertexOverlapEquiv D K hX g : normalizer (D.X.subgroupOf K : Set K)) : K) : G) = g := by
  rfl

/-- An element of the actual vertex overlap moves an element of X. -/
theorem exists_vertex_overlap_moves (e : K ≃* alternatingGroup (Fin 5)) (hX : D.X ≤ K) :
    ∃ t ∈ K ⊓ normalizer (D.X : Set G), ∃ x ∈ D.X, t * x ≠ x * t := by
  have hc : Nat.card (D.X.subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv, D.card_X]
  obtain ⟨t, ht, x, hx, htx⟩ := exists_noncommuting_normalizer e (D.X.subgroupOf K) hc
  have htN : (t : G) ∈ normalizer (D.X : Set G) := by
    change t ∈ (normalizer (D.X : Set G)).subgroupOf K
    simpa only [subgroupOf_normalizer_eq hX] using ht
  exact ⟨t, ⟨t.property, htN⟩, x, hx, fun he => htx (Subtype.ext he)⟩

/-- This discharges `hinverts` in `localDataOfCalculations`. -/
theorem vertex_overlap_not_le_centralizer (e : K ≃* alternatingGroup (Fin 5))
    (hX : D.X ≤ K) :
    ¬ K ⊓ normalizer (D.X : Set G) ≤ centralizer (D.X : Set G) := by
  obtain ⟨t, ht, x, hx, htx⟩ := exists_vertex_overlap_moves D K e hX
  intro h
  exact htx ((h ht) x hx).symm

/-- The pointwise edge overlap is the image of the two intrinsic normalizers. -/
theorem edgeFixer_overlap (Y : D.Vertex) (hX : D.X ≤ K) (hY : Y.val ≤ K) :
    K ⊓ edgeFixer G D.base Y =
      (normalizer (D.X.subgroupOf K : Set K) ⊓
        normalizer (Y.val.subgroupOf K : Set K)).map K.subtype := by
  rw [map_inf _ _ K.subtype K.subtype_injective,
    ← vertex_overlap D K hX, ← subgroupOf_normalizer_eq hY, subgroupOf_map_subtype,
    edgeFixer, D.stabilizer_eq_normalizer, D.stabilizer_eq_normalizer]
  change K ⊓ (normalizer (D.X : Set G) ⊓ normalizer (Y.val : Set G)) = _
  simp only [inf_assoc, inf_left_comm, inf_comm, inf_left_idem]

end AlternatingFiveGeometry

namespace EdgeFrame
variable {D : Seed G} (F : EdgeFrame D)

theorem vertex_orbit_iff (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) (A : D.Vertex) :
    (∃ g : F.K, (g : G) • D.base = A) ↔ A.val ≤ F.K :=
  AlternatingFiveGeometry.vertex_orbit_iff D F.K eK
    (le_sup_left.trans (F.endpoints_le he)) A

/-- Source endpoints give the actual local conjugating element. -/
theorem neighbor_in_local_orbit
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    ∃ g : F.K, (g : G) • D.base = F.y :=
  (F.vertex_orbit_iff he eK F.y).mpr (le_sup_right.trans (F.endpoints_le he))

/-- An actual A₅ identification supplies the required noncentral vertex overlap. -/
theorem vertex_overlap_not_le_centralizer
    (he : Nonempty (edgeFixer G D.base F.y ≃* alternatingGroup (Fin 5)))
    (eK : F.K ≃* alternatingGroup (Fin 5)) :
    ¬ F.K ⊓ normalizer (D.X : Set G) ≤ centralizer (D.X : Set G) :=
  AlternatingFiveGeometry.vertex_overlap_not_le_centralizer D F.K eK
    (le_sup_left.trans (F.endpoints_le he))

end EdgeFrame
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal
