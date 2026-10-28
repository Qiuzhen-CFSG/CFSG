module
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Block23
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Linear
public import Theory.SpecificGroups.Janko4.Model.TwoRank.Finite.Coverage
import Mathlib.Tactic.FinCases

/-!
# Connecting the finite vertices to the actual Sylow subgroup

The existing 16 × 8 × 8 bijection supplies exhaustive coverage. Square-one
permutations lie in the checked list of 192 vertices. Commutativity and fixedness
are transported pointwise, retaining the original eleven rows and direct action.
No normality or additional subgroup coverage hypothesis is used.
-/
set_option Elab.async false
@[expose] public section
namespace Janko4.TwoRank.Finite
open LocalStructure.SylowCore LocalStructure.SylowCore.FiniteBoundCertificate
open LocalStructure.SylowCore.FiniteBoundCertificate.NormalWeights
open Cardinality.QuotientCount.Image
open Simplicity.Max1Fusion.QuotientInvolutions

private theorem allBlocks (k : Fin 24) : BlockValid k := by
  fin_cases k
  · exact blockValid00
  · exact blockValid01
  · exact blockValid02
  · exact blockValid03
  · exact blockValid04
  · exact blockValid05
  · exact blockValid06
  · exact blockValid07
  · exact blockValid08
  · exact blockValid09
  · exact blockValid10
  · exact blockValid11
  · exact blockValid12
  · exact blockValid13
  · exact blockValid14
  · exact blockValid15
  · exact blockValid16
  · exact blockValid17
  · exact blockValid18
  · exact blockValid19
  · exact blockValid20
  · exact blockValid21
  · exact blockValid22
  · exact blockValid23

private theorem block_split (v : Fin 192) : ∃ k o, blockVertex k o = v := by
  refine ⟨⟨v.val / 8, by omega⟩, ⟨v.val % 8, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp only [blockVertex]
  omega

theorem code_vertex (v : Fin 192) : code (vertex v) = v := by
  obtain ⟨k, o, rfl⟩ := block_split v
  exact (allBlocks k).codes o

theorem vertex_injective : Function.Injective vertex := by
  intro v w h
  simpa only [code_vertex] using congrArg code h

theorem point_spec (v : Fin 192) (p : Fin 24) : point v p = perm (vertex v) p := by
  obtain ⟨k, o, rfl⟩ := block_split v
  exact (allBlocks k).points o p

theorem row_spec (v : Fin 192) : row v = rows (vertex v) := by
  obtain ⟨k, o, rfl⟩ := block_split v
  exact (allBlocks k).rows o

private theorem compatible_spec (v w : Fin 192)
    (h : ∀ p : Fin 3,
      point v (point w (p.castLE (by decide))) = point w (point v (p.castLE (by decide)))) :
    compatible v w = true := by
  obtain ⟨k, o, rfl⟩ := block_split v
  obtain ⟨j, q, rfl⟩ := block_split w
  exact (allBlocks k).compatible o j q h

private theorem low_spec (v : Fin 192) (b : Fin 64) :
    low v b.val = maskImage (row v) b.val ^^^ b.val := by
  obtain ⟨k, o, rfl⟩ := block_split v
  exact (allBlocks k).low o b

private theorem high_spec (v : Fin 192) (a : Fin 32) :
    high v a.val = maskImage (row v) (a.val * 64) ^^^ (a.val * 64) := by
  obtain ⟨k, o, rfl⟩ := block_split v
  exact (allBlocks k).high o a

private theorem fixed_spec (v : Fin 192) (m : Fin 2048)
    (h : maskImage (row v) m.val = m.val) : fixed v m = true := by
  let a : Fin 32 := ⟨m.val / 64, by omega⟩
  let b : Fin 64 := ⟨m.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : a.val * 64 + b.val = m.val := by dsimp [a, b]; omega
  have hd := displacement_eq (row v) a b (by simpa only [he] using h)
  change (high v a.val == low v b.val) = true
  rw [high_spec v a, low_spec v b]
  exact beq_iff_eq.mpr hd

private theorem map_square_point {G X : Type*} [Group G]
    (f : G →* Equiv.Perm X) (g : G) (h : g ^ 2 = 1) (p : X) :
    f g (f g p) = p := by
  have he := congrArg (fun x => f x p) h
  simpa only [map_pow, pow_two, map_mul, Equiv.Perm.mul_apply, map_one, Equiv.Perm.one_apply] using he

/-- Every square-one element of the literal candidate occurs among the vertices. -/
theorem native_coverage (g : sylowCandidate) (h : g ^ 2 = 1) :
    ∃ v : Fin 192, element (vertex v) = g := by
  obtain ⟨i, hi⟩ := element_bijective.surjective g
  have hc : vertex (code i) = i := by
    apply square_coverage
    intro p
    have he := map_square_point permHom g h (p.castLE (by decide))
    rw [← hi, permHom_element] at he
    exact he
  exact ⟨code i, (congrArg element hc).trans hi⟩

/-- Elementary commutativity gives the relation used by the branching checker. -/
theorem native_compatible (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B]
    (v w : Fin 192) (hv : element (vertex v) ∈ B) (hw : element (vertex w) ∈ B) :
    compatible v w = true := by
  apply compatible_spec
  intro p
  simp only [point_spec]
  exact commute_point B _ _ hv hw _

/-- The direct `starMask` fixedness implies the checked half-mask relation. -/
theorem native_fixed (B : Subgroup sylowCandidate) (v : Fin 192)
    (hv : element (vertex v) ∈ B) (m : FixedMasks B) : fixed v m.val = true := by
  apply fixed_spec
  rw [row_spec]
  exact m.property ⟨element (vertex v), hv⟩

end Janko4.TwoRank.Finite
