module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.TrackMaximal
public import Theory.GroupAction.CubicTree.TrackTranslation
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.NormalizerOrbit

/-!
# Local transitivity from the ends of a regular track segment

The two endpoint actions of a positive even regular segment supply transpositions
on the neighbors of the first vertex. Translate the right endpoint action back
along the track; its fixed neighbor differs from the fixed neighbor of the left
endpoint action. A third neighbor connects the two resulting orbits. If the
segment fixer normalizes the track fixer, all selected actors belong to its
actual normalizer.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (5.1), p.394.
-/

@[expose] public section
open Subgroup SimpleGraph Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem CubicTreeAction.regular_track_segment_normalizer_transitive
    (h : CubicTreeAction F) (t : Track (RankTwo.graph F) G) (m n : ℕ)
    (hlen : n+1=2*m) (hreg : Regular (A := G) (t.arc 0 (n+1)))
    (hN : t.segmentFixer 0 (n+1) ≤ trackNormalizer t) :
    ∀ w, (RankTwo.graph F).Adj (t.vertex 0) w →
      ∃ g ∈ trackNormalizer t, g • t.vertex 0 = t.vertex 0 ∧ g • t.vertex 1 = w := by
  classical
  let q := t.arc 0 (n+1)
  have hab : (RankTwo.graph F).Adj (t.vertex 0) (t.vertex 1) := by
    simpa only [zero_add] using t.adjacent 0
  have had : (RankTwo.graph F).Adj (t.vertex 0) (t.vertex (-1)) := by
    simpa only [show (-1:ℤ)+1=0 from rfl] using (t.adjacent (-1)).symm
  have hbd : t.vertex 1 ≠ t.vertex (-1) := fun he => by have := t.injective he; omega
  have hc : ((RankTwo.graph F).neighborSet (t.vertex 0)).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact h.card_neighbor _
  obtain ⟨z, hz, hznot⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (s := {t.vertex 1, t.vertex (-1)})
    (t := (RankTwo.graph F).neighborSet (t.vertex 0))
    (by rw [Set.ncard_pair hbd, hc]; decide)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hznot
  have hback (w : RankTwo.Vertex F) : Backward q w ↔
      (RankTwo.graph F).Adj (t.vertex 0) w ∧ w ≠ t.vertex 1 := Iff.rfl
  have hfix0 {g : G} (hg : ∀ v ∈ q.vertices, g • v = v) :
      g • t.vertex 0 = t.vertex 0 :=
    (t.mem_segmentFixer.mp ((t.fixes_arc_iff _ _ _).mp hg)) 0 le_rfl (by omega)
  have hmemN {g : G} (hg : ∀ v ∈ q.vertices, g • v = v) : g ∈ trackNormalizer t :=
    hN ((t.fixes_arc_iff _ _ _).mp hg)
  let u := t.translation ^ (m : ℤ)
  have huN : u ∈ trackNormalizer t :=
    zpow_mem (translation_mem_trackNormalizer t) _
  have hu0 : u • t.vertex 0 = t.vertex (n+1) := by
    rw [t.zpow_translate]
    congr 1
    omega
  have hu1 : u • t.vertex 1 = t.vertex (0+(n+1:ℕ)+1) := by
    rw [t.zpow_translate]
    congr 1
    omega
  have hud : u • t.vertex (-1) = t.vertex (0+(n:ℕ)) := by
    rw [t.zpow_translate]
    congr 1
    omega
  have huforward : Forward q (u • t.vertex 1) := by
    rw [hu1]
    exact t.arc_forward _ _
  have hzforward : Forward q (u • z) := by
    rw [Forward, t.arc_endpoint, t.arc_penultimate]
    refine ⟨?_, ?_⟩
    · have he := trackGraphAction.map_adj u hz
      simpa only [hu0, zero_add, Nat.cast_add, Nat.cast_one] using he
    · rw [← hud]
      exact fun he => hznot.2 ((MulAction.toPerm u).injective he)
  obtain ⟨r, hrfix, hrmove⟩ := hreg.2 _ _ huforward hzforward
  let x := u⁻¹*r*u
  have hxN : x ∈ trackNormalizer t :=
    mul_mem (mul_mem (inv_mem huN) (hmemN hrfix)) huN
  have hx0 : x • t.vertex 0 = t.vertex 0 := by
    have hrend : r • t.vertex (n+1) = t.vertex (n+1) := by
      apply t.mem_segmentFixer.mp ((t.fixes_arc_iff _ _ _).mp hrfix)
        (n+1) (by omega) (by omega)
    dsimp only [x]
    rw [mul_smul, mul_smul, hu0, hrend, ← hu0, inv_smul_smul]
  have hx1 : x • t.vertex 1 = z := by
    dsimp only [x]
    rw [mul_smul, mul_smul, hrmove, inv_smul_smul]
  obtain ⟨l, hlfix, hlmove⟩ := hreg.1 z (t.vertex (-1))
    ((hback z).2 ⟨hz, hznot.1⟩) ((hback _).2 ⟨had, hbd.symm⟩)
  let y := l*x
  have hyN : y ∈ trackNormalizer t := mul_mem (hmemN hlfix) hxN
  have hy0 : y • t.vertex 0 = t.vertex 0 := by
    dsimp only [y]
    rw [mul_smul, hx0, hfix0 hlfix]
  have hy1 : y • t.vertex 1 = t.vertex (-1) := by
    dsimp only [y]
    rw [mul_smul, hx1, hlmove]
  intro w hw
  by_cases he : w = t.vertex 1
  · exact ⟨1, one_mem _, one_smul _ _, by simpa only [one_smul] using he.symm⟩
  · obtain ⟨k, hkfix, hkmove⟩ := hreg.1 (t.vertex (-1)) w
      ((hback _).2 ⟨had, hbd.symm⟩) ((hback w).2 ⟨hw, he⟩)
    refine ⟨k*y, mul_mem (hmemN hkfix) hyN, ?_, ?_⟩
    · rw [mul_smul, hy0, hfix0 hkfix]
    · rw [mul_smul, hy1, hkmove]

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
