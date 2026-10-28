module

public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Placement
public import Theory.SpecificGroups.PSL3Even.MinimalParabolicWitness.LongRoot
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearTwo.Source

/-!
# The genuine linear-three two-conjugate witness

Minimal parabolicity and the original corefree maximal subgroup place the
original elementary normal subgroup V in a marked highest root of the normal
PSL₃ group. The concrete root SL₂ supplies an internal conjugator and its
binary subfield model. The two literal subgroup embeddings preserve the
original Sylow and Borel intersections, so the resulting source Pair retains
H,T,M,V, its internal conjugator, and the exact SL₂ model of degree k>1 dividing n.

Source: Aschbacher--Smith, E.2.7, printed p.219.
-/

public section
open scoped MatrixGroups IsMulCommutative
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3Even.MinimalParabolicWitness
open Matrix.PSL3Even.UnipotentGeometry
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearThree
open ChapterB
variable {H : Type*} [Group H] [Finite H]
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
variable (K : Subgroup H) [K.Normal] [IsSimpleGroup K]
variable (e : K ≃* PSL(3,F)) (T : Sylow 2 H)

include e hn hF in
/-- The complete surviving PSL₃ binary branch, with the original subgroup V.
The degree-one case cannot satisfy the noncyclic elementary hypotheses. -/
theorem exists_witness (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : IsMinimalParabolicOver T ⊤)
    (hcore : (minimalParabolicMax T hP).normalCore = ⊥)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hc : 4 ≤ Nat.card V) :
    Nonempty (LinearTwo.Witness T (minimalParabolicMax T hP) V n) := by
  obtain ⟨g,hU,hB,hZ⟩ := Structure.LinearThree.exists_longRoot_placement
    F hn hF K e T hgen hP hcore V hVT hVN
  let f := modelEmbedding F K (e.trans (MulAut.conj g))
  have hf : Function.Injective f := modelEmbedding_injective F K _
  let W := V.comap f
  have hWr : V ≤ f.range := hZ.trans (map_le_range _ _)
  have hWV : W.map f = V := map_comap_eq_self hWr
  have hWZ : W ≤ projectiveCenter F := by
    have hh := comap_mono (f := f) hZ
    rwa [comap_map_eq_self_of_injective hf] at hh
  have hWc : 4 ≤ Nat.card W := by
    rw [← Subgroup.card_map_of_injective (f := f) (K := W) hf,hWV]
    exact hc
  obtain ⟨w⟩ := exists_longRoot_witness F hF W hWZ hWc
  have wm := w.map f hf (T : Subgroup H) (minimalParabolicMax T hP) hU hB
  rw [hWV] at wm
  exact ⟨LinearTwo.of_model_witness wm⟩

include e hn hF in
/-- The source rank formulation retains the strict parameter and its divisibility. -/
theorem exists_witness_of_rank (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : IsMinimalParabolicOver T ⊤)
    (hcore : (minimalParabolicMax T hP).normalCore = ⊥)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hr : 2 ≤ Module.finrank (ZMod 2) (Additive V)) :
    ∃ w : LinearTwo.Witness T (minimalParabolicMax T hP) V n,
      Module.finrank (ZMod 2) (Additive V) ≤ w.degree := by
  have hcV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  have hc : 4 ≤ Nat.card V := by
    rw [hcV]
    exact (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by decide) hr
  obtain ⟨w⟩ := exists_witness F hn hF K e T hgen hP hcore V hVT hVN hc
  exact ⟨w,w.rank_le_degree hVT⟩

include e hF in
/-- The positive binary degree is genuinely greater than one under the original
noncyclic elementary hypotheses; the degree-one exception is thereby excluded. -/
theorem one_lt_parameter (hn : 0 < n) (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hP : IsMinimalParabolicOver T ⊤)
    (hcore : (minimalParabolicMax T hP).normalCore = ⊥)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ (T : Subgroup H)) (hVN : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hc : 4 ≤ Nat.card V) : 1 < n := by
  obtain ⟨w⟩ := exists_witness F hn hF K e T hgen hP hcore V hVT hVN hc
  exact w.degree_gt_one.trans_le (Nat.le_of_dvd hn w.degree_dvd)

end CFSG.Quasithin.ChapterE.Witnesses.LinearThree
