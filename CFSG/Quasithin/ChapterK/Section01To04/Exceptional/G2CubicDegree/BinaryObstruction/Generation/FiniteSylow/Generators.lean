module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.FiniteSylow.BasicMatrices

/-!
# Recovering the full binary G₂ group from five elements

C, E, F and the two Weyl reflections recover A, B and D by conjugation.
All binary root groups therefore lie in the generated subgroup. The split
torus is trivial, so the existing root-and-torus generation theorem applies.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11. Root conventions are inherited from the ATLAS port;
Gerald Höhn and the ATLAS contributors, ATLAS Research and Attribution License
1.0 (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow

/-- The five recovered elements generate the original octonion group. -/
theorem eq_top_of_basic_letters (K : Subgroup G) (h : ∀ j, basicLetter j ∈ K) : K = ⊤ := by
  have hC : rootC (1 : ZMod 2) ∈ K := h 0
  have hE : rootE (1 : ZMod 2) ∈ K := h 1
  have hF : rootF (1 : ZMod 2) ∈ K := h 2
  have hR : (weylR : G) ∈ K := h 3
  have hS : (weylS : G) ∈ K := h 4
  have undo (x y : G) (hx : x ∈ K) (hxy : x*y*x⁻¹ ∈ K) : y ∈ K := by
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      K.mul_mem (K.mul_mem (K.inv_mem hx) hxy) hx
  have hB : rootB (1 : ZMod 2) ∈ K := undo _ _ hS (by rwa [weylS_rootB])
  have hA : rootA (1 : ZMod 2) ∈ K := undo _ _ hR (by rwa [weylR_rootA])
  have hD : rootD (1 : ZMod 2) ∈ K := undo _ _ hR (by rwa [weylR_rootD])
  have binary (f : ZMod 2 → G) (h0 : f 0 = 1) (h1 : f 1 ∈ K) : ∀ t, f t ∈ K := by
    intro t
    have ht : t = 0 ∨ t = 1 := (by decide +kernel : ∀ t : ZMod 2, t=0 ∨ t=1) t
    rcases ht with rfl | rfl
    · exact h0 ▸ K.one_mem
    · exact h1
  have hU : unipotent ≤ K := by
    apply (Subgroup.closure_le K).mpr
    rintro g (((((hg|hg)|hg)|hg)|hg)|hg)
    all_goals obtain ⟨t,rfl⟩ := hg
    · exact binary rootA rootA_zero hA t
    · exact binary rootB rootB_zero hB t
    · exact binary rootC rootC_zero hC t
    · exact binary rootD rootD_zero hD t
    · exact binary rootE rootE_zero hE t
    · exact binary rootF rootF_zero hF t
  apply top_unique
  rw [← generated_eq_top]
  apply sup_le
  · apply (Subgroup.closure_le K).mpr
    rintro g (hg | hg)
    · exact hU hg
    · rcases hg with (rfl | rfl)
      · exact hR
      · exact hS
  · rintro g ⟨⟨a,b⟩,rfl⟩
    change torus a b ∈ K
    rw [BinaryException.binary_torus]
    exact K.one_mem

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
