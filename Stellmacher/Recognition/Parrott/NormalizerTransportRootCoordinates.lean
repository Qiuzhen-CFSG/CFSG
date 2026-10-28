module

public import Stellmacher.Recognition.Parrott.NormalizerTransportRootAlgebra
public import Stellmacher.Recognition.Parrott.NormalizerTransportFusionCoordinates
public import Stellmacher.Recognition.Parrott.NormalizerRootWordUniqueness
public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquareCoordinates
public import Stellmacher.Recognition.Parrott.NormalizerRootWordSquareCollection

/-!
# Coordinates of a supplied Parrott normalizer transport

Every supplied transport satisfies aˢ ∈ u⟨z⟩ and xˢ ∈ caw⟨u,t,z⟩.
The faithful ordered coordinates exhaust the normalizer core. Their square
calculation restricts the roots of wuvtz to four noncentral patterns, which
lie in cav⟨u,t,z⟩ or caw⟨u,t,z⟩. The elementary fusion restriction on aˢ
and the transported commutator relations then give both conclusions.

All coordinates and the transport are retained literally. The proof uses
the original centralizer hypotheses and the checked finite square calculation;
it requires no involution-orbit census or replacement transport.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
printed p.682, first paragraph.
-/

open Subgroup
namespace Stellmacher.Recognition
open ParrottNormalizerRootSquare
variable {G : Type*} [Group G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

private theorem tail {p q o : G} (hp : p * q = o) (k : G) :
    p * (q * k) = o * k := by rw [← mul_assoc, hp]

-- Code (8,4,3) evaluates to c²vtz = wuvtz. The last two bits of
-- a root are free, so only the head and three noncentral bits occur here.
private theorem finite_roots : ∀ p : Fin 32 × Fin 8,
    smallSquare p = (8,4,3) →
      (p.1 = 4 ∧ (p.2 = 5 ∨ p.2 = 7)) ∨
      (p.1 = 12 ∧ (p.2 = 1 ∨ p.2 = 3)) := by decide +kernel

private theorem word_root_coordinates (f : ParrottSylowGeneratorData n)
    (p : Code) (hp : square p = (8,4,3)) :
    ∃ q ∈ closure ({f.u, n.t, z} : Set G),
      word f p = f.c * f.a * q ∨
      word f p = f.c * f.a * f.w * q ∨
      word f p = f.c * f.a * n.v * q ∨
      word f p = f.c * f.a * f.w * n.v * q := by
  let L := closure ({f.u, n.t, z} : Set G)
  have hu : f.u ∈ L := subset_closure (by simp)
  have hz : z ∈ L := subset_closure (by simp)
  have ht : n.t ∈ L := subset_closure (by simp)
  rcases p with ⟨i,r,j⟩
  let q := n.t ^ (j.val % 2) * z ^ (j.val / 2)
  have hq : q ∈ L := L.mul_mem (L.pow_mem ht _) (L.pow_mem hz _)
  have hwa : f.w * f.a = f.a * f.w * z := by
    rw [(Tits.parrottCommutator_eq_iff _ _ _).mp f.eq02_aw]
    simp only [mul_assoc, ← pow_two, f.z_sq, mul_one]
  have hc3 : f.c ^ 3 = f.c * (f.w * f.u) := by
    rw [pow_succ', f.eq13]
  have huu : f.u * f.u = 1 := by simpa only [pow_two] using f.u_sq
  rcases finite_roots (i,r) hp with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
  · refine ⟨q, hq, Or.inr (Or.inr (Or.inl ?_))⟩
    simp [word, tailWord, q, mul_assoc]
  · refine ⟨f.u * q, L.mul_mem hu hq, Or.inr (Or.inr (Or.inl ?_))⟩
    simp [word, tailWord, q, mul_assoc, tail f.comm_vu.symm.eq]
  · refine ⟨z * f.u * q, L.mul_mem (L.mul_mem hz hu) hq, Or.inr (Or.inl ?_)⟩
    simp only [word, tailWord]
    norm_num
    simp only [q, hc3, mul_assoc, tail f.comm_au.symm.eq, tail hwa]
  · refine ⟨z * q, L.mul_mem hz hq, Or.inr (Or.inl ?_)⟩
    simp only [word, tailWord]
    norm_num
    simp only [q, hc3, mul_assoc, tail f.comm_au.symm.eq, tail hwa, tail huu, one_mul]

/-- The supplied transport satisfies both root-coordinate conclusions on p.682.
Faithful finite core words give root exhaustion, and elementary fusion and the
transported commutator relations eliminate the remaining alternatives. -/
public theorem ParrottNormalizerTransportData.root_coordinates [Finite G]
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f)
    (h : ParrottCentralizerHypotheses z) :
    (k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z) ∧
    (f.c * f.a * f.w)⁻¹ * (k.s⁻¹ * f.x * k.s) ∈ closure ({f.u, n.t, z} : Set G) := by
  let d := f.toParrottSylowGeneratorData
  have hi := d.normalizerRootWord_injective h
  have hc := coordinateLaws d hi
  have hr : k.s⁻¹ * f.x * k.s ∈ Set.range (word d) := by
    rw [hc.range_eq_words, d.normalizerRootWord_range_of_injective hi]
    exact k.x_conj_mem_normalizer_core
  obtain ⟨p, hp⟩ := hr
  have hs : word d (8,4,3) = f.w * f.u * n.v * n.t * z := by
    simp [word, tailWord, d, f.eq13, mul_assoc]
  have hsq : square p = (8,4,3) := hc.injective (by
    rw [square_eval, hp, k.x_conj_sq, hs])
  apply k.root_coordinates_of_exhaustion_and_fusion
  · simpa only [hp] using word_root_coordinates d p hsq
  · exact k.a_conj_fusion_coordinates h

/-- The image of a under every supplied transport lies in u⟨z⟩. -/
public theorem ParrottNormalizerTransportData.a_conj_eq_u_or_uz [Finite G]
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f)
    (h : ParrottCentralizerHypotheses z) :
    k.s⁻¹ * f.a * k.s = f.u ∨ k.s⁻¹ * f.a * k.s = f.u * z :=
  (k.root_coordinates h).1

/-- The transported x lies in the literal coset caw⟨u,t,z⟩. -/
public theorem ParrottNormalizerTransportData.x_conj_mem_caw_coset [Finite G]
    {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerTransportData f)
    (h : ParrottCentralizerHypotheses z) :
    (f.c * f.a * f.w)⁻¹ * (k.s⁻¹ * f.x * k.s) ∈
      closure ({f.u, n.t, z} : Set G) :=
  (k.root_coordinates h).2

end Stellmacher.Recognition
