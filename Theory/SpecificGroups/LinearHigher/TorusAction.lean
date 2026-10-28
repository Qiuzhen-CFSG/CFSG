module

public import Theory.SpecificGroups.LinearHigher.RootCalculus

/-!
# Torus action and central Steinberg defects

The torus words act on every root with the expected diagonal weight.
Multiplicativity of these weights shows that
`hᵢⱼ(s) hᵢⱼ(t) hᵢⱼ(st)⁻¹` centralizes every generator, hence belongs to
the center of the actual Steinberg group. This proves centrality directly
from the defining relations, without assuming global matrix faithfulness
or a Bruhat theorem.

The final theorem supplies the centrality used in the finite-field
calculation of Steinberg, *Lectures on Chevalley Groups*, §6, Lemma 39,
printed pp.72–73 (`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

@[expose] public section

namespace Theory.SpecificGroups.LinearHigher.SteinbergWords

variable {n : ℕ} {F E : Type*} [Field F] [Group E]

def torusWeight (i j : Fin n) (t : Fˣ) (k : Fin n) : Fˣ :=
  if k = i then t else if k = j then t⁻¹ else 1

def rootWeight (i j : Fin n) (t : Fˣ) (r : Root n) : Fˣ :=
  torusWeight i j t r.val.1 / torusWeight i j t r.val.2

theorem torusWeight_mul (i j : Fin n) (s t : Fˣ) (k : Fin n) :
    torusWeight i j (s * t) k = torusWeight i j s k * torusWeight i j t k := by
  simp only [torusWeight]
  split_ifs <;> simp [mul_comm]

theorem rootWeight_mul (i j : Fin n) (s t : Fˣ) (r : Root n) :
    rootWeight i j (s * t) r = rootWeight i j s r * rootWeight i j t r := by
  simp only [rootWeight, torusWeight_mul]
  exact mul_div_mul_comm _ _ _ _

variable {x : Root n → F → E} (h : Relations x)
include h

theorem torusWord_conj_generator (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (t : Fˣ) (r : Root n) (a : F) :
    MulAut.conj (torusWord x i j hij t) (x r a) =
      x r ((rootWeight i j t r : F) * a) := by
  obtain ⟨⟨k, l⟩, hkl⟩ := r
  change MulAut.conj (torusWord x i j hij t) (x (root k l hkl) a) = _
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      simpa [rootWeight, torusWeight, root, hij, hij.symm, mul_assoc, mul_comm,
        mul_left_comm] using torusWord_conj_root h hn i j hij t a
    · simpa [rootWeight, torusWeight, root, hij, hkl.symm, hlj] using
        torusWord_conj_outgoing h i j l hij hkl (Ne.symm hlj) t a
  by_cases hkj : k = j
  · subst k
    by_cases hli : l = i
    · subst l
      simpa [rootWeight, torusWeight, root, hij, hij.symm, div_eq_mul_inv, mul_assoc, mul_comm,
        mul_left_comm] using torusWord_conj_opposite_root h hn i j hij t a
    · simpa [rootWeight, torusWeight, root, hij.symm, hli, hkl.symm] using
        torusWord_conj_other_outgoing h i j l hij (Ne.symm hli) hkl t a
  by_cases hli : l = i
  · subst l
    simpa [rootWeight, torusWeight, root, hki, hkj, mul_comm] using
      torusWord_conj_other_incoming h i j k hij hki hkj t a
  by_cases hlj : l = j
  · subst l
    simpa [rootWeight, torusWeight, root, hki, hkj, hij.symm, mul_comm] using
      torusWord_conj_incoming h i j k hij hki hkj t a
  have hd (b : F) : MulAut.conj (x (root i j hij) b) (x (root k l hkl) a) =
      x (root k l hkl) a := h.conj_distant _ _ b a (Ne.symm hkj) hli
  have hd' (b : F) : MulAut.conj (x (root j i hij.symm) b) (x (root k l hkl) a) =
      x (root k l hkl) a := h.conj_distant _ _ b a (Ne.symm hki) hlj
  simp only [torusWord, weylWord, map_mul, MulAut.mul_apply, hd, hd']
  simp [rootWeight, torusWeight, root, hki, hkj, hli, hlj]

omit h in
theorem torusWord_defect_mem_center (hn : 2 < n) (i j : Fin n) (hij : i ≠ j)
    (s t : Fˣ) :
    torusWord (generator (F := F)) i j hij s * torusWord generator i j hij t *
      (torusWord generator i j hij (s * t))⁻¹ ∈ Subgroup.center (SteinbergGroup n F) := by
  have he :
      (MulAut.conj (torusWord (generator (F := F)) i j hij s *
        torusWord generator i j hij t)).toMonoidHom =
      (MulAut.conj (torusWord generator i j hij (s * t))).toMonoidHom := by
    apply PresentedGroup.ext
    rintro ⟨r, a⟩
    change MulAut.conj (_ * _) (generator r a) =
      MulAut.conj (torusWord generator i j hij (s * t)) (generator r a)
    simp only [map_mul, MulAut.mul_apply, torusWord_conj_generator generator_relations hn,
      rootWeight_mul, Units.val_mul, mul_assoc]
  have he' : MulAut.conj (torusWord (generator (F := F)) i j hij s *
        torusWord generator i j hij t) =
      MulAut.conj (torusWord generator i j hij (s * t)) := by
    ext g
    exact DFunLike.congr_fun he g
  have hc : MulAut.conj (torusWord (generator (F := F)) i j hij s *
      torusWord generator i j hij t * (torusWord generator i j hij (s * t))⁻¹) = 1 := by
    rw [map_mul, map_inv, he', mul_inv_cancel]
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := congrArg (fun f : MulAut (SteinbergGroup n F) => f g) hc
  change _ * g * _ = g at hg
  exact (mul_inv_eq_iff_eq_mul.mp hg).symm

end Theory.SpecificGroups.LinearHigher.SteinbergWords
