module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.ZDTerminal.FactorAlternatives.InternalRigidity.Transport
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import Theory.SpecificGroups.Suzuki.InvolutionFusion

/-!
# Sylow-factor rigidity in a Suzuki group

Commuting root elements with nonzero first coordinates have the same first
coordinate: their ratio is fixed by the Tits automorphism, whose fixed field
is the prime field. If both factors contained such elements, their strongly
closed union could have only one nonzero first coordinate, contradicting the
split torus action. Thus one factor has first coordinate zero.

If the other factor is noncentral, strong closure puts a root element with
every nonzero first coordinate in it. Squaring these elements covers the
zero-first-coordinate subgroup, since the twisted norm a ↦ a·pi(a) is
surjective (its inverse away from zero is b ↦ pi(b)/b). If both factors have
first coordinate zero, involution fusion and the two-subgroup union lemma
prove nesting. Sylow conjugacy transports this calculation to any Sylow
subgroup. The public statement retains both elementary-four hypotheses.

Source: Huppert--Blackburn III, XI.3.1 and XI.3.3; Aschbacher (1975),
Lemma 3.4, final paragraph, printed p.96.
-/

@[expose] public section

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity

private noncomputable def rootA (m : ℕ) (x : SuzukiMatrixGroup m) :
    BinaryGaloisField (2 * m + 1) :=
  ((x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 0 1

private noncomputable def rootB (m : ℕ) (x : SuzukiMatrixGroup m) :
    BinaryGaloisField (2 * m + 1) :=
  ((x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) :
    Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 0 2

private theorem root_coords {m : ℕ} {x : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) :
    (x : GL (Fin 4) (BinaryGaloisField (2 * m + 1))) =
      SuzukiRootGL m (rootA m x) (rootB m x) := by
  obtain ⟨a, b, h⟩ := (mem_suzukiRootSubgroup_iff m x).mp hx
  have ha := congrArg (fun A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
    (A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 0 1) h
  have hb := congrArg (fun A : GL (Fin 4) (BinaryGaloisField (2 * m + 1)) =>
    (A : Matrix (Fin 4) (Fin 4) (BinaryGaloisField (2 * m + 1))) 0 2) h
  have ha' : rootA m x = a := by
    simpa [rootA, SuzukiRootGL, SuzukiRootMatrix] using ha
  have hb' : rootB m x = b := by
    simpa [rootB, SuzukiRootGL, SuzukiRootMatrix] using hb
  simpa [ha', hb'] using h

private theorem rootA_mul {m : ℕ} {x y : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) (hy : y ∈ SuzukiRootSubgroup m) :
    rootA m (x * y) = rootA m x + rootA m y := by
  change (x.val * y.val).val 0 1 = _
  rw [root_coords hx, root_coords hy]
  simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four, add_comm]

private theorem rootB_mul {m : ℕ} {x y : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) (hy : y ∈ SuzukiRootSubgroup m) :
    rootB m (x * y) = rootB m x + rootB m y +
      rootA m x * (suzukiTits m) (rootA m y) := by
  change (x.val * y.val).val 0 2 = _
  rw [root_coords hx, root_coords hy]
  simp [SuzukiRootGL, SuzukiRootMatrix, Matrix.mul_apply, Fin.sum_univ_four,
    suzukiTits_apply, add_comm, add_left_comm, add_assoc]

private theorem rootA_inv {m : ℕ} {x : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) : rootA m x⁻¹ = rootA m x := by
  have h := rootA_mul hx ((SuzukiRootSubgroup m).inv_mem hx)
  have h0 : rootA m (1 : SuzukiMatrixGroup m) = 0 := by simp [rootA]
  rw [mul_inv_cancel, h0] at h
  have h' := congrArg (fun z => rootA m x + z) h
  simpa only [add_zero, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] using h'.symm

private theorem root_commute_coord {m : ℕ} {x y : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) (hy : y ∈ SuzukiRootSubgroup m)
    (hxy : Commute x y) :
    rootA m x * (suzukiTits m) (rootA m y) =
      rootA m y * (suzukiTits m) (rootA m x) := by
  have h := congrArg (rootB m) hxy.eq
  rw [rootB_mul hx hy, rootB_mul hy hx] at h
  linear_combination h

private theorem root_square {m : ℕ} {x : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) :
    rootA m (x ^ 2) = 0 ∧
      rootB m (x ^ 2) = rootA m x * (suzukiTits m) (rootA m x) := by
  have hA := rootA_mul hx hx
  have hB := rootB_mul hx hx
  rw [pow_two]
  constructor
  · simpa [CharTwo.add_self_eq_zero] using hA
  · simpa [CharTwo.add_self_eq_zero] using hB

private noncomputable def torus (m : ℕ) (t : (BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiTorusGL m t, subset_closure (Or.inr (Or.inl ⟨t, rfl⟩))⟩

private theorem root_torus_coord {m : ℕ} {x : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) (t : (BinaryGaloisField (2 * m + 1))ˣ) :
    rootA m (torus m t * x * (torus m t)⁻¹) =
      (t : BinaryGaloisField (2 * m + 1)) * rootA m x := by
  change ((SuzukiTorusGL m t * x.val * (SuzukiTorusGL m t)⁻¹).val) 0 1 = _
  rw [root_coords hx, BenderSuzuki.External.suzukiTorusGL_conj_root m
    (suzukiTits m) (suzukiTits_sq m) (suzukiTits_apply m)]
  simp [SuzukiRootGL, SuzukiRootMatrix]

private theorem root_conjugate_mem_of_torus
    {m : ℕ} {x : SuzukiMatrixGroup m}
    (hx : x ∈ SuzukiRootSubgroup m) (t : (BinaryGaloisField (2 * m + 1))ˣ) :
    torus m t * x * (torus m t)⁻¹ ∈ SuzukiRootSubgroup m := by
  have ht : torus m t ∈ SuzukiSplitTorus m := subset_closure ⟨t, rfl⟩
  exact (mem_normalizer_iff.mp (suzukiSplitTorus_le_normalizer_root m ht) x).mp hx

private noncomputable def rootZeroSubgroup (m : ℕ) : Subgroup (SuzukiMatrixGroup m) where
  carrier := {x | x ∈ SuzukiRootSubgroup m ∧ rootA m x = 0}
  one_mem' := by simp [rootA]
  mul_mem' := by
    intro x y hx hy
    exact ⟨(SuzukiRootSubgroup m).mul_mem hx.1 hy.1,
      by rw [rootA_mul hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  inv_mem' := by
    intro x hx
    exact ⟨(SuzukiRootSubgroup m).inv_mem hx.1, by rw [rootA_inv hx.1, hx.2]⟩

private theorem rootZero_mem_iff {m : ℕ} {x : SuzukiMatrixGroup m} :
    x ∈ rootZeroSubgroup m ↔ x ∈ SuzukiRootSubgroup m ∧ rootA m x = 0 := Iff.rfl

private theorem rootZero_square {m : ℕ} {x : SuzukiMatrixGroup m}
    (hx : x ∈ rootZeroSubgroup m) : x ^ 2 = 1 := by
  apply Subtype.ext
  rw [root_coords ((SuzukiRootSubgroup m).pow_mem hx.1 2),
    (root_square hx.1).1, (root_square hx.1).2, hx.2, zero_mul,
    BenderSuzuki.External.suzukiRootGL_zero_zero]
  rfl

private theorem fixed_tits {m : ℕ} (x : BinaryGaloisField (2 * m + 1))
    (h : (suzukiTits m) x = x) : x = 0 ∨ x = 1 := by
  have hs := suzukiTits_sq m x
  rw [h, h] at hs
  have hz : x * (x - 1) = 0 := by
    calc
      x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := by rw [← hs]; ring
  rcases mul_eq_zero.mp hz with hx | hx
  · exact Or.inl hx
  · exact Or.inr (sub_eq_zero.mp hx)

private theorem commuting_first_line {m : ℕ} {a : BinaryGaloisField (2 * m + 1)}
    (ha : a ≠ 0) {b : BinaryGaloisField (2 * m + 1)}
    (h : a * (suzukiTits m) b = b * (suzukiTits m) a) :
    b = 0 ∨ b = a := by
  let r := b / a
  have hfix : (suzukiTits m) r = r := by
    dsimp [r]
    rw [map_div₀]
    apply (div_eq_div_iff ((map_ne_zero (suzukiTits m)).mpr ha) ha).2
    calc
      (suzukiTits m) b * a = a * (suzukiTits m) b := mul_comm _ _
      _ = b * (suzukiTits m) a := h
  rcases fixed_tits r hfix with hr | hr
  · exact Or.inl ((div_eq_zero_iff).mp hr |>.resolve_right ha)
  · right
    simpa using (div_eq_iff ha).mp hr

private theorem closed_torus {m : ℕ} {B C : Subgroup (SuzukiMatrixGroup m)}
    (hc : IsStronglyClosedSet ((B : Set _) ∪ C) (SuzukiRootSubgroup m) ⊤)
    {x : SuzukiMatrixGroup m} (hx : x ∈ (B : Set _) ∪ C)
    (t : (BinaryGaloisField (2 * m + 1))ˣ) :
    torus m t * x * (torus m t)⁻¹ ∈ (B : Set _) ∪ C := by
  have h := hc.2 x hx (torus m t)⁻¹ (mem_top _)
    (by simpa only [inv_inv] using root_conjugate_mem_of_torus (hc.1 hx) t)
  simpa only [inv_inv] using h

private theorem one_factor_central {m : ℕ} (hm : 0 < m)
    {B C : Subgroup (SuzukiMatrixGroup m)}
    (hB : B ≤ SuzukiRootSubgroup m) (hC : C ≤ SuzukiRootSubgroup m)
    (hcomm : ∀ x ∈ B, ∀ y ∈ C, Commute x y)
    (hc : IsStronglyClosedSet ((B : Set _) ∪ C) (SuzukiRootSubgroup m) ⊤) :
    B ≤ rootZeroSubgroup m ∨ C ≤ rootZeroSubgroup m := by
  classical
  by_contra h
  push Not at h
  obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp h.1
  obtain ⟨y, hy, hyZ⟩ := Set.not_subset.mp h.2
  have hxa : rootA m x ≠ 0 := fun he => hxZ ⟨hB hx, he⟩
  have hya : rootA m y ≠ 0 := fun he => hyZ ⟨hC hy, he⟩
  have heq : rootA m y = rootA m x :=
    (commuting_first_line hxa (root_commute_coord (hB hx) (hC hy)
      (hcomm x hx y hy))).resolve_left hya
  have hline : ∀ z ∈ (B : Set _) ∪ C, rootA m z = 0 ∨ rootA m z = rootA m x := by
    intro z hz
    rcases hz with hz | hz
    · simpa only [heq] using commuting_first_line hya
        (root_commute_coord (hC hy) (hB hz) (hcomm z hz y hy).symm)
    · exact commuting_first_line hxa
        (root_commute_coord (hB hx) (hC hz) (hcomm x hx z hz))
  have hcard : 1 < Nat.card (BinaryGaloisField (2*m+1))ˣ := by
    rw [Nat.card_units, GaloisField.card 2 (2*m+1) (by omega)]
    have hq : 4 ≤ 2 ^ (2*m+1) :=
      (show 4 = 2^2 by norm_num).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega))
    omega
  let : Nontrivial (BinaryGaloisField (2*m+1))ˣ :=
    Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨t, ht⟩ := exists_ne (1 : (BinaryGaloisField (2*m+1))ˣ)
  have htval : (t : BinaryGaloisField (2*m+1)) ≠ 1 :=
    fun hh => ht (Units.ext hh)
  have htline := hline _ (closed_torus hc (Or.inl hx) t)
  rw [root_torus_coord (hB hx)] at htline
  rcases htline with hz | hz
  · exact (mul_ne_zero t.ne_zero hxa) hz
  · exact htval (mul_right_cancel₀ hxa (hz.trans (one_mul _).symm))

private theorem central_le_noncentral {m : ℕ}
    {B C : Subgroup (SuzukiMatrixGroup m)}
    (hB : B ≤ SuzukiRootSubgroup m) (hCZ : C ≤ rootZeroSubgroup m)
    (hc : IsStronglyClosedSet ((B : Set _) ∪ C) (SuzukiRootSubgroup m) ⊤)
    {x : SuzukiMatrixGroup m} (hx : x ∈ B) (hxa : rootA m x ≠ 0) :
    rootZeroSubgroup m ≤ B := by
  have hcoord : ∀ a : BinaryGaloisField (2*m+1), a ≠ 0 →
      ∃ y ∈ B, rootA m y = a := by
    intro a ha
    let t : (BinaryGaloisField (2*m+1))ˣ := Units.mk0 (a / rootA m x) (div_ne_zero ha hxa)
    let y := torus m t * x * (torus m t)⁻¹
    have hya : rootA m y = a := by
      rw [root_torus_coord (hB hx)]
      exact div_mul_cancel₀ a hxa
    have hyB : y ∈ B := by
      rcases closed_torus hc (Or.inl hx) t with hh | hh
      · exact hh
      · exact (ha (hya.symm.trans (hCZ hh).2)).elim
    exact ⟨y, hyB, hya⟩
  intro z hz
  by_cases hb : rootB m z = 0
  · have hz1 : z = 1 := by
      apply Subtype.ext
      rw [root_coords hz.1, hz.2, hb, BenderSuzuki.External.suzukiRootGL_zero_zero]
      rfl
    exact hz1 ▸ B.one_mem
  let b := rootB m z
  let a := suzukiTits m b / b
  have hpi : suzukiTits m b ≠ 0 := (map_ne_zero _).mpr hb
  have ha : a ≠ 0 := div_ne_zero hpi hb
  have hnorm : a * suzukiTits m a = b := by
    dsimp only [a]
    rw [map_div₀, suzukiTits_sq]
    field_simp [hb, hpi]
  obtain ⟨y, hy, hya⟩ := hcoord a ha
  have hy2 : y ^ 2 = z := by
    apply Subtype.ext
    rw [root_coords ((SuzukiRootSubgroup m).pow_mem (hB hy) 2), root_coords hz.1,
      (root_square (hB hy)).1, (root_square (hB hy)).2, hz.2, hya, hnorm]
  exact hy2 ▸ B.pow_mem hy 2

private theorem root_factors_nested {m : ℕ} (hm : 0 < m)
    (B C : Subgroup (SuzukiMatrixGroup m))
    (hB : B ≤ SuzukiRootSubgroup m) (hC : C ≤ SuzukiRootSubgroup m)
    (hBC : ⁅B,C⁆ = ⊥) (hBr : TwoRankAtLeastTwo B)
    (hc : IsStronglyClosedSet ((B : Set _) ∪ C) (SuzukiRootSubgroup m) ⊤) :
    B ≤ C ∨ C ≤ B := by
  classical
  have hcomm : ∀ x ∈ B, ∀ y ∈ C, Commute x y := by
    intro x hx y hy
    exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hBC) hx) y hy).symm
  have hswap : IsStronglyClosedSet ((C : Set _) ∪ B) (SuzukiRootSubgroup m) ⊤ := by
    rwa [Set.union_comm]
  have hcentral : B ≤ rootZeroSubgroup m → C ≤ rootZeroSubgroup m → B ≤ C ∨ C ≤ B := by
    intro hBZ hCZ
    have hBne : B ≠ ⊥ := by
      obtain ⟨E, hE, _⟩ := hBr
      have he := card_le_card_group E
      rw [hE] at he
      intro hb
      rw [hb] at he
      simp at he
    obtain ⟨x, hxne⟩ := ne_bot_iff_exists_ne_one.mp hBne
    have hxi : orderOf (x : SuzukiMatrixGroup m) = 2 :=
      orderOf_eq_prime (rootZero_square (hBZ x.property)) (fun he => hxne (Subtype.ext he))
    have hcover : (rootZeroSubgroup m : Set (SuzukiMatrixGroup m)) ⊆ (B : Set (SuzukiMatrixGroup m)) ∪ C := by
      intro z hz
      by_cases hz1 : z = 1
      · exact Or.inl (hz1 ▸ B.one_mem)
      have hzi : orderOf z = 2 := orderOf_eq_prime (rootZero_square hz) hz1
      obtain ⟨g, hg⟩ := isConj_iff.mp (suzuki_involutions_isConj m hm x z hxi hzi)
      have hh := hc.2 x (Or.inl x.property) g⁻¹ (mem_top _)
        (by simpa only [inv_inv, hg] using hz.1)
      simpa only [inv_inv, hg] using hh
    rcases SubgroupClass.subset_union.mp hcover with hzB | hzC
    · exact Or.inr (hCZ.trans hzB)
    · exact Or.inl (hBZ.trans hzC)
  rcases one_factor_central hm hB hC hcomm hc with hBZ | hCZ
  · by_cases hCZ : C ≤ rootZeroSubgroup m
    · exact hcentral hBZ hCZ
    · obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp hCZ
      have hxa : rootA m x ≠ 0 := fun he => hxZ ⟨hC hx, he⟩
      exact Or.inl (hBZ.trans (central_le_noncentral hC hBZ hswap hx hxa))
  · by_cases hBZ : B ≤ rootZeroSubgroup m
    · exact hcentral hBZ hCZ
    · obtain ⟨x, hx, hxZ⟩ := Set.not_subset.mp hBZ
      have hxa : rootA m x ≠ 0 := fun he => hxZ ⟨hB hx, he⟩
      exact Or.inr (hCZ.trans (central_le_noncentral hB hCZ hc hx hxa))

/-- Commuting Sylow factors with strongly closed union nest in Sz(2^(2m+1)). -/
theorem suzuki_rigidity (m : ℕ) (hm : 1 ≤ m) :
    SylowFactorRigidity (SuzukiMatrixGroup m) := by
  intro P B C hBP hCP hBC hB _hC hc
  obtain ⟨Q, hQ⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) P Q
  let e := MulAut.conj g
  have hP : (P : Subgroup (SuzukiMatrixGroup m)).map e.toMonoidHom = SuzukiRootSubgroup m := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hQ] at hh
    exact hh
  have hc' : IsStronglyClosedSet ((B.map e.toMonoidHom : Set _) ∪ C.map e.toMonoidHom)
      (SuzukiRootSubgroup m) ⊤ := by
    rw [← hP]
    simpa only [Set.image_union, Subgroup.coe_map] using
      stronglyClosed_image P ((B : Set _) ∪ C) hc e.toMonoidHom e.surjective
  have hB' : TwoRankAtLeastTwo (B.map e.toMonoidHom) :=
    rank_map_of_injective (e.toMonoidHom.subgroupMap B)
      (fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))) hB
  have hBC' : ⁅B.map e.toMonoidHom, C.map e.toMonoidHom⁆ = ⊥ := by
    rw [← map_commutator, hBC, Subgroup.map_bot]
  have hBP' : B.map e.toMonoidHom ≤ SuzukiRootSubgroup m := hP ▸ map_mono hBP
  have hCP' : C.map e.toMonoidHom ≤ SuzukiRootSubgroup m := hP ▸ map_mono hCP
  have hreflect : ∀ A D : Subgroup (SuzukiMatrixGroup m),
      A.map e.toMonoidHom ≤ D.map e.toMonoidHom → A ≤ D := by
    intro A D h x hx
    obtain ⟨y, hy, he⟩ := h (mem_map_of_mem e.toMonoidHom hx)
    exact e.injective he ▸ hy
  rcases root_factors_nested hm _ _ hBP' hCP' hBC' hB' hc' with h | h
  · exact Or.inl (hreflect B C h)
  · exact Or.inr (hreflect C B h)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75.InternalRigidity
end
