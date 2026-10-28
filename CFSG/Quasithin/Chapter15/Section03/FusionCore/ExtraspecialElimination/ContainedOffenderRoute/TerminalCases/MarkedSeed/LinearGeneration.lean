module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Four
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.Generation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Flags

/-!
# Cubic generation of binary linear Sylow overgroups

For PSLₙ(2), 3 ≤ n ≤ 5, every overgroup K of a Sylow two-subgroup P
satisfies K = theta K ⊔ P, where theta uses actual elements of order three.
No representation, designated parabolic, or solvability premise occurs.

In degrees four and five, conjugate to the standard Sylow and apply the
proved Bruhat flag classification to both K and theta K ⊔ P. Multiplying
an adjacent basis swap by the corresponding upper transvection gives an
element of order three. Thus the two overgroups allow exactly the same
adjacent swaps and have the same flag cuts. The private flag calculations
below adapt `ParabolicIdentification.Linear.Flags` without changing its API.
In degree three, the existing checked Bruhat decomposition has six Weyl
representatives: each is the identity, is cubic, or becomes cubic after
multiplication by an upper transvection. The only new finite checks are
these explicit three-by-three matrix identities, checked by the kernel.
Finally the actual central-quotient equivalences transport the statements
from the linear models to the requested projective groups.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(l) and the seed-point stabilizers on printed pp.1144–1145.
The application importing `MarkedSeed` is separate to preserve the intrinsic
module boundary and allow later source assembly to import this theorem.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.LinearGeneration
open ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open Chapter2.ComponentRefinement.LieType.Binary

private theorem mem_cutStabilizer_maps {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (g : BinaryLinear.GL (Vector (m + 1))) :
    g ∈ cutStabilizer b cuts ↔
      ∀ i ∈ cuts, ∀ v ∈ cutSpace b i, g v ∈ cutSpace b i := by
  rw [mem_cutStabilizer]
  constructor
  · exact fun h i hi v hv => (h i hi v).mpr hv
  · intro h i hi v
    refine ⟨?_, h i hi v⟩
    intro hv
    let f : cutSpace b i → cutSpace b i := fun w => ⟨g w, h i hi w w.property⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (g.injective (congrArg Subtype.val hxy))
    obtain ⟨w, hw⟩ := (Finite.surjective_of_injective hf) ⟨g v, hv⟩
    exact (g.injective (congrArg Subtype.val hw)) ▸ w.property

private noncomputable def swapCut {m : ℕ} (b : Basis m) (i : Fin m) :
    BinaryLinear.GL (Vector (m + 1)) := b.equiv b (Equiv.swap i.castSucc i.succ)

private theorem swapCut_mem {m : ℕ} (b : Basis m) (cuts : Set (Fin m)) (i : Fin m) :
    swapCut b i ∈ cutStabilizer b cuts ↔ i ∉ cuts := by
  classical
  constructor
  · intro h hi
    have hv := ((mem_cutStabilizer b cuts _).mp h i hi (b i.castSucc)).mpr
      ((basis_mem_cutSpace b i _).mpr le_rfl)
    rw [swapCut, Module.Basis.equiv_apply, Equiv.swap_apply_left, basis_mem_cutSpace] at hv
    simp at hv
  · intro hi
    rw [mem_cutStabilizer_maps]
    intro j hj v hv
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hle : cutSpace b j ≤ (cutSpace b j).comap (swapCut b i).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      change swapCut b i (b k) ∈ cutSpace b j
      rw [swapCut, Module.Basis.equiv_apply, basis_mem_cutSpace]
      by_cases hki : k = i.castSucc
      · subst k
        rw [Equiv.swap_apply_left]
        simp only [Fin.val_succ]
        have : j.val ≠ i.val := fun h => hji (Fin.ext h)
        change i.val ≤ j.val at hk
        omega
      · by_cases hks : k = i.succ
        · subst k
          rw [Equiv.swap_apply_right]
          simp only [Fin.val_castSucc]
          change i.val + 1 ≤ j.val at hk
          omega
        · rw [Equiv.swap_apply_of_ne_of_ne hki hks]
          exact hk
    exact hle hv

private noncomputable def upper {m : ℕ} (b : Basis m) (i : Fin m) :
    BinaryLinear.GL (Vector (m + 1)) :=
  BinaryLinear.transvection (b i.castSucc) (b.coord i.succ) (by
    simp [Module.Basis.coord_apply, Fin.ext_iff])

private lemma upper_basis {m : ℕ} (b : Basis m) (i : Fin m) (k : Fin (m + 1)) :
    upper b i (b k) = if k = i.succ then b k + b i.castSucc else b k := by
  change b k + (b.coord i.succ (b k)) • b i.castSucc = _
  by_cases hk : k = i.succ
  · simp [hk, Module.Basis.coord_apply]
  · simp [Module.Basis.coord_apply, hk, Ne.symm hk]

private lemma upper_mem {m : ℕ} (b : Basis m) (i : Fin m) :
    upper b i ∈ cutStabilizer b Set.univ := by
  rw [mem_cutStabilizer_maps]
  intro j _ v hv
  have hle : cutSpace b j ≤ (cutSpace b j).comap (upper b i).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    change upper b i (b k) ∈ cutSpace b j
    rw [upper_basis]
    split_ifs with he
    · apply Submodule.add_mem
      · exact (basis_mem_cutSpace b j k).mpr hk
      · apply (basis_mem_cutSpace b j i.castSucc).mpr
        subst k
        change i.val + 1 ≤ j.val at hk
        change i.val ≤ j.val
        omega
    · exact (basis_mem_cutSpace b j k).mpr hk
  exact hle hv

private lemma cubic_order {m : ℕ} (b : Basis m) (i : Fin m) :
    orderOf (upper b i * swapCut b i) = 3 := by
  let c := upper b i * swapCut b i
  have hi : i.castSucc ≠ i.succ := by simp [Fin.ext_iff]
  have hc (k : Fin (m + 1)) : c (b k) =
      if k = i.castSucc then b i.succ + b i.castSucc
      else if k = i.succ then b i.castSucc else b k := by
    change upper b i (swapCut b i (b k)) = _
    rw [swapCut, Module.Basis.equiv_apply]
    by_cases hk : k = i.castSucc
    · subst k
      simp [upper_basis]
    · by_cases hks : k = i.succ
      · subst k
        simp [upper_basis, hi, hk]
      · simp [Equiv.swap_apply_of_ne_of_ne hk hks, upper_basis, hk, hks]
  have h0 : c (b i.castSucc) = b i.succ + b i.castSucc := by
    simpa using hc i.castSucc
  have h1 : c (b i.succ) = b i.castSucc := by
    simpa [hi.symm] using hc i.succ
  have h3 : c ^ 3 = 1 := by
    apply b.ext'
    intro k
    change c (c (c (b k))) = b k
    by_cases hk : k = i.castSucc
    · subst k
      simp only [h0, h1, map_add]
      ext r
      change (b i.succ r + b i.castSucc r) +
        (b i.castSucc r + (b i.succ r + b i.castSucc r)) = b i.castSucc r
      simp only [add_assoc, CharTwo.add_cancel_left]
    · by_cases hks : k = i.succ
      · subst k
        simp only [h0, h1, map_add]
        ext r
        change b i.castSucc r + (b i.succ r + b i.castSucc r) = b i.succ r
        rw [← add_assoc, add_comm (b i.castSucc r), CharTwo.add_cancel_right]
      · simp [hc, hk, hks]
  apply orderOf_eq_prime h3
  intro he
  have hh := congrArg (fun g : BinaryLinear.GL (Vector (m + 1)) => g (b i.succ)) he
  have heq : b i.castSucc = b i.succ := by simpa [hc, hi.symm] using hh
  exact hi (b.injective heq)

private theorem of_standard {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (h : ∀ K : Subgroup D, (S : Subgroup D) ≤ K → K = theta K ⊔ (S : Subgroup D)) :
    SylowThetaGeneration D := by
  intro P K hPK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D S P
  let e := MulAut.conj g
  have hmap : (S : Subgroup D).map e.toMonoidHom = (P : Subgroup D) := by
    change ((g • S : Sylow 2 D) : Subgroup D) = _
    rw [hg]
  have hP : (P : Subgroup D).map e.symm.toMonoidHom = (S : Subgroup D) := by
    exact (Subgroup.map_symm_eq_iff_map_eq (S : Subgroup D)
      (e := e) (H := (P : Subgroup D))).mpr hmap
  apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
  rw [Subgroup.map_sup, theta_map_of_injective _ e.symm.injective, hP]
  apply h
  rw [← hP]
  exact map_mono hPK

/-- Rank-one cubic elements recover all deleted nodes of a standard flag. -/
private theorem of_flags {m : ℕ} (b : Basis m)
    (S : Sylow 2 (BinaryLinear.GL (Vector (m + 1))))
    (hS : (S : Subgroup _) = cutStabilizer b Set.univ)
    (hflags : ∀ K : Subgroup (BinaryLinear.GL (Vector (m + 1))),
      cutStabilizer b Set.univ ≤ K → ∃ cuts, K = cutStabilizer b cuts) :
    SylowThetaGeneration (BinaryLinear.GL (Vector (m + 1))) := by
  let : Finite (BinaryLinear.GL (Vector (m + 1))) :=
    Finite.of_injective (fun g : BinaryLinear.GL (Vector (m + 1)) =>
      (g : Vector (m + 1) → Vector (m + 1))) DFunLike.coe_injective
  apply of_standard S
  intro K hSK
  rw [hS] at hSK ⊢
  let Q := theta K ⊔ cutStabilizer b Set.univ
  obtain ⟨s, hs⟩ := hflags K hSK
  obtain ⟨t, ht⟩ := hflags Q le_sup_right
  have hts : t ⊆ s := by
    intro i hi
    by_contra hn
    have hu : upper b i ∈ cutStabilizer b Set.univ := upper_mem b i
    have hw : swapCut b i ∈ K := hs.symm ▸ (swapCut_mem b s i).mpr hn
    have hc : upper b i * swapCut b i ∈ theta K :=
      subset_closure ⟨K.mul_mem (hSK hu) hw, cubic_order b i⟩
    have hwQ : swapCut b i ∈ Q :=
      (Q.mul_mem_cancel_left (mem_sup_right hu)).mp (mem_sup_left hc)
    exact (swapCut_mem b t i).mp (ht ▸ hwQ) hi
  exact le_antisymm (by
    change K ≤ Q
    rw [hs, ht]
    exact (cutStabilizer_le_iff b s t).mpr hts) (sup_le (theta_le K) hSK)

private noncomputable def threeSylow : Sylow 2 Matrix.PSL3Two.SL :=
  Sylow.ofCard Matrix.PSL3Two.borelSL (by
    rw [Matrix.PSL3Two.card_borelSL, Matrix.PSL3Two.card_SL]
    decide +kernel)

private theorem three_linear : SylowThetaGeneration Matrix.PSL3Two.SL := by
  apply of_standard threeSylow
  intro K hBK
  change K = theta K ⊔ Matrix.PSL3Two.borelSL
  change Matrix.PSL3Two.borelSL ≤ K at hBK
  let Q := theta K ⊔ Matrix.PSL3Two.borelSL
  have hcubic (x : Matrix.PSL3Two.SL) (hx : x ∈ K) (ho : orderOf x = 3) : x ∈ Q :=
    mem_sup_left (subset_closure ⟨hx, ho⟩)
  have hswap (i : Fin 8) (j : Fin 6) (hj : Matrix.PSL3Two.Bruhat.perm j ∈ K)
      (ho : orderOf (Matrix.PSL3Two.Bruhat.upper i * Matrix.PSL3Two.Bruhat.perm j) = 3) :
      Matrix.PSL3Two.Bruhat.perm j ∈ Q :=
    (Q.mul_mem_cancel_left (mem_sup_right (Matrix.PSL3Two.Bruhat.upper_mem i))).mp
      (hcubic _ (K.mul_mem (hBK (Matrix.PSL3Two.Bruhat.upper_mem i)) hj) ho)
  apply le_antisymm ?_ (sup_le (theta_le K) hBK)
  intro g hg
  obtain ⟨i, j, k, he⟩ := Matrix.PSL3Two.Bruhat.decomposition g
  have hj : Matrix.PSL3Two.Bruhat.perm j ∈ K := by
    rw [he] at hg
    exact (K.mul_mem_cancel_left (hBK (Matrix.PSL3Two.Bruhat.upper_mem i))).mp
      ((K.mul_mem_cancel_right (hBK (Matrix.PSL3Two.Bruhat.upper_mem k))).mp hg)
  have hw : Matrix.PSL3Two.Bruhat.perm j ∈ Q := by
    fin_cases j
    · have he : Matrix.PSL3Two.Bruhat.perm 0 = 1 := by decide +kernel
      exact he.symm ▸ Q.one_mem
    · apply hswap 4 1 hj
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    · apply hswap 1 2 hj
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    · apply hcubic _ hj
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    · apply hcubic _ hj
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    · apply hswap 2 5 hj
      exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  rw [he]
  exact Q.mul_mem (Q.mul_mem (mem_sup_right (Matrix.PSL3Two.Bruhat.upper_mem i)) hw)
    (mem_sup_right (Matrix.PSL3Two.Bruhat.upper_mem k))

private theorem four_linear : SylowThetaGeneration (BinaryLinear.GL (Vector 4)) := by
  apply of_flags Four.standardBasis Four.standardSylow rfl
  exact Four.standard_overgroups_of_bruhat Four.hasBruhatDecomposition

private theorem five_linear : SylowThetaGeneration (BinaryLinear.OuterCyclic.LinearGroup 5) := by
  apply of_flags BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardBasis
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.standardSylow rfl
  exact BinaryLinear.FiveFlagGeometry.SylowOvergroups.standard_overgroups_of_bruhat
    BinaryLinear.FiveFlagGeometry.SylowOvergroups.hasBruhatDecomposition

private instance linearFinite (n : ℕ) : Finite (BinaryLinear.OuterCyclic.LinearGroup n) :=
  Finite.of_injective (fun g : BinaryLinear.OuterCyclic.LinearGroup n =>
    (g : BinaryLinear.OuterCyclic.Space n → BinaryLinear.OuterCyclic.Space n))
    DFunLike.coe_injective

/-- Intrinsic generation in the actual central quotient PSL₃(2). -/
theorem three :
    SylowThetaGeneration (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
  three_linear.of_mulEquiv Matrix.PSL3Two.equiv.symm

/-- Intrinsic generation in the actual central quotient PSL₄(2). -/
theorem four :
    SylowThetaGeneration (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
  four_linear.of_mulEquiv (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide))

/-- Intrinsic generation in the actual central quotient PSL₅(2). -/
theorem five :
    SylowThetaGeneration (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
  five_linear.of_mulEquiv (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide))

/-- The complete binary linear branch of `MarkedSeed.generation_of_models`. -/
theorem binary_linear (n : ℕ) (lo : 3 ≤ n) (hi : n ≤ 5) :
    SylowThetaGeneration (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) := by
  rcases (show n = 3 ∨ n = 4 ∨ n = 5 by omega) with rfl | rfl | rfl
  · exact three
  · exact four
  · exact five

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.TerminalCases.MarkedSeed.LinearGeneration
