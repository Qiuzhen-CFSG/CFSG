module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.NormNum

/-!
# Conjugate joins in S₅ × C₂

A subgroup of a Sylow two-subgroup with even first projection of order
four lies in V₄ × C₂. If it is outside the zero graph, an actual conjugate
inside that even subgroup generates the whole even part together with it.
The full even subgroup uses the identity conjugator. For the remaining
subgroups a cubic permutation in the S₄ normalizer rotates the three
nonzero graphs V₄ → C₂. A small kernel-checked certificate on the eight
even elements proves the required product decomposition; it never enumerates
subsets of the ambient group of order 240.

The standard D₈ coordinates follow `SymmetricFive.LocalTwoCore`. Sylow
conjugacy and a genuine isomorphism of order-two groups transport the result,
preserving the literal first projection, parity, and zero graph.

This finite calculation supplies the characteristic-five local input in
Aschbacher--Smith E.1.5, E.1.8 and E.1.14(6), printed pp.210--214,
citing Aschbacher (1982), Lemma 4.10. It does not assert the full source theorem.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymmetricFive.LocalGraphSpreading
private abbrev C := Multiplicative (ZMod 2)
private abbrev V := C × C
private abbrev E := V × C
private abbrev D := Equiv.Perm (Fin 5)
private def a : D := Equiv.swap 0 1
private def b : D := Equiv.swap 2 3
private def c : D := Equiv.swap 0 2 * Equiv.swap 1 3
private def word : Fin 8 → D := ![1, a, b, a * b, c, a * c, b * c, a * b * c]
private def eight : Subgroup D where
  carrier := Set.range word
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    have hc : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hc i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    have hc : ∀ i, ∃ j, (word i)⁻¹ = word j := by decide +kernel
    rintro x ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hc i
    exact ⟨j, hj.symm⟩

private theorem eight_card : Nat.card eight = 8 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 8
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp

private noncomputable def standardSylow : Sylow 2 (D × C) := Sylow.ofCard (eight.prod ⊤) (by
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    eight_card, Subgroup.card_top, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial,
    Nat.factorization_mul, Nat.factorization_pow]
  decide +kernel)

private def vw (x : V) : D := (if x.1 = 1 then 1 else a * b) * (if x.2 = 1 then 1 else c)
private def ew (x : E) : D × C := (vw x.1, x.2)
private def cyc : D := Equiv.swap 0 1 * Equiv.swap 1 2
private def act (x : E) : E := ((x.1.1 * x.1.2, x.1.1), x.2)
private def vh : V →* D where
  toFun := vw
  map_one' := by decide +kernel
  map_mul' := by decide +kernel
private def eh : E →* D × C := vh.prodMap (MonoidHom.id _)

private theorem conj_word : ∀ i, ew (act i) = (cyc, 1) * ew i * (cyc, 1)⁻¹ := by decide +kernel

-- The decision instance is large because of the nested finite quantifiers;
-- the kernel calculation still ranges over only 256 subsets of eight elements.
set_option synthInstance.maxSize 512 in
private theorem graph_certificate : ∀ s : E → Bool, s 1 = true →
    (∀ i j, s i = true → s j = true → s (i * j) = true) →
    (∀ i : V, ∃ z, s (i, z) = true) →
    (∃ i, s i = true ∧ i.2 ≠ 1) →
    ∀ k, ∃ i j, s i = true ∧ s j = true ∧ i * act j = k := by
  decide +kernel

private theorem vw_injective : Function.Injective vw := by decide +kernel
private theorem vw_mem_eight : ∀ x : V, ∃ i, vw x = word i := by decide +kernel
private theorem even_word : ∀ i, (word i).sign = 1 → ∃ x : V, vw x = word i := by
  decide +kernel

private theorem four_card : Nat.card vh.range = 4 := by
  change Nat.card (Set.range vw) = 4
  rw [← Nat.card_congr (Equiv.ofInjective _ vw_injective)]
  simp [V, C, Nat.card_eq_fintype_card]

private theorem ew_mem_standard (x : E) : ew x ∈ eight.prod (⊤ : Subgroup C) := by
  obtain ⟨i, hi⟩ := vw_mem_eight x.1
  exact ⟨⟨i, hi.symm⟩, trivial⟩

private theorem even_mem_range (x : D × C) (hx : x ∈ eight.prod (⊤ : Subgroup C))
    (he : x.1 ∈ alternatingGroup (Fin 5)) : ∃ k : E, ew k = x := by
  obtain ⟨i, hi⟩ := hx.1
  obtain ⟨v, hv⟩ := even_word i (by
    rw [hi]
    exact Equiv.Perm.mem_alternatingGroup.mp he)
  exact ⟨(v, x.2), Prod.ext (hv.trans hi) rfl⟩

private theorem standard_spreading (B : Subgroup (D × C))
    (hB : B ≤ eight.prod ⊤)
    (hc : Nat.card (B.map (MonoidHom.fst _ _)) = 4)
    (he : B.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5))
    (hn : ¬ B ≤ (alternatingGroup (Fin 5)).prod ⊥) :
    ∃ g : D × C,
      B.map (MulAut.conj g).toMonoidHom ≤ eight.prod ⊤ ∧
      eight.prod ⊤ ⊓ (alternatingGroup (Fin 5)).prod ⊤ ≤
        B ⊔ B.map (MulAut.conj g).toMonoidHom := by
  classical
  by_cases hfull : eight.prod ⊤ ⊓ (alternatingGroup (Fin 5)).prod ⊤ ≤ B
  · refine ⟨1, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      simpa using hB hx
    · exact hfull.trans le_sup_left
  have hproj : B.map (MonoidHom.fst _ _) = vh.range := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := even_mem_range x (hB hx) (he ⟨x, hx, rfl⟩)
      exact ⟨k.1, congrArg Prod.fst hk⟩
    · rw [hc, four_card]
  let s : E → Bool := fun k => decide (ew k ∈ B)
  have hs (k : E) : s k = true ↔ ew k ∈ B := by simp [s]
  have hone : s 1 = true := (hs 1).mpr (by
    change eh 1 ∈ B
    rw [map_one]
    exact B.one_mem)
  have hmul : ∀ i j, s i = true → s j = true → s (i * j) = true := by
    intro i j hi hj
    apply (hs _).mpr
    change eh (i * j) ∈ B
    rw [map_mul]
    exact B.mul_mem ((hs _).mp hi) ((hs _).mp hj)
  have honto : ∀ i : V, ∃ z, s (i, z) = true := by
    intro i
    have hi : vw i ∈ B.map (MonoidHom.fst _ _) := by
      rw [hproj]
      exact ⟨i, rfl⟩
    obtain ⟨y, hy, hiy⟩ := hi
    refine ⟨y.2, (hs _).mpr ?_⟩
    have hyw : ew (i, y.2) = y := Prod.ext hiy.symm rfl
    rwa [hyw]
  have hnonzero : ∃ i, s i = true ∧ i.2 ≠ 1 := by
    by_contra! hz
    apply hn
    intro y hy
    have hey := he (mem_map_of_mem (MonoidHom.fst _ _) hy)
    obtain ⟨k, hk⟩ := even_mem_range y (hB hy) hey
    refine ⟨hey, ?_⟩
    have hz' := hz k ((hs _).mpr (hk.symm ▸ hy))
    exact (congrArg Prod.snd hk).symm.trans hz'
  refine ⟨(cyc, 1), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, rfl⟩ := even_mem_range x (hB hx) (he ⟨x, hx, rfl⟩)
    change (cyc, 1) * ew k * (cyc, 1)⁻¹ ∈ _
    rw [← conj_word]
    exact ew_mem_standard _
  · rintro x ⟨hxP,hxe⟩
    obtain ⟨k, rfl⟩ := even_mem_range x hxP hxe.1
    obtain ⟨i, j, hi, hj, hk⟩ := graph_certificate s hone hmul honto hnonzero k
    rw [← hk]
    change eh (i * act j) ∈ _
    rw [map_mul]
    apply Subgroup.mul_mem
    · exact (le_sup_left : B ≤ B ⊔ B.map (MulAut.conj (cyc, 1)).toMonoidHom) ((hs _).mp hi)
    · apply (le_sup_right : B.map (MulAut.conj (cyc, 1)).toMonoidHom ≤
        B ⊔ B.map (MulAut.conj (cyc, 1)).toMonoidHom)
      exact ⟨ew j, (hs _).mp hj, (conj_word j).symm⟩
private def Spreading {Z : Type*} [Group Z] (P : Subgroup (D × Z)) : Prop :=
  ∀ (B : Subgroup (D × Z)), B ≤ P →
    Nat.card (B.map (MonoidHom.fst _ _)) = 4 →
    B.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5) →
    ¬ B ≤ (alternatingGroup (Fin 5)).prod ⊥ →
    ∃ g : Equiv.Perm (Fin 5) × Z, B.map (MulAut.conj g).toMonoidHom ≤ P ∧
      P ⊓ (alternatingGroup (Fin 5)).prod ⊤ ≤
        B ⊔ B.map (MulAut.conj g).toMonoidHom

private theorem transport {Z W : Type*} [Group Z] [Group W]
    (P : Subgroup (D × Z)) (Q : Subgroup (D × W))
    (e : D × Z ≃* D × W) (d : D ≃* D)
    (hP : P.map e.toMonoidHom = Q)
    (hf : ∀ x, (e x).1 = d x.1)
    (ha : ∀ x, d x ∈ alternatingGroup (Fin 5) ↔ x ∈ alternatingGroup (Fin 5))
    (hz : ∀ x, (e x).2 = 1 ↔ x.2 = 1)
    (hQ : Spreading Q) : Spreading P := by
  intro B hB hc he hn
  let B' := B.map e.toMonoidHom
  have hfirst : B'.map (MonoidHom.fst _ _) =
      (B.map (MonoidHom.fst _ _)).map d.toMonoidHom := by
    change (B.map e.toMonoidHom).map _ = _
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hf
  have hBP : B' ≤ Q := hP ▸ map_mono hB
  have hcard : Nat.card (B'.map (MonoidHom.fst _ _)) = 4 := by
    rw [hfirst, Subgroup.card_map_of_injective d.injective, hc]
  have he' : B'.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5) := by
    rw [hfirst]
    rintro _ ⟨x, hx, rfl⟩
    exact (ha x).mpr (he hx)
  have hn' : ¬ B' ≤ (alternatingGroup (Fin 5)).prod ⊥ := by
    intro h
    apply hn
    intro x hx
    have hx' := h (mem_map_of_mem e.toMonoidHom hx)
    refine ⟨(ha _).mp ?_, (hz x).mp hx'.2⟩
    rw [← hf]
    exact hx'.1
  obtain ⟨g, hgP, hgjoin⟩ := hQ B' hBP hcard he' hn'
  let t := e.symm g
  have hconj (x : D × Z) : e (t * x * t⁻¹) = g * e x * g⁻¹ := by
    simp only [map_mul, map_inv, t, e.apply_symm_apply]
  refine ⟨t, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := hgP (show g * e x * g⁻¹ ∈ B'.map (MulAut.conj g).toMonoidHom from
      ⟨e x, mem_map_of_mem e.toMonoidHom hx, rfl⟩)
    rw [← hP, ← hconj, Subgroup.mem_map_equiv] at hx'
    change t * x * t⁻¹ ∈ P
    simpa only [e.symm_apply_apply] using hx'
  · intro x hx
    have hex : e x ∈ Q ⊓ (alternatingGroup (Fin 5)).prod ⊤ := by
      refine ⟨?_, ?_, trivial⟩
      · rw [← hP]
        exact mem_map_of_mem e.toMonoidHom hx.1
      · rw [hf]
        exact (ha _).mpr hx.2.1
    have hj : B' ⊔ B'.map (MulAut.conj g).toMonoidHom ≤
        (B ⊔ B.map (MulAut.conj t).toMonoidHom).map e.toMonoidHom := by
      apply sup_le
      · exact map_mono le_sup_left
      · rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨t * z * t⁻¹, (le_sup_right : B.map (MulAut.conj t).toMonoidHom ≤
          B ⊔ B.map (MulAut.conj t).toMonoidHom) (show t * z * t⁻¹ ∈
          B.map (MulAut.conj t).toMonoidHom from ⟨z, hz, rfl⟩), hconj z⟩
    have hx' := hj (hgjoin hex)
    rw [Subgroup.mem_map_equiv] at hx'
    simpa only [e.symm_apply_apply] using hx'

private theorem conjugation_even (g x : D) :
    g * x * g⁻¹ ∈ alternatingGroup (Fin 5) ↔ x ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv,
    mul_comm (Equiv.Perm.sign g) (Equiv.Perm.sign x), mul_inv_cancel_right]

private theorem concrete_spreading (P : Sylow 2 (D × C)) :
    Spreading (P : Subgroup (D × C)) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (D × C) P standardSylow
  have hmap : (P : Subgroup _).map (MulAut.conj g).toMonoidHom =
      (standardSylow : Subgroup _) := by
    have h := congrArg (fun Q : Sylow 2 (D × C) => (Q : Subgroup (D × C))) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  apply transport (P : Subgroup _) (standardSylow : Subgroup _)
    (MulAut.conj g) (MulAut.conj g.1) hmap (fun _ => rfl)
    (fun x => conjugation_even g.1 x)
  · intro x
    change g.2 * x.2 * g.2⁻¹ = 1 ↔ x.2 = 1
    exact (MulAut.conj g.2).map_eq_one_iff
  · exact standard_spreading

/-- In S₅ times any group of order two, every subgroup with even
four-element first projection and nontrivial second projection has a
conjugate in the same Sylow subgroup which generates its even part. -/
theorem spreading_of_card_two (Z : Type*) [Group Z] (hZ : Nat.card Z = 2)
    (P : Sylow 2 (Equiv.Perm (Fin 5) × Z)) (B : Subgroup (Equiv.Perm (Fin 5) × Z))
    (hB : B ≤ (P : Subgroup _))
    (hc : Nat.card (B.map (MonoidHom.fst _ _)) = 4)
    (he : B.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 5))
    (hn : ¬ B ≤ (alternatingGroup (Fin 5)).prod ⊥) :
    ∃ g : Equiv.Perm (Fin 5) × Z,
      B.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup _) ∧
      (P : Subgroup _) ⊓ (alternatingGroup (Fin 5)).prod ⊤ ≤
        B ⊔ B.map (MulAut.conj g).toMonoidHom := by
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; decide)
  let z : Z ≃* C := mulEquivOfPrimeCardEq hZ (by
    simp [C, Nat.card_eq_fintype_card])
  let e := MulEquiv.prodCongr (MulEquiv.refl D) z
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : Spreading (P : Subgroup (Equiv.Perm (Fin 5) × Z)) := by
    apply transport (P : Subgroup _) (Q : Subgroup _) e (MulEquiv.refl D)
      rfl (fun _ => rfl) (fun _ => Iff.rfl)
    · intro x
      exact z.map_eq_one_iff
    · exact concrete_spreading Q
  exact hQ B hB hc he hn
end Theory.SpecificGroups.SymmetricFive.LocalGraphSpreading
