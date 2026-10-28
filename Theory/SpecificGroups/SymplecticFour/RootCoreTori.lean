module

public import Theory.SpecificGroups.SymplecticFour.RootCoreTori.Quotients
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual

import Mathlib.Tactic.FinCases

/-!
# Compatible scalar complements for symplectic root normalizers

Over a finite field of characteristic two and order greater than two, each
of the eight original matrix root groups has a centralizer complement whose
image in the normalizer modulo its intrinsic two-core is central. The
preimage of this quotient center meets the root centralizer only in the core.

For the standard long root we use `diagonalTorus s 1`; for the standard
short root we use `diagonalTorus s s`. Both act on their root parameter by
squaring. This weight is bijective in the finite field, so the scalar torus
realizes every normalizer action and meets the centralizer trivially.
`Quotients` proves centrality and separation using the actual point and plane
Levi actions. Explicit Weyl conjugation transports all four clauses to every
root, including the intrinsic core and the embedded quotient-center preimage.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
symplectic case of E.6.11(3c), printed pp.249–250 (PDF pp.260–261),
and the compatible commutator bound in E.6.25, printed p.255 (PDF p.266).
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.RootCoreTori
open RootNormalizerResidual
variable {F : Type*} [Field F]

private noncomputable def planeParameter : Fˣ →* Sp F where
  toFun s := diagonalTorus s s
  map_one' := by
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> simp [diagonalTorus, Matrix.diagonal]
  map_mul' s t := by
    apply Subtype.ext
    change (diagonalTorus (s * t) (s * t)).val =
      (diagonalTorus s s).val * (diagonalTorus t t).val
    simp only [diagonalTorus, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [mul_comm]

variable [CharP F 2]

private theorem planeParameter_conjugate (s : Fˣ) (t : F) :
    planeParameter s * rootElement 4 t * (planeParameter s)⁻¹ =
      rootElement 4 ((s : F) ^ 2 * t) := by
  change diagonalTorus s s * rootElement 4 t * (diagonalTorus s s)⁻¹ = _
  rw [plane_conjugate _ (diagonalTorus_mem_borel s s).2]
  congr 1
  simp [diagonalTorus, Matrix.diagonal, pow_two]

private theorem planeParameter_normalizes :
    (planeParameter (F := F)).range ≤
      normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) := by
  rw [normalizer_four_eq]
  rintro _ ⟨s, rfl⟩
  exact (diagonalTorus_mem_borel s s).2

variable [Finite F]

private theorem plane_complement_sup :
    centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ⊔ planeParameter.range =
      normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) := by
  apply le_antisymm (sup_le (centralizer_le_normalizer _) planeParameter_normalizes)
  intro g hg
  obtain ⟨c, hc⟩ := RootTori.normalizer_scalar 4 g hg
  obtain ⟨s, hs⟩ := RootTori.weight_surjective (F := F) 0 c
  have hs' : (s : F) ^ 2 = (c : F) := congrArg Units.val hs
  have he (t : F) :
      g * rootElement 4 t * g⁻¹ =
        planeParameter s * rootElement 4 t * (planeParameter s)⁻¹ := by
    rw [hc, planeParameter_conjugate, hs']
  have hz : (planeParameter s)⁻¹ * g ∈
      centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff 4 x).mp hx
    have h := congrArg (fun z : Sp F => (planeParameter s)⁻¹ * z * g) (he t)
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h.symm
  have hy : planeParameter s ∈ (planeParameter (F := F)).range := ⟨s, rfl⟩
  have hh := (centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ⊔
    planeParameter.range).mul_mem (mem_sup_right hy) (mem_sup_left hz)
  simpa only [mul_inv_cancel_left] using hh

omit [Finite F] in
private theorem plane_complement_inf :
    centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ⊓ planeParameter.range = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hc, s, rfl⟩
  change planeParameter s = 1
  have hh := mem_centralizer_iff.mp hc (rootElement 4 1)
    ((RootSubgroup.mem_group_iff 4 _).mpr ⟨1, rfl⟩)
  have hconj : planeParameter s * rootElement 4 1 * (planeParameter s)⁻¹ =
      rootElement 4 1 := by
    rw [← hh]
    simp
  rw [planeParameter_conjugate, mul_one] at hconj
  have hs : s = 1 := by
    apply Units.ext
    exact CharTwo.sq_injective (by simpa using RootSubgroup.element_injective 4 hconj)
  rw [hs, map_one]

private theorem point_complement {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ∃ Z : Subgroup (Sp F),
      centralizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) ⊔ Z =
        normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) ∧
      centralizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) ⊓ Z = ⊥ ∧
      Z ≤ (normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F))).coreCenterIn 2 ∧
      (normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F))).coreCenterIn 2 ⊓
        centralizer (RootSubgroup.group (F := F) 0 : Set (Sp F)) ≤
          (normalizer (RootSubgroup.group (F := F) 0 : Set (Sp F))).pCoreIn 2 := by
  refine ⟨RootTori.torus 0, RootTori.centralizer_sup_torus 0,
    RootTori.centralizer_inf_torus 0, ?_, ?_⟩
  · rw [normalizer_zero_eq]
    rintro _ ⟨s, rfl⟩
    exact point_scalar_mem_coreCenter hcard hn s
  · rw [normalizer_zero_eq, centralizer_zero_eq]
    exact point_separation hcard hn

private theorem plane_complement {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    ∃ Z : Subgroup (Sp F),
      centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ⊔ Z =
        normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ∧
      centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ⊓ Z = ⊥ ∧
      Z ≤ (normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F))).coreCenterIn 2 ∧
      (normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F))).coreCenterIn 2 ⊓
        centralizer (RootSubgroup.group (F := F) 4 : Set (Sp F)) ≤
          (normalizer (RootSubgroup.group (F := F) 4 : Set (Sp F))).pCoreIn 2 := by
  refine ⟨planeParameter.range, plane_complement_sup, plane_complement_inf, ?_, ?_⟩
  · rw [normalizer_four_eq]
    rintro _ ⟨s, rfl⟩
    exact plane_scalar_mem_coreCenter hcard hn s
  · rw [normalizer_four_eq, centralizer_four_eq]
    exact plane_separation hcard hn

private theorem centralizer_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (R : Subgroup G) :
    (centralizer (R : Set G)).map e.toMonoidHom =
      centralizer (R.map e.toMonoidHom : Set H) := by
  ext b
  simp only [mem_map_equiv, mem_centralizer_iff]
  constructor
  · intro h a ha
    apply e.symm.injective
    simpa only [map_mul] using h (e.symm a) (mem_map_equiv.mp ha)
  · intro h a ha
    have he := h (e a) (by simpa)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm he

private theorem complement_map {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (R : Subgroup G)
    (h : ∃ Z : Subgroup G,
      centralizer (R : Set G) ⊔ Z = normalizer (R : Set G) ∧
      centralizer (R : Set G) ⊓ Z = ⊥ ∧
      Z ≤ (normalizer (R : Set G)).coreCenterIn 2 ∧
      (normalizer (R : Set G)).coreCenterIn 2 ⊓ centralizer (R : Set G) ≤
        (normalizer (R : Set G)).pCoreIn 2) :
    ∃ Z : Subgroup H,
      centralizer (R.map e.toMonoidHom : Set H) ⊔ Z =
        normalizer (R.map e.toMonoidHom : Set H) ∧
      centralizer (R.map e.toMonoidHom : Set H) ⊓ Z = ⊥ ∧
      Z ≤ (normalizer (R.map e.toMonoidHom : Set H)).coreCenterIn 2 ∧
      (normalizer (R.map e.toMonoidHom : Set H)).coreCenterIn 2 ⊓
        centralizer (R.map e.toMonoidHom : Set H) ≤
          (normalizer (R.map e.toMonoidHom : Set H)).pCoreIn 2 := by
  obtain ⟨Z, hsup, hinf, hc, hs⟩ := h
  refine ⟨Z.map e.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · have hm := congrArg (Subgroup.map e.toMonoidHom) hsup
    rwa [Subgroup.map_sup, centralizer_map, map_equiv_normalizer_eq] at hm
  · have hm := congrArg (Subgroup.map e.toMonoidHom) hinf
    rwa [map_inf _ _ _ e.injective, centralizer_map, Subgroup.map_bot] at hm
  · have hm := map_mono (f := e.toMonoidHom) hc
    rwa [map_coreCenterIn_of_injective _ _ _ e.injective, map_equiv_normalizer_eq] at hm
  · have hm := map_mono (f := e.toMonoidHom) hs
    rwa [map_inf _ _ _ e.injective, map_coreCenterIn_of_injective _ _ _ e.injective,
      map_pCoreIn_of_injective _ _ _ e.injective, centralizer_map,
      map_equiv_normalizer_eq] at hm

/-- Every symplectic root normalizer has a root-centralizer complement central
modulo its intrinsic two-core; that quotient center meets the root centralizer
only in the two-core. -/
theorem exists_core_central_complement {n : ℕ}
    (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) (r : Fin 8) :
    let R := RootSubgroup.group (F := F) r
    let N := normalizer (R : Set (Sp F))
    let C := centralizer (R : Set (Sp F))
    ∃ Z : Subgroup (Sp F), C ⊔ Z = N ∧ C ⊓ Z = ⊥ ∧
      Z ≤ N.coreCenterIn 2 ∧ N.coreCenterIn 2 ⊓ C ≤ N.pCoreIn 2 := by
  dsimp only
  obtain ⟨w, he⟩ := exists_root_conjugation (F := F) r
  split_ifs at he
  · rw [← he]
    exact complement_map (MulAut.conj w) _ (point_complement hcard hn)
  · rw [← he]
    exact complement_map (MulAut.conj w) _ (plane_complement hcard hn)

end Theory.SpecificGroups.SymplecticFour.RootCoreTori
