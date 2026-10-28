module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.FixedSpace
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryCore
public import Theory.Representation.BinaryPermutation

/-!
# Marked natural coordinates for the parabolic two-core

The genuine natural S₃-module is the augmentation kernel on three letters.
A surjective coordinate homomorphism with kernel E identifies S/E with a
sum of these modules. Equivariance uses literal conjugation in I₂; W/E
and X/E are the two specified coordinate lines. No center-image or
inverse-image assertion is included among the inputs.

Source: Aschbacher–Smith, Lemma 12.8.9(1–3), printed pp.852–853.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Coordinates on the actual S/E, retaining the actual S₃ quotient and
its conjugation action. The coordinate markings are choices of basis in
the natural factor, common to every summand, not hypotheses on Z(U). -/
structure ParabolicNaturalModule (F : InvariantFlag T V n) (L : Subgroup G)
    (g : G) (ι : Type*) [Fintype ι] where
  generation : F.U ⊔ conjugate F.U g = F.I₂ L
  core_eq : (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g
  E_commutator : ⁅F.E g, F.I₂ L⁆ = F.Vi 2
  quotient : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3)
  coordinates : ↥(F.W ⊔ F.X g) →* Multiplicative (ι → BinaryPermutation.core (Fin 3))
  onto : Function.Surjective coordinates
  kernel : coordinates.ker = (F.E g).subgroupOf (F.W ⊔ F.X g)
  equivariant : ∀ (i : F.I₂ L) (s t : ↥(F.W ⊔ F.X g)),
    (t : G) = (i : G) * s * (i : G)⁻¹ → ∀ j,
      Multiplicative.toAdd (coordinates t) j =
        BinaryPermutation.coreRepresentation (Fin 3)
          (quotient (QuotientGroup.mk' (pCore 2 (F.I₂ L)) i))
          (Multiplicative.toAdd (coordinates s) j)
  W_marking : ∀ s : ↥(F.W ⊔ F.X g),
    (s : G) ∈ F.W ↔ ∀ j, (Multiplicative.toAdd (coordinates s) j).val 0 = 0
  X_marking : ∀ s : ↥(F.W ⊔ F.X g),
    (s : G) ∈ F.X g ↔ ∀ j, (Multiplicative.toAdd (coordinates s) j).val 1 = 0
  U_marking : ∀ u : F.U, (u : G) ∉ F.W →
    quotient (QuotientGroup.mk' (pCore 2 (F.I₂ L))
      ⟨u, le_conjugateSpanBy F.U (F.P L) u.property⟩) = Equiv.swap 1 2

private theorem right_conjugate_mul (A : Subgroup G) (k h : G) :
    conjugate (conjugate A k) h = conjugate A (k * h) := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Replace g by an internal representative while preserving both marked
subgroups and the marked center. The original g is not assumed to lie in I₂. -/
theorem exists_internal_natural_representative (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
    (hPH : (F.P L).pCoreIn 2 ≤ F.H)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2) :
    ∃ h ∈ F.I₂ L, h ∉ F.H ∧ conjugate F.U h = conjugate F.U g ∧
      F.X h = F.X g ∧ conjugate F.ZU h = conjugate F.ZU g := by
  have hIP : F.I₂ L ≤ F.P L := le_sup_right.trans hfactor.ge
  have hnormal : normalizer (F.I₂ L : Set G) ≤
      normalizer ((F.I₂ L).pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L))
  have hPnormal : F.P L ≤ normalizer ((F.P L).pCoreIn 2 : Set G) :=
    (F.P L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (F.P L) (pCore 2 (F.P L)))
  have hgprod : g ∈ ((F.P L).pCoreIn 2 : Set G) * (F.I₂ L : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hIP.trans hPnormal), ← hfactor]
    exact hgP
  obtain ⟨k, hk, h, hh, rfl⟩ := hgprod
  have hkU : conjugate F.U k = F.U := (conjugate_eq_iff _ _).mpr
    (le_normalizer_conjugateSpanBy V F.H (hPH hk))
  have hconj : conjugate F.U h = conjugate F.U (k * h) := by
    rw [← right_conjugate_mul, hkU]
  have hkZ : conjugate F.ZU k = F.ZU := by
    change conjugate (centerIn F.U) k = centerIn F.U
    rw [← centerIn_conjugate, hkU]
  have hZ : conjugate F.ZU h = conjugate F.ZU (k * h) := by
    rw [← right_conjugate_mul, hkZ]
  have hUI : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  have hW : F.U ⊓ (F.I₂ L).pCoreIn 2 = F.W := by
    rw [← hcore, ← inf_assoc, inf_eq_left.mpr hUI]
    rfl
  have hSg : conjugate ((F.I₂ L).pCoreIn 2) (k * h) = (F.I₂ L).pCoreIn 2 :=
    (conjugate_eq_iff _ _).mpr
      (hnormal (le_normalizer_conjugateSpanBy F.U (F.P L) hgP))
  have hSh : conjugate ((F.I₂ L).pCoreIn 2) h = (F.I₂ L).pCoreIn 2 :=
    (conjugate_eq_iff _ _).mpr (hnormal ((F.I₂ L).le_normalizer hh))
  have hX : F.X h = F.X (k * h) := by
    change conjugate F.W h = conjugate F.W (k * h)
    rw [← hW, conjugate_inf, conjugate_inf, hSh, hSg, hconj]
  exact ⟨h, hh, fun hH => hgH (F.H.mul_mem (hPH hk) hH), hconj, hX, hZ⟩

namespace ParabolicNaturalModule
variable {F : InvariantFlag T V n} {L : Subgroup G} {g : G} {ι : Type*} [Fintype ι]

/-- The coordinate witness induces an actual isomorphism on the literal
section, rather than merely labelling that section as natural. -/
noncomputable def sectionEquiv (M : F.ParabolicNaturalModule L g ι)
    [((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal] :
    (↥(F.W ⊔ F.X g) ⧸ (F.E g).subgroupOf (F.W ⊔ F.X g)) ≃*
      Multiplicative (ι → BinaryPermutation.core (Fin 3)) :=
  (QuotientGroup.quotientMulEquivOfEq M.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective M.coordinates M.onto)

/-- The four-vector calculation in a single genuine natural summand.
It is independent of the multiplicity and of every group-theoretic center. -/
theorem natural_coordinate_calculation (p : Equiv.Perm (Fin 3))
    (v : BinaryPermutation.core (Fin 3)) (hW : v.val 0 = 0)
    (hX : (BinaryPermutation.coreRepresentation (Fin 3) p v).val 1 = 0) :
    BinaryPermutation.coreRepresentation (Fin 3) p v -
      BinaryPermutation.coreRepresentation (Fin 3) (Equiv.swap 1 2)
        (BinaryPermutation.coreRepresentation (Fin 3) p v) = v := by
  have hcalc : ∀ (p : Equiv.Perm (Fin 3)) (v : Fin 3 → ZMod 2),
      (∑ i, v i) = 0 → v 0 = 0 → v (p.symm 1) = 0 →
      (fun a => v (p.symm a) - v (p.symm ((Equiv.swap (1 : Fin 3) 2).symm a))) = v := by
    decide
  apply Subtype.ext
  exact hcalc p v.val v.property hW hX

/-- Multiplication modulo the coordinate kernel is the literal equivalence
modulo E; no quotient of the ambient group G is used. -/
theorem coordinates_eq_iff (M : F.ParabolicNaturalModule L g ι)
    (s t : ↥(F.W ⊔ F.X g)) :
    M.coordinates s = M.coordinates t ↔ (t : G)⁻¹ * s ∈ F.E g := by
  rw [MonoidHom.eq_iff, M.kernel]
  rfl

/-- I₂ normalizes the actual two-core S = W X. -/
theorem core_normalized (M : F.ParabolicNaturalModule L g ι) :
    F.I₂ L ≤ normalizer ((F.W ⊔ F.X g : Subgroup G) : Set G) := by
  rw [← M.core_eq]
  exact (F.I₂ L).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (F.I₂ L) (pCore 2 (F.I₂ L)))

/-- In the chosen coordinates the literal group commutator [x,u] is the
natural-module displacement x - u(x). -/
theorem commutator_coordinates (M : F.ParabolicNaturalModule L g ι)
    (u : F.U) (hu : (u : G) ∉ F.W) (x c : ↥(F.W ⊔ F.X g))
    (hc : (c : G) = ⁅(x : G), (u : G)⁆) (j : ι) :
    Multiplicative.toAdd (M.coordinates c) j =
      Multiplicative.toAdd (M.coordinates x) j -
        BinaryPermutation.coreRepresentation (Fin 3) (Equiv.swap 1 2)
          (Multiplicative.toAdd (M.coordinates x) j) := by
  let ui : F.I₂ L := ⟨u, le_conjugateSpanBy F.U (F.P L) u.property⟩
  let y : ↥(F.W ⊔ F.X g) := ⟨(u : G) * x * (u : G)⁻¹,
    (mem_normalizer_iff.mp (M.core_normalized ui.property) (x : G)).mp x.property⟩
  have he : c = x * y⁻¹ := by
    apply Subtype.ext
    dsimp [y]
    rw [hc, commutatorElement_def]
    group
  have hy := M.equivariant ui x y rfl j
  rw [M.U_marking u hu] at hy
  rw [he, map_mul, map_inv]
  simp only [toAdd_mul, toAdd_inv,
    Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
  rw [hy]

/-- The fixed-space calculation in a single natural summand. -/
theorem natural_displacement_eq_zero_iff (v : BinaryPermutation.core (Fin 3)) :
    v - BinaryPermutation.coreRepresentation (Fin 3) (Equiv.swap 1 2) v = 0 ↔
      v.val 0 = 0 := by
  have hcalc : ∀ (v : Fin 3 → ZMod 2), (∑ i, v i) = 0 →
      ((fun a => v a - v ((Equiv.swap (1 : Fin 3) 2).symm a)) = 0 ↔ v 0 = 0) := by
    decide
  exact (Subtype.ext_iff).trans (hcalc v.val v.property)

/-- The fixed space in S/E is exactly W/E, stated with the actual ambient
commutator and the coordinate kernel E. This feeds the published kernel lemma. -/
theorem commutator_mem_E_iff (M : F.ParabolicNaturalModule L g ι)
    (u : F.U) (hu : (u : G) ∉ F.W) (x c : ↥(F.W ⊔ F.X g))
    (hc : (c : G) = ⁅(x : G), (u : G)⁆) :
    ⁅(x : G), (u : G)⁆ ∈ F.E g ↔ (x : G) ∈ F.W := by
  have hker : (c : G) ∈ F.E g ↔ M.coordinates c = 1 := by
    change c ∈ (F.E g).subgroupOf (F.W ⊔ F.X g) ↔ _
    rw [← M.kernel]
    rfl
  rw [← hc, hker, M.W_marking]
  constructor
  · intro he j
    apply (natural_displacement_eq_zero_iff _).mp
    rw [← M.commutator_coordinates u hu x c hc j, he]
    rfl
  · intro he
    apply Multiplicative.toAdd.injective
    funext j
    change Multiplicative.toAdd (M.coordinates c) j = 0
    rw [M.commutator_coordinates u hu x c hc j]
    exact (natural_displacement_eq_zero_iff _).mpr (he j)

/-- Abelianity of the literal section follows from its coordinate embedding. -/
theorem commutator_core_le (M : F.ParabolicNaturalModule L g ι) :
    ⁅F.W ⊔ F.X g, F.W ⊔ F.X g⁆ ≤ F.E g := by
  apply commutator_le.mpr
  intro a ha b hb
  have he : ⁅(⟨a, ha⟩ : ↥(F.W ⊔ F.X g)), ⟨b, hb⟩⁆ ∈ M.coordinates.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [M.kernel] at he
  exact he

/-- The coordinate calculation recovers each z ∈ Z(U) after conjugation
and displacement. The internal representative is required to preserve the
actual displaced center, not only X. -/
theorem displaced_center_coordinates (M : F.ParabolicNaturalModule L g ι)
    (h : G) (hh : h ∈ F.I₂ L) (hZ : conjugate F.ZU h = conjugate F.ZU g)
    (u : F.U) (hu : (u : G) ∉ F.W) (z : F.ZU)
    (c : ↥(F.W ⊔ F.X g)) (hc : (c : G) = ⁅h⁻¹ * z * h, (u : G)⁆) :
    M.coordinates c = M.coordinates
      ⟨z, (le_sup_left : F.W ≤ F.W ⊔ F.X g) (F.ZU_le_W z.property)⟩ := by
  let zs : ↥(F.W ⊔ F.X g) :=
    ⟨z, (le_sup_left : F.W ≤ F.W ⊔ F.X g) (F.ZU_le_W z.property)⟩
  have hzX : h⁻¹ * z * h ∈ F.X g := by
    apply F.conjugate_ZU_le_X g
    rw [← hZ]
    exact ⟨z, z.property, by simp⟩
  let x : ↥(F.W ⊔ F.X g) := ⟨h⁻¹ * z * h, (le_sup_right : F.X g ≤ F.W ⊔ F.X g) hzX⟩
  let hi : F.I₂ L := ⟨h, hh⟩
  apply Multiplicative.toAdd.injective
  funext j
  have hx := M.equivariant hi⁻¹ zs x (by simp [x, hi, zs]) j
  have hW := (M.W_marking zs).mp (F.ZU_le_W z.property) j
  have hX := (M.X_marking x).mp hzX j
  rw [hx] at hX
  rw [M.commutator_coordinates u hu x c hc j, hx]
  exact natural_coordinate_calculation _ _ hW hX

end ParabolicNaturalModule
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
