module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.TensorModels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.FullOrbit.Coordinates
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.FullOrbit.FieldSum
public import Theory.Representation.PGroupRegularOrbit
/-!
# The full symplectic tensor has a regular Sylow orbit

For the tensor of all `2*n` graph twists, the highest coefficient of the
unipotent orbit sum of the lowest vector is one. The finite-p-group
regular-orbit argument therefore makes this orbit a basis: both the orbit
and the tensor have dimension `q^4`. Its fixed line is the marked highest
line, and its orbit sum is precisely the highest vector.

A nonzero subrepresentation contains a nonzero Sylow-fixed vector. It then
contains the highest vector, its block-exchange image (the lowest vector),
and the entire orbit basis. This proves irreducibility over any field
admitting the given coefficient embedding, without algebraic closedness.

The acting map is the actual matrix Sylow inclusion followed by the inverse
of the derived/full equivalence. This proves the full-tensor prerequisite
for GLS3, 2.8.6(a), 2.8.10(d), `refs/KGroup/GLS3/chapter2.tex`, used on
printed pp.356–357 of `refs/quasithin.pdf`. The remaining subsets and their
inequivalence are assembled by the tensor-family consumer.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Representation
set_option linter.unusedSimpArgs false
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.FullOrbit
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local instance : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
local notation "a" => (Sum.inl (0 : Fin 2) : Coordinate)
variable {E : Type*} [Field E]

noncomputable local instance : Fintype (unipotent (F := F)) := Fintype.ofFinite _

lemma norm_highest_coefficient (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) :
    (∑ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) (lowest n))
      (fun _ => a) = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let κ : (F × F × F × F) ≃ unipotent (F := F) :=
    Equiv.ofBijective (fun t => CentralRootGeometry.element t.1 t.2.1 t.2.2.1 t.2.2.2)
      ⟨CentralRootGeometry.element_injective, CentralRootGeometry.element_surjective⟩
  rw [Finset.sum_apply]
  rw [← κ.sum_comp]
  change (∑ t : F × F × F × F,
    tensorModel e (FullIndex n) (sylowMap hq
      (CentralRootGeometry.element t.1 t.2.1 t.2.2.1 t.2.2.2)) (lowest n) (fun _ => a)) = 1
  simp_rw [highest_coefficient e hq hF]
  rw [← map_sum]
  change e (∑ t : F × F × F × F,
    t.2.1^(Nat.card F-1) *
      (t.2.1*t.2.2.2+t.2.2.1^2+t.1*t.2.2.1*t.2.2.2)^(Nat.card F-1)) = 1
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hr : (∑ b : F, ∑ x : F, ∑ y : F, ∑ z : F,
      x^(Nat.card F-1) * (x*z+y^2+b*y*z)^(Nat.card F-1)) = 1 := by
    calc
      _ = ∑ x : F, ∑ y : F, ∑ z : F, ∑ b : F,
          x^(Nat.card F-1) * (x*z+y^2+b*y*z)^(Nat.card F-1) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        exact Finset.sum_comm
      _ = 1 := by simpa only [Nat.card_eq_fintype_card] using (orbit_sum (F := F))
  rw [hr, map_one]

lemma norm_lowest_ne_zero (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) :
    (∑ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) (lowest n)) ≠ 0 := by
  intro hz
  have hh := norm_highest_coefficient e hq hF
  rw [hz, Pi.zero_apply] at hh
  exact zero_ne_one hh

omit [Algebra (ZMod 2) F] in
lemma dimension_eq_card (n : ℕ) (hF : Nat.card F = 2^n) :
    Module.finrank E ((FullIndex n → Coordinate) → E) = Fintype.card (unipotent (F := F)) := by
  rw [tensorModel_finrank, ← Nat.card_eq_fintype_card, card_unipotent, hF]
  simp only [FullIndex, Finset.card_univ, Fintype.card_fin]
  calc
    4 ^ (2*n) = (2^2)^(2*n) := by norm_num
    _ = (2^n)^4 := by simp only [← pow_mul]; congr 1; omega


omit [Finite F] in
lemma coefficient_ringChar (e : F →+* E) : ringChar E = 2 := by
  let : CharP E 2 := charP_of_injective_ringHom e.injective 2
  exact ringChar.eq E 2

omit [Finite F] in
private lemma coefficient_char_ne_zero (e : F →+* E) : ringChar E ≠ 0 := by
  rw [coefficient_ringChar e]
  decide

private lemma sylow_isPGroup (e : F →+* E) {n : ℕ} (hF : Nat.card F = 2^n) :
    IsPGroup (ringChar E) (unipotent (F := F)) := by
  rw [coefficient_ringChar e]
  exact isPGroup_unipotent hF

/-- The regular coefficient space maps equivariantly onto the full tensor by
sending the delta function at `u` to the translate of the marked lowest vector. -/
noncomputable def orbitEquiv (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) :
    (unipotent (F := F) → E) ≃ₗ[E] ((FullIndex n → Coordinate) → E) :=
  PGroupRegularOrbit.orbitEquiv (by exact coefficient_char_ne_zero e) (by exact sylow_isPGroup e hF)
    ((tensorModel e (FullIndex n)).comp (sylowMap hq)) (lowest n)
    (norm_lowest_ne_zero e hq hF) (dimension_eq_card n hF)

lemma orbitEquiv_apply (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) (f : unipotent (F := F) → E) :
    orbitEquiv e hq hF f =
      ∑ u : unipotent (F := F), f u • tensorModel e (FullIndex n) (sylowMap hq u) (lowest n) := rfl

lemma orbitEquiv_equivariant (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) (u : unipotent (F := F)) (f : unipotent (F := F) → E) :
    orbitEquiv e hq hF (PGroupRegularOrbit.regular u f) =
      tensorModel e (FullIndex n) (sylowMap hq u) (orbitEquiv e hq hF f) :=
  PGroupRegularOrbit.orbitMap_equivariant _ _ _ _

noncomputable def orbitBasis (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) :
    Module.Basis (unipotent (F := F)) E ((FullIndex n → Coordinate) → E) :=
  PGroupRegularOrbit.orbitBasis (by exact coefficient_char_ne_zero e) (by exact sylow_isPGroup e hF)
    ((tensorModel e (FullIndex n)).comp (sylowMap hq)) (lowest n)
    (norm_lowest_ne_zero e hq hF) (dimension_eq_card n hF)

lemma orbitBasis_apply (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) (u : unipotent (F := F)) :
    orbitBasis e hq hF u = tensorModel e (FullIndex n) (sylowMap hq u) (lowest n) :=
  PGroupRegularOrbit.orbitBasis_apply _ _ _ _ _ _ _

lemma norm_lowest_eq_highest (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) :
    (∑ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) (lowest n)) =
      highest n := by
  have hh := (PGroupRegularOrbit.fixed_iff (coefficient_char_ne_zero e) (sylow_isPGroup e hF)
    ((tensorModel e (FullIndex n)).comp (sylowMap hq)) (lowest n)
    (norm_lowest_ne_zero e hq hF) (dimension_eq_card n hF) (highest n)).mp
    (highest_fixed e n hq)
  obtain ⟨z, hz⟩ := hh
  have he : (1 : E) = z := by
    have h := congrFun hz (fun _ => a)
    change highest n (fun _ => a) = z *
      (∑ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) (lowest n))
        (fun _ => a) at h
    simpa [highest, norm_highest_coefficient e hq hF] using h
  simpa [← he] using hz.symm

/-- The exact fixed line for the same marked matrix Sylow subgroup. -/
lemma fixed_line (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) (v : (FullIndex n → Coordinate) → E) :
    (∀ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) v = v) ↔
      ∃ z : E, v = z • highest n := by
  have hh := PGroupRegularOrbit.fixed_iff (coefficient_char_ne_zero e) (sylow_isPGroup e hF)
    ((tensorModel e (FullIndex n)).comp (sylowMap hq)) (lowest n)
    (norm_lowest_ne_zero e hq hF) (dimension_eq_card n hF) v
  change (∀ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) v = v) ↔
    ∃ z : E, v = z •
      (∑ u : unipotent (F := F), tensorModel e (FullIndex n) (sylowMap hq u) (lowest n)) at hh
  rwa [norm_lowest_eq_highest e hq hF] at hh

/-- A nonzero submodule contains a Sylow-fixed vector, hence the highest vector,
the lowest vector, and its complete Sylow orbit basis. -/
lemma irreducible (e : F →+* E) {n : ℕ} (hq : 2 < Nat.card F)
    (hF : Nat.card F = 2^n) : IsIrreducible (tensorModel e (FullIndex n)) := by
  classical
  let ρ := tensorModel e (FullIndex n)
  have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, fun h =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro W hW
  have : Nontrivial W.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr
    (fun hh => hW (Subrepresentation.toSubmodule_injective hh))
  obtain ⟨v, hv, hfix⟩ := pGroup_fix_nonzero_vector (coefficient_char_ne_zero e)
    (sylow_isPGroup e hF) (W.toRepresentation.comp (sylowMap hq))
  obtain ⟨z, hz⟩ := (fixed_line e hq hF v.val).mp (fun u => congrArg Subtype.val (hfix u))
  have hz0 : z ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    simpa [h] using hz
  have hhigh : highest n ∈ W := by
    have hh := W.toSubmodule.smul_mem z⁻¹ v.property
    rw [hz, inv_smul_smul₀ hz0] at hh
    exact hh
  have hlow : lowest n ∈ W := by
    have hh := W.apply_mem_toSubmodule (longElement hq) hhigh
    rwa [longElement_highest e n hq] at hh
  apply le_antisymm le_top
  intro w _
  rw [← (orbitBasis e hq hF).sum_repr w]
  apply W.toSubmodule.sum_mem
  intro u _
  apply W.toSubmodule.smul_mem
  rw [orbitBasis_apply]
  exact W.apply_mem_toSubmodule (sylowMap hq u) hlow

/-- The full tensor in the nonbinary source range is irreducible over every
coefficient field admitting the specified embedding. -/
theorem tensorModel_full_irreducible (e : F →+* E) {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 2 ≤ n) :
    IsIrreducible (tensorModel e (Finset.univ : Finset (Fin (2*n)))) := by
  apply irreducible e (hF := hF)
  rw [hF]
  calc
    2 < 2^2 := by decide
    _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.FullOrbit
