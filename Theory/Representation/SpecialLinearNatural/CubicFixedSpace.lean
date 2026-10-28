module

public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.CubicFixedSpace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.FinCases

/-!
A binary root four-group in SL₃(F) has fixed space F e₁ on the natural
module. An explicit cubic normalizes that four-group and fixes this space.
The same calculation works on identically marked copies and central sections.
Source: Aschbacher–Smith B.4.8, B.5.1 and 15.3.67.
-/

@[expose] public section
open Matrix Subgroup Representation Representation.BinaryOffender
namespace Representation.SL3BinaryCubic
variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev Actor (F : Type*) [CommRing F] := Matrix.SpecialLinearGroup (Fin 3) F
abbrev Space (F : Type*) := Fin 3 → F

abbrev natural : Representation (ZMod 2) (Actor F) (Space F) :=
  (specialLinearNatural 3).restrictScalars

def root (a b : F) : Actor F :=
  ⟨!![1,a,b; 0,1,0; 0,0,1], by simp [Matrix.det_fin_three]⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
private lemma root_mul (a b c d : F) : root a b * root c d = root (a+c) (b+d) := by
  apply Subtype.ext
  change (root a b).val * (root c d).val = (root (a+c) (b+d)).val
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

omit [CharP F 2] [Algebra (ZMod 2) F] in
private lemma root_zero : root (0 : F) 0 = 1 := by
  apply Subtype.ext
  funext i j
  fin_cases i <;> fin_cases j <;> simp [root]

omit [Algebra (ZMod 2) F] in
private lemma root_inv (a b : F) : (root a b)⁻¹ = root a b := by
  apply inv_eq_of_mul_eq_one_left
  rw [root_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, root_zero]

/-- Only the two binary parameters are used, even when F is a larger field. -/
def binaryRootHom : Multiplicative (ZMod 2 × ZMod 2) →* Actor F where
  toFun x := root (algebraMap (ZMod 2) F x.toAdd.1) (algebraMap (ZMod 2) F x.toAdd.2)
  map_one' := by simpa using (root_zero (F := F))
  map_mul' x y := by simp [root_mul]

def klein : Subgroup (Actor F) := (binaryRootHom (F := F)).range

omit [CharP F 2] in
lemma binaryRootHom_injective : Function.Injective (binaryRootHom (F := F)) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · exact (algebraMap (ZMod 2) F).injective (congrArg (fun g : Actor F => g.val 0 1) h)
  · exact (algebraMap (ZMod 2) F).injective (congrArg (fun g : Actor F => g.val 0 2) h)

omit [CharP F 2] in
lemma klein_card : Nat.card (klein (F := F)) = 4 := by
  classical
  change Nat.card (binaryRootHom (F := F)).range = 4
  rw [Nat.card_eq_fintype_card, Fintype.card_coeSort_range binaryRootHom_injective]
  decide +kernel

omit [CharP F 2] in
private lemma root_mem_klein (a b : ZMod 2) :
    root (algebraMap (ZMod 2) F a) (algebraMap (ZMod 2) F b) ∈ klein :=
  ⟨Multiplicative.ofAdd (a,b), rfl⟩

omit [CharP F 2] in
lemma klein_two : IsPGroup 2 (klein (F := F)) := by
  exact ZModModule.isPGroup_multiplicative.of_surjective
    (binaryRootHom (F := F)).rangeRestrict (binaryRootHom (F := F)).rangeRestrict_surjective

def cycle : Actor F :=
  ⟨!![1,0,0; 0,0,1; 0,1,1], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

private def cycleInverse : Actor F :=
  ⟨!![1,0,0; 0,1,1; 0,1,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

omit [Algebra (ZMod 2) F] in
private lemma cycle_inv : (cycle (F := F))⁻¹ = cycleInverse := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (cycleInverse (F := F)).val * cycle.val = (1 : Matrix (Fin 3) (Fin 3) F)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, cycleInverse, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

omit [Algebra (ZMod 2) F] in
lemma cycle_pow : (cycle (F := F)) ^ 3 = 1 := by
  apply Subtype.ext
  change (cycle (F := F)).val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycle, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]

omit [Algebra (ZMod 2) F] in
lemma cycle_ne_one : (cycle (F := F)) ≠ 1 := by
  intro h
  have he := congrArg (fun g : Actor F => g.val 1 1) h
  exact zero_ne_one he

omit [Algebra (ZMod 2) F] in
lemma cycle_order : orderOf (cycle (F := F)) = 3 :=
  orderOf_eq_prime cycle_pow cycle_ne_one

omit [Algebra (ZMod 2) F] in
private lemma cycle_conjugate_root (a b : F) :
    cycle * root a b * cycle⁻¹ = root (a+b) a := by
  rw [cycle_inv]
  apply Subtype.ext
  change cycle.val * (root a b).val * cycleInverse.val = (root (a+b) a).val
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [root, cycle, cycleInverse, Matrix.mul_apply, Fin.sum_univ_three,
      CharTwo.add_self_eq_zero, add_comm]

lemma cycle_normalizes :
    cycle (F := F) ∈ normalizer (klein (F := F) : Set (Actor F)) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, rfl⟩
    change cycle * root _ _ * cycle⁻¹ ∈ klein
    rw [cycle_conjugate_root, ← map_add]
    exact root_mem_klein (x.toAdd.1 + x.toAdd.2) x.toAdd.1
  · rintro ⟨x, hx⟩
    have he : g = root (algebraMap (ZMod 2) F x.toAdd.2)
        (algebraMap (ZMod 2) F (x.toAdd.1 + x.toAdd.2)) := by
      apply (MulAut.conj (cycle (F := F))).injective
      change cycle * g * cycle⁻¹ = cycle * root _ _ * cycle⁻¹
      rw [← hx, cycle_conjugate_root, map_add]
      change root _ _ = root _ _
      congr 1
      rw [add_left_comm, CharTwo.add_self_eq_zero, add_zero]
    rw [he]
    exact root_mem_klein x.toAdd.2 (x.toAdd.1 + x.toAdd.2)

omit [CharP F 2] in
private lemma root_action (a b : F) (v : Space F) :
    natural (root a b) v = ![v 0 + a * v 1 + b * v 2, v 1, v 2] := by
  change (root a b).val.mulVec v = _
  funext i
  fin_cases i <;>
    simp [root, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

private lemma cycle_action (v : Space F) :
    natural (cycle (F := F)) v = ![v 0, v 2, v 1 + v 2] := by
  change (cycle (F := F)).val.mulVec v = _
  funext i
  fin_cases i <;>
    simp [cycle, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]

omit [CharP F 2] in
/-- The fixed space consists of all F multiples of the first basis vector. -/
lemma mem_fixedSpace_klein_iff (v : Space F) :
    v ∈ fixedSpace natural klein ↔ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro hv
    have h1 := congrFun (hv ⟨root (1 : F) 0, by simpa using root_mem_klein (F := F) 1 0⟩) 0
    have h2 := congrFun (hv ⟨root (0 : F) 1, by simpa using root_mem_klein (F := F) 0 1⟩) 0
    change natural (root 1 0) v 0 = v 0 at h1
    change natural (root 0 1) v 0 = v 0 at h2
    simp only [root_action, Matrix.cons_val_zero, one_mul, zero_mul, add_zero] at h1 h2
    exact ⟨add_eq_left.mp h1, add_eq_left.mp h2⟩
  · rintro ⟨h1,h2⟩ ⟨g,hg⟩
    obtain ⟨x,rfl⟩ := hg
    change natural (root _ _) v = v
    rw [root_action]
    funext i
    fin_cases i <;> simp [h1,h2]

lemma cycle_fixes_natural :
    ∀ v ∈ fixedSpace (natural (F := F)) klein, natural cycle v = v := by
  intro v hv
  obtain ⟨h1,h2⟩ := (mem_fixedSpace_klein_iff v).mp hv
  rw [cycle_action]
  funext i
  fin_cases i <;> simp [h1,h2]

lemma cycle_fixes_double :
    ∀ v ∈ fixedSpace ((natural (F := F)).prod natural) klein,
      (natural.prod natural) cycle v = v := by
  intro v hv
  exact Prod.ext (cycle_fixes_natural v.1 (fun g => congrArg Prod.fst (hv g)))
    (cycle_fixes_natural v.2 (fun g => congrArg Prod.snd (hv g)))

private theorem centralSection_cubic
    {D V X : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) D V) (f : Actor F →* D) (hf : Function.Injective f)
    (σ : Representation (ZMod 2) (Actor F) X)
    (hσ : ∀ x ∈ fixedSpace σ klein, σ cycle x = x)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] X)
    (hq : ∀ g u, q (U.toRepresentation g u) = σ g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v := by
  obtain ⟨c, hc, hp, hv⟩ := sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf
    klein klein_two cycle cycle_pow cycle_ne_one
    (cubic_fixedSpace_of_central_section (ρ.comp f) σ _ _ cycle_pow cycle_normalizes
      U q hq hker hquot hσ) S
  exact ⟨c, orderOf_eq_prime hp (fun h => hc (h ▸ S.one_mem)), hv⟩

/-- Natural central sections, with the literal subrepresentation and quotient map. -/
theorem natural_centralSection_cubic
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor F →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] Space F)
    (hq : ∀ g u, q (U.toRepresentation g u) = natural g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v :=
  centralSection_cubic ρ f hf natural cycle_fixes_natural U q hq hker hquot S

/-- The two natural factors retain the same SL₃(F) marking. -/
theorem double_centralSection_cubic
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (f : Actor F →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f)) (q : U.toSubmodule →ₗ[ZMod 2] (Space F × Space F))
    (hq : ∀ g u, q (U.toRepresentation g u) = (natural.prod natural) g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ c : D, orderOf c = 3 ∧ ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ c v = v :=
  centralSection_cubic ρ f hf (natural.prod natural) cycle_fixes_double U q hq hker hquot S

end Representation.SL3BinaryCubic
