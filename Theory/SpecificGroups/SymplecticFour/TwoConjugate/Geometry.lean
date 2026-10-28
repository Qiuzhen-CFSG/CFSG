module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.Representation.SubrepresentationLattice
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Irreducibility of the actual opposite central-root pair

The standard Sylow center is the plane of long and short root parameters.
Unless a subgroup lies in one root axis or a diagonal root line, two of its
parameter vectors are independent over the coefficient field. Linear
combinations of their displacement operators isolate the two root operators.
The opposite operators then connect the four coordinate vectors, proving
irreducibility over F of the original generated subgroup.

This is the irreducibility step in Aschbacher–Smith, E.2.7, printed pp.219–220.
It avoids replacing F-linear irreducibility with binary irreducibility, and
works even when neither root axis meets V nontrivially. Recognition of the
resulting finite subgroup is a separate source obligation.
-/

@[expose] public section
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [CharP F 2]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

def opposition : Sp F := ⟨fromBlocks 0 1 1 0, by
  rw [SymplecticGroup.mem_iff]
  simp only [Matrix.J, fromBlocks_multiply, fromBlocks_transpose,
    transpose_zero, transpose_one, mul_zero, zero_mul, mul_one, one_mul,
    zero_add, add_zero]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq]⟩

theorem opposition_inv : (opposition (F := F))⁻¹ = opposition := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change fromBlocks 0 1 1 0 * fromBlocks 0 1 1 0 = (1 : Matrix _ _ F)
  simp [fromBlocks_multiply, ← fromBlocks_one]

def upper (s t : F) : Sp F := rootElement 0 s * rootElement 4 t

def lower (s t : F) : Sp F := opposition * upper s t * opposition⁻¹

theorem upper_apply (s t : F) (x : Vector F) :
    upper s t • x = Sum.elim ![x a + s*x c + t*x d,x b+t*x c] ![x c,x d] := by
  change (rootMatrix 0 s * rootMatrix 4 t) *ᵥ x = _
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [rootMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single, Matrix.one_apply,
      Matrix.fromBlocks] <;> ring

theorem opposition_apply (x : Vector F) :
    (opposition (F := F)) • x = Sum.elim ![x c,x d] ![x a,x b] := by
  change fromBlocks 0 1 1 0 *ᵥ x = _
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.one_apply, Matrix.fromBlocks]

theorem lower_apply (s t : F) (x : Vector F) :
    lower s t • x = Sum.elim ![x a,x b] ![x c+s*x a+t*x b,x d+t*x a] := by
  rw [lower, opposition_inv, mul_smul, mul_smul, opposition_apply, upper_apply,
    opposition_apply]
  rfl

private theorem upper_displacement (s t : F) (x : Vector F) :
    upper s t • x - x =
      s • (x c • Pi.single a 1) + t • (x d • Pi.single a 1 + x c • Pi.single b 1) := by
  rw [upper_apply]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Pi.single_apply] <;> ring

private theorem lower_displacement (s t : F) (x : Vector F) :
    lower s t • x - x =
      s • (x a • Pi.single c 1) + t • (x b • Pi.single c 1 + x a • Pi.single d 1) := by
  rw [lower_apply]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Pi.single_apply] <;> ring

private theorem separate_two (W : Submodule F (Vector F)) (y z : Vector F)
    (s t u v : F) (hdet : s*v-u*t ≠ 0)
    (h₁ : s • y+t • z ∈ W) (h₂ : u • y+v • z ∈ W) : y ∈ W ∧ z ∈ W := by
  have hy : (s*v-u*t) • y ∈ W := by
    have h := W.sub_mem (W.smul_mem v h₁) (W.smul_mem t h₂)
    convert h using 1 <;> module
  have hz : (s*v-u*t) • z ∈ W := by
    have h := W.sub_mem (W.smul_mem s h₂) (W.smul_mem u h₁)
    convert h using 1 <;> module
  exact ⟨(W.smul_mem_iff hdet).mp hy,(W.smul_mem_iff hdet).mp hz⟩

/-- Two independent central-root directions and their opposites act
irreducibly on the literal four-dimensional F-space. -/
theorem invariant_eq_bot_or_top (W : Submodule F (Vector F))
    (s t u v : F) (hdet : s*v-u*t ≠ 0)
    (hup₁ : ∀x∈W,upper s t • x ∈ W)
    (hup₂ : ∀x∈W,upper u v • x ∈ W)
    (hlo₁ : ∀x∈W,lower s t • x ∈ W)
    (hlo₂ : ∀x∈W,lower u v • x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hu (x : Vector F) (hx : x ∈ W) :
      x c • Pi.single a 1 ∈ W ∧ x d • Pi.single a 1 + x c • Pi.single b 1 ∈ W := by
    apply separate_two W _ _ s t u v hdet
    · simpa only [upper_displacement] using W.sub_mem (hup₁ x hx) hx
    · simpa only [upper_displacement] using W.sub_mem (hup₂ x hx) hx
  have hl (x : Vector F) (hx : x ∈ W) :
      x a • Pi.single c 1 ∈ W ∧ x b • Pi.single c 1 + x a • Pi.single d 1 ∈ W := by
    apply separate_two W _ _ s t u v hdet
    · simpa only [lower_displacement] using W.sub_mem (hlo₁ x hx) hx
    · simpa only [lower_displacement] using W.sub_mem (hlo₂ x hx) hx
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have he : (Pi.single a (1:F) : Vector F) ∈ W := by
    by_cases hc : x c = 0
    · by_cases hd : x d = 0
      · by_cases ha : x a = 0
        · have hb : x b ≠ 0 := by
            intro hb
            apply hx0
            ext i
            rcases i with i | i <;> fin_cases i <;> simp_all
          have hf : (Pi.single c (1:F) : Vector F) ∈ W := by
            have h := (hl x hx).2
            simpa [ha] using (W.smul_mem_iff hb).mp (by simpa [ha] using h)
          simpa using (hu _ hf).1
        · have hf : (Pi.single c (1:F) : Vector F) ∈ W :=
            (W.smul_mem_iff ha).mp (hl x hx).1
          simpa using (hu _ hf).1
      · have h := (hu x hx).2
        exact (W.smul_mem_iff hd).mp (by simpa [hc] using h)
    · exact (W.smul_mem_iff hc).mp (hu x hx).1
  have hf : (Pi.single c (1:F) : Vector F) ∈ W := by simpa using (hl _ he).1
  have he' : (Pi.single b (1:F) : Vector F) ∈ W := by simpa using (hu _ hf).2
  have hf' : (Pi.single d (1:F) : Vector F) ∈ W := by simpa using (hl _ he).2
  apply top_unique
  intro y _
  have h := W.add_mem (W.add_mem (W.smul_mem (y a) he) (W.smul_mem (y b) he'))
    (W.add_mem (W.smul_mem (y c) hf) (W.smul_mem (y d) hf'))
  convert h using 1
  ext i
  rcases i with i | i <;> fin_cases i <;> simp

/-- The actual source pair generated by the central subgroup and its
opposite under the flag-swapping symplectic matrix. -/
def oppositePair (V : Subgroup (Sp F)) : Subgroup (Sp F) :=
  V ⊔ V.map (MulAut.conj (opposition (F := F))).toMonoidHom

/-- The natural action of the actual opposite pair. -/
def pairAction (V : Subgroup (Sp F)) : Representation F (oppositePair V) (Vector F) :=
  (Representation.symplecticNatural 2).comp (oppositePair V).subtype

theorem pairAction_irreducible_of_independent (V : Subgroup (Sp F))
    (s t u v : F) (hdet : s*v-u*t ≠ 0)
    (h₁ : upper s t ∈ V) (h₂ : upper u v ∈ V) :
    Representation.IsIrreducible (pairAction V) := by
  refine ⟨fun W => ?_⟩
  have hi (g : Sp F) (hg : g ∈ oppositePair V) (x : Vector F) (hx : x ∈ W) :
      g • x ∈ W := W.apply_mem_toSubmodule ⟨g,hg⟩ hx
  have hl (s t : F) (hs : upper s t ∈ V) : lower s t ∈ oppositePair V :=
    (show V.map (MulAut.conj (opposition (F := F))).toMonoidHom ≤ oppositePair V from le_sup_right) (mem_map_of_mem (MulAut.conj (opposition (F := F))).toMonoidHom hs)
  rcases invariant_eq_bot_or_top W.toSubmodule s t u v hdet
    (hi _ ((show V ≤ oppositePair V from le_sup_left) h₁))
    (hi _ ((show V ≤ oppositePair V from le_sup_left) h₂))
    (hi _ (hl _ _ h₁)) (hi _ (hl _ _ h₂)) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

private theorem upper_add (s t u v : F) : upper s t * upper u v = upper (s+u) (t+v) := by
  simpa only [Subgroup.coe_mul, CentralRootGeometry.theta_val,upper] using
    congrArg (fun g : unipotent (F := F) => (g : Sp F))
      (CentralRootGeometry.theta_add s t u v)

/-- The diagonal root line R(μ), with the printed parameter convention. -/
def diagonalHom (μ : F) : Multiplicative F →* Sp F where
  toFun x := upper x.toAdd (x.toAdd*μ)
  map_one' := by simp [upper,RootSubgroup.element_zero]
  map_mul' x y := by simpa [add_mul] using (upper_add x.toAdd (x.toAdd*μ) y.toAdd (y.toAdd*μ)).symm

def diagonal (μ : F) : Subgroup (Sp F) := (diagonalHom μ).range

theorem mem_diagonal_iff (μ : F) (x : Sp F) :
    x ∈ diagonal μ ↔ ∃s, upper s (s*μ) = x := by
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨s.toAdd,hs⟩
  · rintro ⟨s,hs⟩
    exact ⟨Multiplicative.ofAdd s,hs⟩

private theorem parameter_eq_upper (s t : Multiplicative F) :
    CentralRootGeometry.parameter (s,t) = upper s.toAdd t.toAdd :=
  CentralRootGeometry.parameter_apply _

theorem exists_independent_of_no_diagonal (V : Subgroup (Sp F))
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (hl : ¬ V ≤ RootSubgroup.group 0) (hs : ¬ V ≤ RootSubgroup.group 4)
    (hd : ∀μ:F,μ≠0 → ¬V ≤ diagonal μ) :
    ∃s t u v:F,upper s t ∈ V ∧ upper u v ∈ V ∧ s*v-u*t≠0 := by
  obtain ⟨x,hx,hxs⟩ := SetLike.not_le_iff_exists.mp hs
  obtain ⟨⟨s,t⟩,rfl⟩ := hc hx
  simp only [parameter_eq_upper] at hx hxs
  have hsn : s.toAdd ≠ 0 := by
    intro h
    apply hxs
    apply (RootSubgroup.mem_group_iff 4 _).mpr
    exact ⟨t.toAdd,by simp [upper,h,RootSubgroup.element_zero]⟩
  by_contra! hn
  have he (u v:F) (h:upper u v ∈ V) : s.toAdd*v-u*t.toAdd=0 :=
    hn s.toAdd t.toAdd u v hx h
  by_cases ht : t.toAdd=0
  · apply hl
    intro y hy
    obtain ⟨⟨u,v⟩,rfl⟩ := hc hy
    simp only [parameter_eq_upper] at hy
    have hv : v.toAdd=0 := by
      have h := he u.toAdd v.toAdd hy
      simpa [ht,hsn] using h
    apply (RootSubgroup.mem_group_iff 0 _).mpr
    exact ⟨u.toAdd,by simp [CentralRootGeometry.parameter_apply, hv,RootSubgroup.element_zero]⟩
  · apply hd (t.toAdd/s.toAdd) (div_ne_zero ht hsn)
    intro y hy
    obtain ⟨⟨u,v⟩,rfl⟩ := hc hy
    simp only [parameter_eq_upper] at hy
    apply (mem_diagonal_iff _ _).mpr
    refine ⟨u.toAdd,?_⟩
    simp only [parameter_eq_upper]
    congr 1
    rw [← mul_div_assoc]
    apply (div_eq_iff hsn).mpr
    have h := he u.toAdd v.toAdd hy
    linear_combination -h

/-- The source non-diagonal branch is irreducible over F itself. Neither
binary irreducibility nor any representation-recognition theorem is used. -/
theorem pairAction_irreducible_of_no_diagonal (V : Subgroup (Sp F))
    (hc : V ≤ (CentralRootGeometry.parameter (F := F)).range)
    (hl : ¬ V ≤ RootSubgroup.group 0) (hs : ¬ V ≤ RootSubgroup.group 4)
    (hd : ∀μ:F,μ≠0 → ¬V ≤ diagonal μ) :
    Representation.IsIrreducible (pairAction V) := by
  obtain ⟨s,t,u,v,h₁,h₂,hdet⟩ := exists_independent_of_no_diagonal V hc hl hs hd
  exact pairAction_irreducible_of_independent V s t u v hdet h₁ h₂

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
