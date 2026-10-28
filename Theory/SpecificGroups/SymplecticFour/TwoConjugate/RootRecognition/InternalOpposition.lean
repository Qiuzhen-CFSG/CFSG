module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition.FourAxes
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.MovingActor
-- This continuation reuses the internal Weyl-word matrix calculations.
import all Theory.SpecificGroups.SymplecticFour.TwoConjugate.RootRecognition.FourAxes

/-!
# An internal opposition from two nonzero central-root intersections

After a diagonal change of coordinates, one nonidentity element in each
central root axis gives the parameter-one long and short root elements.
Their opposites give two Weyl words. The square of their product is the
literal opposition matrix, hence opposition belongs to the group generated
by the normalized subgroup and its opposite. Transport back gives an
internal conjugator for the original subgroup. No recognition of the
generated group or coefficient field is assumed.

Source: the root-containing branch of Aschbacher--Smith E.2.7,
printed pp.219--220.
-/

public section
noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2]

private theorem opposition_word :
    ((rootElement 0 (1:F) * rootElement 1 1 * rootElement 0 1) *
      (rootElement 4 1 * rootElement 5 1 * rootElement 4 1)) ^ 2 = opposition := by
  apply Subtype.ext
  change ((n₀ (F := F)).val * (n₄ (F := F)).val)^2 = fromBlocks 0 1 1 0
  rw [n₀_matrix,n₄_matrix,pow_two]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

/-- Two parameter-one central-root elements make the fixed opposition internal. -/
theorem opposition_mem_of_unit_axes (V : Subgroup (Sp F))
    (h₀ : rootElement 0 (1:F) ∈ V) (h₄ : rootElement 4 (1:F) ∈ V) :
    opposition ∈ oppositePair V := by
  have hpos {x : Sp F} (hx : x ∈ V) : x ∈ oppositePair V := (show V ≤ oppositePair V from le_sup_left) hx
  have hneg {x : Sp F} (hx : x ∈ V) : opposition * x * opposition⁻¹ ∈ oppositePair V :=
    (show V.map (MulAut.conj (opposition (F := F))).toMonoidHom ≤ oppositePair V from le_sup_right) (mem_map_of_mem (MulAut.conj opposition).toMonoidHom hx)
  have h₁ : rootElement 1 (1:F) ∈ oppositePair V := by
    rw [←(opposition_central_axes (F:=F) 1).1]
    exact hneg h₀
  have h₅ : rootElement 5 (1:F) ∈ oppositePair V := by
    rw [←(opposition_central_axes (F:=F) 1).2]
    exact hneg h₄
  rw [←opposition_word]
  exact (oppositePair V).pow_mem ((oppositePair V).mul_mem
    ((oppositePair V).mul_mem ((oppositePair V).mul_mem (hpos h₀) h₁) (hpos h₀))
    ((oppositePair V).mul_mem ((oppositePair V).mul_mem (hpos h₄) h₅) (hpos h₄))) 2

variable [Finite F]

/-- A diagonal element of the actual Borel normalizes two nonzero central-root
parameters simultaneously to one. -/
theorem exists_torus_unit_axes (V : Subgroup (Sp F))
    {s t : F} (hs : s ≠ 0) (ht : t ≠ 0)
    (h₀ : rootElement 0 s ∈ V) (h₄ : rootElement 4 t ∈ V) :
    ∃ b : Sp F, b ∈ normalizer (unipotent (F := F) : Set (Sp F)) ∧
      rootElement 0 (1:F) ∈ V.map (MulAut.conj b).toMonoidHom ∧
      rootElement 4 (1:F) ∈ V.map (MulAut.conj b).toMonoidHom := by
  obtain ⟨x,hx⟩ := Finite.surjective_of_injective (CharTwo.sq_injective (R := F)) s⁻¹
  change x^2 = s⁻¹ at hx
  have hx0 : x ≠ 0 := by
    intro h
    have : s⁻¹ = 0 := by simpa [h] using hx.symm
    exact hs (inv_eq_zero.mp this)
  let a : Fˣ × Fˣ := (Units.mk0 x hx0, Units.mk0 (x*t)⁻¹ (inv_ne_zero (mul_ne_zero hx0 ht)))
  refine ⟨diagonalTorusHom a, diagonalTorus_normalizes a, ?_, ?_⟩
  · have he := diagonalTorus_weights a s 0
    have hxs : x^2*s=1 := by rw [hx,inv_mul_cancel₀ hs]
    have hconj : (MulAut.conj (diagonalTorusHom a)) (rootElement 0 s) = rootElement 0 1 := by
      simpa [parameter_apply,RootSubgroup.element_zero,a,hxs] using he
    rw [←hconj]
    exact mem_map_of_mem (MulAut.conj (diagonalTorusHom a)).toMonoidHom h₀
  · have he := diagonalTorus_weights a 0 t
    have hxt : x*(x*t)⁻¹*t=1 := by field_simp
    have hconj : (MulAut.conj (diagonalTorusHom a)) (rootElement 4 t) = rootElement 4 1 := by
      simp only [parameter_apply,toAdd_ofAdd,RootSubgroup.element_zero,one_mul,mul_zero] at he
      change diagonalTorusHom a * rootElement 4 t * (diagonalTorusHom a)⁻¹ =
        rootElement 4 (x*(x*t)⁻¹*t) at he
      rw [hxt] at he
      exact he
    rw [←hconj]
    exact mem_map_of_mem (MulAut.conj (diagonalTorusHom a)).toMonoidHom h₄

omit [Finite F] in
theorem internal_conjugator_of_normalized_axes (V : Subgroup (Sp F)) (b : Sp F)
    (h₀ : rootElement 0 (1:F) ∈ V.map (MulAut.conj b).toMonoidHom)
    (h₄ : rootElement 4 (1:F) ∈ V.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * opposition * b ∈ V ⊔ V.map (MulAut.conj (b⁻¹ * opposition * b)).toMonoidHom := by
  let g : Sp F := b⁻¹ * opposition * b
  let P := V ⊔ V.map (MulAut.conj g).toMonoidHom
  have hh : (MulAut.conj b).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj opposition).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,g,mul_assoc]
  have hmap : P.map (MulAut.conj b).toMonoidHom =
      oppositePair (V.map (MulAut.conj b).toMonoidHom) := by
    simp only [P,oppositePair,Subgroup.map_sup,Subgroup.map_map,hh]
  have hm := opposition_mem_of_unit_axes (V.map (MulAut.conj b).toMonoidHom) h₀ h₄
  rw [←hmap] at hm
  obtain ⟨x,hx,hxg⟩ := hm
  have he : x = g := by
    apply (MulAut.conj b).injective
    change b*x*b⁻¹ = b*g*b⁻¹
    simpa [g,mul_assoc] using hxg
  change g ∈ P
  exact he ▸ hx

theorem exists_internal_conjugator_of_nonzero_axes (V : Subgroup (Sp F))
    {s t : F} (hs : s ≠ 0) (ht : t ≠ 0)
    (h₀ : rootElement 0 s ∈ V) (h₄ : rootElement 4 t ∈ V) :
    ∃ b : Sp F, b ∈ normalizer (unipotent (F := F) : Set (Sp F)) ∧
      b⁻¹ * opposition * b ∈ V ⊔ V.map (MulAut.conj (b⁻¹ * opposition * b)).toMonoidHom := by
  obtain ⟨b,hb,h0,h4⟩ := exists_torus_unit_axes V hs ht h₀ h₄
  exact ⟨b,hb,internal_conjugator_of_normalized_axes V b h0 h4⟩

/-- The root-containing moving-actor branch has an internal conjugator of the
literal original V after a Borel change of coordinates. -/
theorem exists_internal_conjugator_of_moving_root (hq : 2 < Nat.card F)
    (a : EvenBorelTorus.ActorReduction.stabilizer (F := F))
    (ha : ¬ DiagramAutomorphisms.PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V)
    {s : F} (hs : s ≠ 0) (hroot : rootElement 0 s ∈ V) :
    ∃ b : Sp F, b ∈ normalizer (unipotent (F := F) : Set (Sp F)) ∧
      b⁻¹ * opposition * b ∈ V ⊔ V.map (MulAut.conj (b⁻¹ * opposition * b)).toMonoidHom := by
  obtain ⟨σ,c,d,_hc,hd,hcoord⟩ := moving_actor_coordinates hq a ha
  have hm : a.val (upper s 0) ∈ V := hV.le (mem_map_of_mem a.val.toMonoidHom
    (by simpa [upper,RootSubgroup.element_zero] using hroot))
  rw [hcoord] at hm
  have hshort : rootElement 4 (d*σ s) ∈ V := by
    simpa [upper,RootSubgroup.element_zero] using hm
  exact exists_internal_conjugator_of_nonzero_axes V hs
    (mul_ne_zero hd ((map_ne_zero σ).mpr hs)) hroot hshort

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
