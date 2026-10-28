module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Borels
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualLinear
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner
public import Theory.GroupAction.InnerSylow
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree.Fixers.Transport

/-!
# The intrinsic linear-three residual-torus actor centralizers

The actual first diagonal axis of O³(Fˣ) maps into O³(B). Thus source
fixation gives a displacement in the specified Sylow two-subgroup. At the
standard Sylow, the torus/unipotent complement converts this to a parameter
equality. The cubic projective scalar kernel permits neither a nontrivial
two-power field actor outside degrees two and six nor any graph-field actor
outside degree two. Projecting the SL₃ displacements proves the same facts
on the special linear cover, without identifying that cover with PSL₃.

The mixed-actor reductions remove the linear factor on the quotient and
bound the coefficient order from the full actor, without a torus-stability
premise. Every standard two-power fixer is consequently inner-diagonal.
Cubing removes the diagonal contribution, and Sylow maximality in Inn(D)
places every inner actor in the specified inner Sylow image. Conjugation
transports actual residual displacements for arbitrary Sylows; perfectness
lifts innerness from PSL₃ back to SL₃. The two final equivalences retain only
standard-automorphism coverage as an explicit earlier classification input.
Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

public section

open Subgroup Matrix.PSL3
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.CartanActions.BorelQuotient Matrix.PSL3.CartanActions.ResidualParameters
open Matrix.PSL3.OuterSolvable Matrix.PSL3.OuterSolvable.OddPrimeCoverage
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
variable {F : Type*} [Field F] [Finite F]

/-- The first parameter axis of O³(Fˣ) lies in the actual embedded Borel residual. -/
theorem special_residual_axis {u : Fˣ} (hu : u ∈ pResidual 3 Fˣ) :
    torusSL F (u,1) ∈ residualIn 3 (borelSL F) := by
  let f := (torusInBorelSL F).comp (MonoidHom.inl Fˣ Fˣ)
  exact ⟨f u, map_pResidual_le 3 f ⟨u,hu,rfl⟩, rfl⟩

/-- The same embedded residual axis survives projectivization. -/
theorem projective_residual_axis {u : Fˣ} (hu : u ∈ pResidual 3 Fˣ) :
    torusMap F (u,1) ∈ residualIn 3 (borel F) := by
  let f : Fˣ →* borel F :=
    ((torusMap F).codRestrict (borel F) (fun d => torus_le_borel F ⟨d,rfl⟩)).comp
      (MonoidHom.inl Fˣ Fˣ)
  exact ⟨f u, map_pResidual_le 3 f ⟨u,hu,rfl⟩, rfl⟩

/-- Source fixation at the standard SL₃ Sylow gives the literal axis displacement. -/
theorem special_fixer_axis {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (α : MulAut SL(3,F))
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSLSylow F (by omega) hF)) α)
    {u : Fˣ} (hu : u ∈ pResidual 3 Fˣ) :
    α (torusSL F (u,1)) * (torusSL F (u,1))⁻¹ ∈ unipotentSL F := by
  have hB : intrinsicResidual (unipotentSLSylow F (by omega) hF) = borelSL F := by
    rw [special_residual_eq hF hn]
    exact normalizer_unipotentSL F
  have hx : torusSL F (u,1) ∈
      residualIn 3 (intrinsicResidual (unipotentSLSylow F (by omega) hF)) := by
    rw [hB]
    exact special_residual_axis hu
  have h := hfix _ (Subgroup.mem_sup_left hx)
  rwa [special_residual_twoCore hF hn] at h

/-- Source fixation at the standard PSL₃ Sylow gives the literal axis displacement. -/
theorem projective_fixer_axis {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (α : MulAut PSL(3,F))
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSylow F (by omega) hF)) α)
    {u : Fˣ} (hu : u ∈ pResidual 3 Fˣ) :
    α (torusMap F (u,1)) * (torusMap F (u,1))⁻¹ ∈ unipotent F := by
  have hB : intrinsicResidual (unipotentSylow F (by omega) hF) = borel F := by
    rw [projective_residual_eq hF hn]
    exact normalizer_unipotent F (by omega) hF
  have hx : torusMap F (u,1) ∈
      residualIn 3 (intrinsicResidual (unipotentSylow F (by omega) hF)) := by
    rw [hB]
    exact projective_residual_axis hu
  have h := hfix _ (Subgroup.mem_sup_left hx)
  rwa [projective_residual_twoCore hF hn] at h


/-- A pure projective field actor of arbitrary two-power order is detected by
source residual fixation, outside degrees two and six. -/
theorem projective_field_fixer_eq_one [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (σ : F ≃+* F) (hpow : fieldAction F σ ^ (2 ^ k) = 1)
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSylow F (by omega) hF))
      (fieldAction F σ)) : σ = 1 := by
  apply field_eq_one_of_fixed_axes hF hn2 hn6 σ
  · apply fieldAction_injective
    rw [map_pow, hpow, map_one]
  · intro u hu
    apply (torus_displacement_mem_unipotent_iff hF _ _).mp
    have h := projective_fixer_axis hF hn (fieldAction F σ) hfix hu
    simpa only [field_torusMap, map_one] using h

/-- No pure graph-field actor fixes the source projective residual torus,
regardless of its order, when the field degree exceeds two. -/
theorem projective_graph_field_not_fixes {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (σ : F ≃+* F) :
    ¬ FixesResidualTorus (intrinsicResidual (unipotentSylow F (by omega) hF))
      (fieldAction F σ * oppositionGraph F) := by
  intro hfix
  apply graph_field_not_fixed hF hn hn2 σ
  intro u hu
  apply (torus_displacement_mem_unipotent_iff hF _ _).mp
  have h := projective_fixer_axis hF hn _ hfix hu
  simpa only [MulAut.mul_apply, oppositionGraph_torusMap, field_torusMap,
    inv_one, map_one, map_inv] using h

omit [Finite F] in
/-- The literal SL₃ field action projects to the existing PSL₃ field action. -/
private theorem projection_field (σ : F ≃+* F) (x : SL(3,F)) :
    projection F (Atlas.fieldEquivSL 3 σ x) = fieldAction F σ (projection F x) :=
  (fieldAction_mk F σ x).symm

/-- SL₃ pure field actors have the same coefficient rigidity, retaining the
actual SL₃ carrier rather than replacing it by its central quotient. -/
theorem special_field_fixer_eq_one [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (σ : F ≃+* F) (hpow : (Atlas.fieldEquivSL 3 σ) ^ (2 ^ k) = 1)
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSLSylow F (by omega) hF))
      (Atlas.fieldEquivSL 3 σ)) : σ = 1 := by
  have hp : fieldAction F σ ^ (2 ^ k) = 1 := by
    have he : centerAction F (Atlas.fieldEquivSL 3 σ) = fieldAction F σ := by
      ext x
      obtain ⟨y,rfl⟩ := projection_surjective F x
      exact projection_field σ y
    have h := congrArg (centerAction F) hpow
    simpa only [map_pow, map_one, he] using h
  have hσ : σ ^ (2 ^ k) = 1 := by
    apply fieldAction_injective
    rw [map_pow, hp, map_one]
  apply field_eq_one_of_fixed_axes hF hn2 hn6 σ hσ
  intro u hu
  apply (torus_displacement_mem_unipotent_iff hF _ _).mp
  have h := special_fixer_axis hF hn _ hfix hu
  have hp := Subgroup.mem_map_of_mem (projection F) h
  rw [map_mul, map_inv, projection_field] at hp
  change fieldAction F σ (torusMap F (u,1)) * (torusMap F (u,1))⁻¹ ∈ unipotent F at hp
  simpa only [field_torusMap, map_one] using hp

omit [Finite F] in
/-- Projecting the actual adjusted graph-field action commutes with the given
central quotient map. -/
private theorem projection_graph_field (σ : F ≃+* F) (x : SL(3,F)) :
    projection F ((Atlas.fieldEquivSL 3 σ *
      (linearConjSL F (reversalGL F) * graphSL F)) x) =
      (fieldAction F σ * oppositionGraph F) (projection F x) := by
  change projection F (Atlas.fieldEquivSL 3 σ
    (linearConjSL F (reversalGL F) (graphSL F x))) =
      fieldAction F σ (oppositionGraph F (projection F x))
  rw [projection_field]
  rfl

/-- The same graph obstruction applies on the actual special linear cover. -/
theorem special_graph_field_not_fixes {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (σ : F ≃+* F) :
    ¬ FixesResidualTorus (intrinsicResidual (unipotentSLSylow F (by omega) hF))
      (Atlas.fieldEquivSL 3 σ * (linearConjSL F (reversalGL F) * graphSL F)) := by
  intro hfix
  apply graph_field_not_fixed hF hn hn2 σ
  intro u hu
  apply (torus_displacement_mem_unipotent_iff hF _ _).mp
  have h := special_fixer_axis hF hn _ hfix hu
  have hp := Subgroup.mem_map_of_mem (projection F) h
  rw [map_mul, map_inv, projection_graph_field] at hp
  change (fieldAction F σ * oppositionGraph F) (torusMap F (u,1)) *
    (torusMap F (u,1))⁻¹ ∈ unipotent F at hp
  simpa only [MulAut.mul_apply, oppositionGraph_torusMap, field_torusMap,
    inv_one, map_one, map_inv] using hp

/-- At the standard projective Sylow, an arbitrary standard two-power fixer
has neither a field nor a graph contribution. -/
theorem projective_standard_fixer_is_linear [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (α : MulAut PSL(3,F)) (hα : α ∈ standard F)
    (hstable : (unipotent F).map α.toMonoidHom = unipotent F)
    (hpow : α ^ (2 ^ k) = 1)
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSylow F (by omega) hF)) α) :
    α ∈ innerDiagonal F :=
  ResidualLinear.standard_fixer_is_linear hF hn hn2 hn6 α hα hstable hpow
    (fun _ hu => projective_fixer_axis hF hn α hfix hu)

omit [Finite F] in
/-- Projecting a Sylow-preserving SL₃ actor retains Sylow stability. -/
theorem special_actor_projective_stability (α : MulAut SL(3,F))
    (hstable : (unipotentSL F).map α.toMonoidHom = unipotentSL F) :
    (unipotent F).map (centerAction F α).toMonoidHom = unipotent F := by
  have he : (centerAction F α).toMonoidHom.comp (projection F) =
      (projection F).comp α.toMonoidHom := by
    ext x
    rfl
  change ((unipotentSL F).map (projection F)).map _ = (unipotentSL F).map (projection F)
  rw [Subgroup.map_map, he, ← Subgroup.map_map, hstable]

/-- On the actual special linear carrier, every two-power residual fixer has
inner-diagonal projective image. No quotient action formula is assumed. -/
theorem special_standard_fixer_image_is_linear [CharP F 2] {n k : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (α : MulAut SL(3,F)) (hα : centerAction F α ∈ standard F)
    (hstable : (unipotentSL F).map α.toMonoidHom = unipotentSL F)
    (hpow : α ^ (2 ^ k) = 1)
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSLSylow F (by omega) hF)) α) :
    centerAction F α ∈ innerDiagonal F := by
  apply ResidualLinear.standard_fixer_is_linear hF hn hn2 hn6 _ hα
    (special_actor_projective_stability α hstable)
    (show (centerAction F α) ^ (2 ^ k) = 1 by rw [← map_pow, hpow, map_one])
  intro u hu
  have hp := Subgroup.mem_map_of_mem (projection F) (special_fixer_axis hF hn α hfix hu)
  rw [map_mul, map_inv] at hp
  change projection F (α (torusSL F (u,1))) * (projection F (torusSL F (u,1)))⁻¹ ∈
    unipotent F at hp
  exact hp

/-- The standard-coverage input is the earlier full automorphism classification;
the arbitrary two-group actor calculation is proved here. -/
theorem projective_actor_fixer_is_linear [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : standard F = ⊤) (A : Subgroup (MulAut PSL(3,F)))
    (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A (unipotentSylow F (by omega) hF))
    {α : MulAut PSL(3,F)} (hα : α ∈ A)
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSylow F (by omega) hF)) α) :
    α ∈ innerDiagonal F := by
  obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
  exact projective_standard_fixer_is_linear hF hn hn2 hn6 α (by rw [hcover]; trivial)
    (hstable α hα) (congrArg Subtype.val hk) hfix

/-- The same arbitrary two-group calculation on SL₃ retains its actual
central projection and does not identify the cover with PSL₃. -/
theorem special_actor_fixer_image_is_linear [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : standard F = ⊤) (A : Subgroup (MulAut SL(3,F)))
    (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A (unipotentSLSylow F (by omega) hF))
    {α : MulAut SL(3,F)} (hα : α ∈ A)
    (hfix : FixesResidualTorus (intrinsicResidual (unipotentSLSylow F (by omega) hF)) α) :
    centerAction F α ∈ innerDiagonal F := by
  obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
  exact special_standard_fixer_image_is_linear hF hn hn2 hn6 α
    (by rw [hcover]; trivial) (hstable α hα) (congrArg Subtype.val hk) hfix


/-- The source projective actor centralizer, with only the earlier full
standard-automorphism classification retained as a raw input. -/
theorem projective_fixesResidualTorus_iff [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : standard F = ⊤) (S : Sylow 2 PSL(3,F))
    (A : Subgroup (MulAut PSL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A)
    {α : MulAut PSL(3,F)} (hα : α ∈ A) :
    FixesResidualTorus (intrinsicResidual S) α ↔ α ∈ innerSylow S := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, projective_inner_fixes hF hn S⟩
  intro hfix
  obtain ⟨g,hgS,hgB⟩ := sylow_normalizer_conjugate F (by omega) hF S
  let e : PSL(3,F) ≃* PSL(3,F) := MulAut.conj g
  let β : MulAut PSL(3,F) := (MulAut.congr e.symm) α
  obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
  have hk' : α ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hβpow : β ^ (2 ^ k) = 1 := by
    change ((MulAut.congr e.symm) α) ^ (2 ^ k) = 1
    rw [← map_pow, hk', map_one]
  have hβstable : (unipotent F).map β.toMonoidHom = unipotent F :=
    MulAut.aligned_actor_stable e (unipotent F) S hgS α (hstable α hα)
  have hβaxes : ∀ u ∈ pResidual 3 Fˣ,
      β (torusMap F (u,1)) * (torusMap F (u,1))⁻¹ ∈ unipotent F := by
    intro u hu
    apply aligned_actor_displacement e (unipotent F) (borel F) S hgS
      (by rw [projective_residual_eq hF hn]; exact hgB.le)
      (projective_residual_twoCore hF hn S) α hfix
    exact projective_residual_axis hu
  have hlin := ResidualLinear.standard_fixer_is_linear hF hn hn2 hn6 β
    (by rw [hcover]; trivial) hβstable hβpow hβaxes
  obtain ⟨m,hm⟩ := hlin
  have hβinner : β ∈ MulAut.innerSubgroup PSL(3,F) := by
    rw [← hm]
    exact ResidualInner.linearConj_twoPower_inner m (by rwa [hm])
  exact MulAut.mem_innerSylow_of_mem_inner S A hA hinner hα
    (MulAut.inner_of_aligned_inner e α hβinner)

/-- The source special linear actor centralizer. The projective reduction
uses the actual scalar quotient, and perfectness lifts innerness back to SL₃. -/
theorem special_fixesResidualTorus_iff [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) (hn2 : n ≠ 2) (hn6 : n ≠ 6)
    (hcover : standard F = ⊤) (S : Sylow 2 SL(3,F))
    (A : Subgroup (MulAut SL(3,F))) (hA : IsPGroup 2 A)
    (hstable : StabilizesSylow A S) (hinner : innerSylow S ≤ A)
    {α : MulAut SL(3,F)} (hα : α ∈ A) :
    FixesResidualTorus (intrinsicResidual S) α ↔ α ∈ innerSylow S := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, special_inner_fixes hF hn S⟩
  intro hfix
  obtain ⟨g,hgS,hgB⟩ := sylowSL_normalizer_conjugate F (by omega) hF S
  let e : SL(3,F) ≃* SL(3,F) := MulAut.conj g
  let β : MulAut SL(3,F) := (MulAut.congr e.symm) α
  obtain ⟨k,hk⟩ := hA ⟨α,hα⟩
  have hk' : α ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hβpow : β ^ (2 ^ k) = 1 := by
    change ((MulAut.congr e.symm) α) ^ (2 ^ k) = 1
    rw [← map_pow, hk', map_one]
  have hβstable : (unipotentSL F).map β.toMonoidHom = unipotentSL F :=
    MulAut.aligned_actor_stable e (unipotentSL F) S hgS α (hstable α hα)
  have hβaxes : ∀ u ∈ pResidual 3 Fˣ,
      β (torusSL F (u,1)) * (torusSL F (u,1))⁻¹ ∈ unipotentSL F := by
    intro u hu
    apply aligned_actor_displacement e (unipotentSL F) (borelSL F) S hgS
      (by rw [special_residual_eq hF hn]; exact hgB.le)
      (special_residual_twoCore hF hn S) α hfix
    exact special_residual_axis hu
  have hcpow : centerAction F β ^ (2 ^ k) = 1 := by rw [← map_pow, hβpow, map_one]
  have hlin : centerAction F β ∈ innerDiagonal F := by
    apply ResidualLinear.standard_fixer_is_linear hF hn hn2 hn6 _
      (by rw [hcover]; trivial) (special_actor_projective_stability β hβstable) hcpow
    intro u hu
    have hp := Subgroup.mem_map_of_mem (projection F) (hβaxes u hu)
    rw [map_mul, map_inv] at hp
    change projection F (β (torusSL F (u,1))) * (projection F (torusSL F (u,1)))⁻¹ ∈
      unipotent F at hp
    exact hp
  obtain ⟨m,hm⟩ := hlin
  have hcinner : centerAction F β ∈ MulAut.innerSubgroup PSL(3,F) := by
    rw [← hm]
    exact ResidualInner.linearConj_twoPower_inner m (by rwa [hm])
  have hβinner := ResidualInner.special_inner_of_projective_inner β hcinner
  exact MulAut.mem_innerSylow_of_mem_inner S A hA hinner hα
    (MulAut.inner_of_aligned_inner e α hβinner)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.LinearThree
