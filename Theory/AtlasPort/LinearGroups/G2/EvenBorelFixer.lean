module

public import Theory.AtlasPort.LinearGroups.G2.EvenBorelAction

/-!
# Detecting G₂ torus fixers on the field units

Projection identifies fixation of the three-residual modulo the Borel's
two-core with fixation of O³(Fˣ) by the field component. The forward
implication uses the actual first-coordinate torus embedding; the reverse
uses the two coordinate homomorphisms out of the Borel. Functoriality of
prime residuals supplies the residual memberships in both directions.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. This is the exact
model-to-field reduction. The arithmetic exclusion of nontrivial two-power
field automorphisms outside degrees two and six is a separate obligation.
-/

@[expose] public section
namespace Atlas.G2.EvenBorelTorus
open Subgroup LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Fixation of the actual three-residual modulo the intrinsic two-core. -/
def FixesResidualTorus (α : MulAut (Model F)) : Prop :=
  ∀ b : borel (K := F), b ∈ pResidual 3 borel →
    α b.val * b.val⁻¹ ∈ (borel (K := F)).pCoreIn 2

theorem displacement_mem_twoCore_iff (α : MulAut (Model F))
    (hα : borel.map α.toMonoidHom = borel) (b : borel (K := F)) :
    α b.val * b.val⁻¹ ∈ (borel (K := F)).pCoreIn 2 ↔
      projection (restrictActor α hα b) = projection b := by
  rw [twoCoreIn_eq_unipotent]
  have h : α b.val * b.val⁻¹ ∈ unipotent ↔
      restrictActor α hα b * b⁻¹ ∈ (projection (F := F)).ker := by
    rw [projection_ker]
    rfl
  rw [h, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

/-- The intrinsic quotient convention agrees with the explicit projection. -/
theorem fixesResidualTorus_iff_projection (α : MulAut (Model F))
    (hα : borel.map α.toMonoidHom = borel) :
    FixesResidualTorus α ↔ ∀ b ∈ pResidual 3 (borel (K := F)),
      projection (restrictActor α hα b) = projection b := by
  unfold FixesResidualTorus
  apply forall_congr'
  intro b
  apply forall_congr'
  intro _
  rw [twoCoreIn_eq_unipotent]
  have h : α b.val * b.val⁻¹ ∈ unipotent ↔
      restrictActor α hα b * b⁻¹ ∈ (projection (F := F)).ker := by
    rw [projection_ker]
    rfl
  rw [h, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]

/-- The actor fixes the residual torus exactly when its field part fixes
O³(Fˣ). Both directions use homomorphisms of the actual Borel. -/
theorem semilinear_fixesResidualTorus_iff
    (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent) :
    FixesResidualTorus (semilinearAction z) ↔
      ∀ u ∈ pResidual 3 Fˣ, Units.map z.right.toMonoidHom u = u := by
  rw [fixesResidualTorus_iff_projection _ (semilinear_map_borel z hz)]
  constructor
  · intro h u hu
    let f : Fˣ →* borel (K := F) := torusSection.comp (MonoidHom.inl Fˣ Fˣ)
    have hf : f u ∈ pResidual 3 (borel (K := F)) :=
      map_pResidual_le 3 f (mem_map_of_mem f hu)
    have he := h (f u) hf
    rw [projection_semilinear z hz] at he
    have hp : projection (f u) = (u,1) := projection_torus (u,1)
    rw [hp] at he
    exact congrArg Prod.fst he
  · intro h b hb
    have hfst : (projection b).1 ∈ pResidual 3 Fˣ :=
      map_pResidual_le 3 ((MonoidHom.fst Fˣ Fˣ).comp projection)
        (mem_map_of_mem _ hb)
    have hsnd : (projection b).2 ∈ pResidual 3 Fˣ :=
      map_pResidual_le 3 ((MonoidHom.snd Fˣ Fˣ).comp projection)
        (mem_map_of_mem _ hb)
    rw [projection_semilinear z hz, h _ hfst, h _ hsnd]

/-- Including the two-core in the numerator gives exactly the source
O³(B)O₂(B)/O₂(B) convention. -/
theorem semilinear_fixes_fullSection_iff
    (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent) :
    (∀ x ∈ (pResidual 3 (borel (K := F))).map borel.subtype ⊔ borel.pCoreIn 2,
      semilinearAction z x * x⁻¹ ∈ borel.pCoreIn 2) ↔
      ∀ u ∈ pResidual 3 Fˣ, Units.map z.right.toMonoidHom u = u := by
  rw [← semilinear_fixesResidualTorus_iff z hz]
  constructor
  · intro h b hb
    exact h b.val (mem_sup_left (mem_map_of_mem borel.subtype hb))
  · intro h
    let a := restrictActor (semilinearAction z) (semilinear_map_borel z hz)
    let E := (projection.comp a.toMonoidHom).eqLocus projection
    have hR : (pResidual 3 (borel (K := F))).map borel.subtype ≤ E.map borel.subtype := by
      rintro x ⟨b,hb,rfl⟩
      exact ⟨b,(displacement_mem_twoCore_iff (semilinearAction z)
        (semilinear_map_borel z hz) b).mp (h b hb),rfl⟩
    have hU : (borel (K := F)).pCoreIn 2 ≤ E.map borel.subtype := by
      intro x hx
      have hxU : x ∈ unipotent := by rwa [twoCoreIn_eq_unipotent] at hx
      have hxB : x ∈ borel := (le_sup_left : unipotent ≤ borel) hxU
      have haxU : semilinearAction z x ∈ unipotent := by
        rw [← hz]
        exact mem_map_of_mem _ hxU
      refine ⟨⟨x,hxB⟩,?_,rfl⟩
      apply (displacement_mem_twoCore_iff (semilinearAction z)
        (semilinear_map_borel z hz) ⟨x,hxB⟩).mp
      rw [twoCoreIn_eq_unipotent]
      exact unipotent.mul_mem haxU (unipotent.inv_mem hxU)
    intro x hx
    obtain ⟨b,hb,rfl⟩ := sup_le hR hU hx
    exact (displacement_mem_twoCore_iff (semilinearAction z)
      (semilinear_map_borel z hz) b).mpr hb

/-- Two-power order in the actual automorphism image implies two-power
order of the field part, using faithfulness of the semilinear action. -/
theorem field_part_two_power (hq : 2 < Nat.card F)
    (z : Model F ⋊[fieldAction] (F ≃+* F)) (k : ℕ)
    (hk : semilinearAction z ^ (2 ^ k) = 1) : z.right ^ (2 ^ k) = 1 := by
  have he : z ^ (2 ^ k) = 1 := semilinearAction_injective hq
    (by simpa only [map_pow, map_one] using hk)
  rw [← SemidirectProduct.rightHom_eq_right, ← map_pow, he, map_one]

/-- For two-elements, trivial field part is equivalent to belonging to
the actual inner image of the specified standard Sylow subgroup. -/
theorem inner_sylow_iff_field_part_one (hq : 2 < Nat.card F)
    (z : Model F ⋊[fieldAction] (F ≃+* F))
    (hz : unipotent.map (semilinearAction z).toMonoidHom = unipotent)
    (k : ℕ) (hk : semilinearAction z ^ (2 ^ k) = 1) :
    semilinearAction z ∈ unipotent.map (MulAut.conj : Model F →* MulAut (Model F)) ↔
      z.right = 1 := by
  constructor
  · rintro ⟨u,_,hu⟩
    have he : semilinearAction z = semilinearAction (SemidirectProduct.inl u) := hu.symm
    exact congrArg SemidirectProduct.right (semilinearAction_injective hq he)
  · intro hσ
    have he : semilinearAction z = MulAut.conj z.left := by
      rw [semilinearAction_apply, hσ, map_one, mul_one]
    refine ⟨z.left,?_,he.symm⟩
    apply inner_two_element_mem_unipotent hq ⟨z.left,semilinear_inner_mem_borel z hz⟩ k
    rwa [← he]

end Atlas.G2.EvenBorelTorus
