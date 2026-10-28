module
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Quadratic action from a central secondary preimage

For a symplectic two-group in standard flag coordinates, the plane moves
into the point. If the inverse image of that point belongs to Z, the plane
lies in the greatest subgroup whose commutator lies in Z. Centralizing this
preimage therefore fixes the plane pointwise. Orthogonality then puts every
displacement in that plane, proving that the whole action is quadratic.

Source application: MS93 (3.6), printed p.871. The original graph application
retains the actual subgroup action and places the fixed point in Z_beta.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour
variable {G F : Type*} [Group G] [Field F]

theorem quadratic_of_central_secondary_preimage
    (W P Z : Subgroup G) (hn : P ≤ normalizer W)
    (φ : W ≃* Multiplicative (Vector F)) (α : P →* Sp F)
    (hα : ∀ p : P, α p ∈ unipotent)
    (hact : ∀ (p : P) (w : W) (hw : p.val*w.val*p.val⁻¹ ∈ W),
      φ ⟨p.val*w.val*p.val⁻¹,hw⟩ = Multiplicative.ofAdd (α p • (φ w).toAdd))
    (hpoint : ∀ w : W, (φ w).toAdd ∈ point F → (w:G) ∈ Z)
    (hcentral : ⁅commutatorPreimage W P Z,P⁆ = ⊥) :
    ⁅⁅W,P⁆,P⁆ = ⊥ := by
  let A : Subgroup G := ((plane F).toAddSubgroup.toSubgroup.comap φ.toMonoidHom).map W.subtype
  have hAW : A ≤ W := map_subtype_le _
  have hAZ : ⁅A,P⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro p hp w ⟨u,hu,rfl⟩
    have hcw : ⁅p,(u:G)⁆ ∈ W :=
      le_normalizer_iff_commutator_le_right.mp hn (commutator_mem_commutator hp u.property)
    let v : W := ⟨⁅p,(u:G)⁆,hcw⟩
    apply hpoint v
    have he : φ v = φ ⟨p*(u:G)*p⁻¹,
        (mem_normalizer_iff.mp (hn hp) u).mp u.property⟩ * (φ u)⁻¹ := by
      rw [←map_inv,←map_mul]
      rfl
    rw [he,hact ⟨p,hp⟩ u]
    change (φ u).toAdd ∈ plane F at hu
    simpa only [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg] using
      unipotent_trivial_on_plane_mod_point (hα ⟨p,hp⟩) hu
  have hAP : A ≤ commutatorPreimage W P Z := le_commutatorPreimage hAW hAZ
  have hfix : ∀ (p : P) (v : Vector F), v ∈ plane F → α p • v = v := by
    intro p v hv
    let w := φ.symm (Multiplicative.ofAdd v)
    have hwA : (w:G) ∈ A := mem_map_of_mem W.subtype (by
      change (φ w).toAdd ∈ plane F
      simpa only [w,φ.apply_symm_apply,toAdd_ofAdd] using hv)
    have hc := (commutator_eq_bot_iff_le_centralizer.mp hcentral) (hAP hwA) p p.property
    have hconj : (⟨p.val*w.val*p.val⁻¹,
      (mem_normalizer_iff.mp (hn p.property) w).mp w.property⟩ : W) = w := by
      apply Subtype.ext
      change p.val*w.val*p.val⁻¹ = w.val
      rw [hc,mul_inv_cancel_right]
    have he := hact p w ((mem_normalizer_iff.mp (hn p.property) w).mp w.property)
    rw [hconj] at he
    have hh := congrArg Multiplicative.toAdd he
    simpa only [w,φ.apply_symm_apply,toAdd_ofAdd] using hh.symm
  have hcomm : ⁅W,P⁆ ≤ A := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro p hp w hw
    have hcw : ⁅p,w⁆ ∈ W :=
      le_normalizer_iff_commutator_le_right.mp hn (commutator_mem_commutator hp hw)
    let v : W := ⟨⁅p,w⁆,hcw⟩
    apply mem_map_of_mem W.subtype (x := v)
    change (φ v).toAdd ∈ plane F
    have he : φ v = φ ⟨p*w*p⁻¹,
        (mem_normalizer_iff.mp (hn hp) w).mp hw⟩ * (φ ⟨w,hw⟩)⁻¹ := by
      rw [←map_inv,←map_mul]
      rfl
    rw [he,hact ⟨p,hp⟩ ⟨w,hw⟩]
    simpa only [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg] using
      displacement_mem_of_self_orthogonal (plane F) (by
      ext v
      change (∀ u ∈ plane F, form F u v = 0) ↔ v ∈ plane F
      constructor
      · intro h i
        have he := h (Theory.SpecificGroups.SymplecticFour.e i) (e_mem_plane i)
        fin_cases i <;> simpa [form_apply,Theory.SpecificGroups.SymplecticFour.e] using he
      · intro hv u hu
        exact plane_isotropic u v hu hv)
      (α ⟨p,hp⟩) (hfix ⟨p,hp⟩) (φ ⟨w,hw⟩).toAdd
  apply le_bot_iff.mp
  exact (commutator_mono (hcomm.trans hAP) le_rfl).trans_eq hcentral
end Theory.SpecificGroups.SymplecticFour
