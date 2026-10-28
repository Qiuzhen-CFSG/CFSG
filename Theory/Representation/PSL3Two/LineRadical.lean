module
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Coordinates
public import Theory.Representation.PSL3Two.ParabolicCyclic
public import Theory.Representation.PSL3Two.PointOffenders
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.EquivariantOffender
/-!
# The line radical on the five binary SL₃(2) modules

Two explicit commuting shears have nonzero second displacement on the
trace-zero adjoint module. Together with the existing seven-point core
calculation, this rules out every non-natural H.6.5 alternative when the
whole line radical acts quadratically. A subgroup of that radical with
rank greater than one is the whole radical; the natural alternative has
an explicit transvection. Thus a module with no transvections cannot
have such a quadratic subgroup. The field-sieve source application uses
this on the actual conjugate of its critical subgroup.

Source: Aschbacher–Smith, H.6.5 and 13.8.19, printed pp.388 and 953.
-/

public section
open Matrix Representation Representation.BinaryOffender Subgroup
namespace BinaryLinearThree.LineRadical
private def ra : Group := shear (Multiplicative.ofAdd (1,0))
private def rb : Group := shear (Multiplicative.ofAdd (0,1))
private theorem rai : ra⁻¹ = ra := by apply inv_eq_of_mul_eq_one_right; decide
private theorem rbi : rb⁻¹ = rb := by apply inv_eq_of_mul_eq_one_right; decide
private noncomputable def witness : Steinberg :=
  IrreducibleCatalogue.coordinates.symm ![0,0,0,0,1,0,0,0]

/-- The actual adjoint action is not quadratic on the marked line radical. -/
theorem steinberg_not_quadratic : ¬ IsQuadratic S R := by
  intro h
  have hh := h ra ⟨Multiplicative.ofAdd (1,0),rfl⟩ rb ⟨Multiplicative.ofAdd (0,1),rfl⟩ witness
  have hh' := congrArg (fun f : Steinberg => LinearMap.toMatrix' f.val 1 2) hh
  change LinearMap.toMatrix'
    (W ra ∘ₗ (W rb ∘ₗ witness.val ∘ₗ W rb⁻¹ - witness.val) ∘ₗ W ra⁻¹) 1 2 =
      LinearMap.toMatrix' (W rb ∘ₗ witness.val ∘ₗ W rb⁻¹ - witness.val) 1 2 at hh'
  rw [rai,rbi] at hh'
  have hn : LinearMap.toMatrix'
    (W ra ∘ₗ (W rb ∘ₗ witness.val ∘ₗ W rb - witness.val) ∘ₗ W ra) 1 2 ≠
      LinearMap.toMatrix' (W rb ∘ₗ witness.val ∘ₗ W rb - witness.val) 1 2 := by decide
  exact hn hh'

/-- A subgroup of the marked four-group with rank greater than one fills it. -/
theorem eq_radical_of_rank_gt_one (A : Subgroup Group) (hA : A ≤ R)
    (hr : 1 < rank A) : A = R := by
  by_contra hn
  have hc : Nat.card A < 4 := by
    have hle := Subgroup.card_le_of_le hA
    rw [card_R] at hle
    have hneq : Nat.card A ≠ 4 := by
      intro he
      exact hn (Subgroup.eq_of_le_of_card_ge hA (by rw [card_R,he]))
    omega
  have hlog := Nat.log_lt_of_lt_pow' (b := 2) (by decide : 2 ≠ 0) hc
  change 1 < Nat.log 2 (Nat.card A) at hr
  omega

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

/-- Only the natural H.6.5 alternative allows quadratic action of this radical. -/
theorem natural_of_alternatives_of_quadratic (ρ : Representation (ZMod 2) Group U)
    (h : ParabolicCyclic.Alternatives ρ) (hq : IsQuadratic ρ R) :
    Nonempty (ρ.Equiv W) := by
  have transfer {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
      (σ : Representation (ZMod 2) Group E) (e : ρ.Equiv σ) : IsQuadratic σ R :=
    quadratic_of_equivariant_surjection ρ σ e.toLinearMap e.surjective
      (fun g u => LinearMap.congr_fun (e.isIntertwining' g) u) R hq
  unfold ParabolicCyclic.Alternatives at h
  rcases h with hn | hc | hs | hws | hcs
  · exact hn
  · obtain ⟨e⟩ := hc
    exact (R_not_quadratic (transfer U₂ e)).elim
  · obtain ⟨e⟩ := hs
    exact (steinberg_not_quadratic (transfer S e)).elim
  · obtain ⟨e⟩ := hws
    have hs := quadratic_of_equivariant_surjection (W.prod S) S
      (LinearMap.snd (ZMod 2) Vector Steinberg) (fun v => ⟨((0 : Vector),v),rfl⟩)
      (fun _ _ => rfl) R (transfer _ e)
    exact (steinberg_not_quadratic hs).elim
  · obtain ⟨e⟩ := hcs
    have hs := quadratic_of_equivariant_surjection (U₂.prod S) S
      (LinearMap.snd (ZMod 2) Core Steinberg) (fun v => ⟨((0 : Core),v),rfl⟩)
      (fun _ _ => rfl) R (transfer _ e)
    exact (steinberg_not_quadratic hs).elim

/-- The original natural action has a cyclic actor of fixed codimension one. -/
theorem natural_has_transvection : ∃ g : Group, fixedCodim W (zpowers g) = 1 := by
  let g := Matrix.PSL3Two.PointOffenders.row (Multiplicative.ofAdd (1,0))
  have hg : g ∈ Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    rw [← Matrix.PSL3Two.PointOffenders.row_range]
    exact ⟨_,rfl⟩
  have ho : orderOf g = 2 := orderOf_eq_prime (by decide) (by decide)
  refine ⟨g,?_⟩
  rw [Matrix.PSL3Two.PointOffenders.fixedCodim_eq_rank _ (zpowers_le.mpr hg),
    Representation.BinaryOffender.rank,Nat.card_zpowers,ho]
  decide

/-- H.6.5 and the source critical-rank inequality contradict absence of transvections. -/
theorem no_large_quadratic_of_no_transvections (ρ : Representation (ZMod 2) Group U)
    (h : ParabolicCyclic.Alternatives ρ)
    (hno : ∀ g, fixedCodim ρ (zpowers g) ≠ 1)
    (A : Subgroup Group) (hA : A ≤ R) (hq : IsQuadratic ρ A)
    (hr : 1 < rank A) : False := by
  have he := eq_radical_of_rank_gt_one A hA hr
  obtain ⟨e⟩ := natural_of_alternatives_of_quadratic ρ h (he ▸ hq)
  obtain ⟨g,hg⟩ := natural_has_transvection
  apply hno g
  have hc := fixedCodim_map_equivariant ρ W (MonoidHom.id Group) e.toLinearEquiv
    (fun g u => LinearMap.congr_fun (e.isIntertwining' g) u) (zpowers g)
  simpa only [Subgroup.map_id,hg] using hc
end BinaryLinearThree.LineRadical
