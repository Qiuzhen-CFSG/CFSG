module
public import Theory.Representation.SL3FourNaturalDual.CentralSections
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.SpecificGroups.PSL3Even.GraphRemarking
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.Group

/-!
# Two translates of a homogeneous natural SL₃(4) constituent

Every automorphism of the full SL₃(4) has a linear-field form, optionally
followed by inverse transpose. This follows from the proved projective
coverage and faithfulness of the central-quotient action of a perfect group;
the scalar center is retained. Linear and field coordinates preserve the
binary natural module. Their actual intertwiners form a subgroup.

Homogeneity turns these intertwiners on the central image into equality of
literal Irr⁺ constituents. Two automorphisms in the graph coset differ by
one preserving the natural module. Thus, in the presence of a specified
graph actor, the entire normalizer orbit is the sum of the chosen constituent
and its translate by that actor. This does not assume that the orbit spans
the ambient module; the source application supplies that separate equality.

Source: Aschbacher–Smith, A.1.40–42 and 13.8.20, printed pp.31–32 and955;
GLS3, Theorem 2.5.12(a,e). The imported field transport and elementary
perfectness retain their ATLAS attribution and license.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Matrix Matrix.PSL3.OuterSolvable
open scoped MatrixGroups
namespace Representation.SL3FourNaturalDual.HomogeneousOrbit

private theorem centerAction_injective : Function.Injective (centerAction F) := by
  let : Group.IsPerfect SL := Atlas.sl_perfect 3 (by decide)
  have he : centerAction F = Subgroup.quotientAut (Subgroup.center SL) := by
    ext a x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) x
    change centerAction F a (QuotientGroup.mk y) = _
    rw [centerAction_mk,Subgroup.quotientAut_apply_mk]
    rfl
  rw [he]
  exact MulAut.quotient_center_injective

private theorem fieldAction_eq (σ : F ≃+* F) :
    centerAction F (Atlas.fieldEquivSL 3 σ) = fieldAction F σ := by
  ext x
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) x
  change QuotientGroup.mk (Atlas.fieldEquivSL 3 σ y) =
    fieldAction F σ (QuotientGroup.mk y)
  rw [fieldAction_mk]
  rfl

/-- Every automorphism of the full special linear group has a linear-field
form, optionally followed by inverse transpose. The scalar center is retained. -/
theorem automorphism_form (α : MulAut SL) :
    ∃ (m : GL (Fin 3) F) (σ : F ≃+* F),
      α = linearConjSL F m * Atlas.fieldEquivSL 3 σ ∨
      α = linearConjSL F m * Atlas.fieldEquivSL 3 σ * graphSL F := by
  have hcover := Matrix.PSL3Even.AutomorphismCoverage.standard_eq_top F
    (n := 2) (by decide) (by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]; decide)
  obtain ⟨m,σ,h | h⟩ := Matrix.PSL3.CartanActions.NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph (centerAction F α)
      (hcover ▸ mem_top _)
  · refine ⟨m,σ,Or.inl ?_⟩
    apply centerAction_injective
    simpa only [map_mul,fieldAction_eq,linearConj,MonoidHom.comp_apply] using h
  · refine ⟨m,σ,Or.inr ?_⟩
    apply centerAction_injective
    simpa only [map_mul,fieldAction_eq,linearConj,MonoidHom.comp_apply,graph] using h

/-- Entrywise field transport is binary linear. -/
def fieldCoordinates (σ : F ≃+* F) : W ≃ₗ[ZMod 2] W where
  toFun v := fun i => σ (v i)
  invFun v := fun i => σ.symm (v i)
  left_inv v := by funext i; exact σ.symm_apply_apply (v i)
  right_inv v := by funext i; exact σ.apply_symm_apply (v i)
  map_add' v w := by funext i; exact σ.map_add (v i) (w i)
  map_smul' c v := by funext i; exact ZMod.map_smul σ.toAddMonoidHom c (v i)

theorem fieldCoordinates_intertwines (σ : F ≃+* F) (g : SL) (v : W) :
    fieldCoordinates σ (natural g v) =
      natural (Atlas.fieldEquivSL 3 σ g) (fieldCoordinates σ v) := by
  funext i
  change σ (∑ j, g.val i j * v j) = ∑ j, σ (g.val i j) * σ (v j)
  simp only [map_sum,map_mul]

/-- A linear-field automorphism preserves the marked binary natural module. -/
def semilinearCoordinates (m : GL (Fin 3) F) (σ : F ≃+* F) : W ≃ₗ[ZMod 2] W :=
  (fieldCoordinates σ).trans (matrixCoordinates m)

theorem semilinearCoordinates_intertwines (m : GL (Fin 3) F) (σ : F ≃+* F)
    (g : SL) (v : W) :
    semilinearCoordinates m σ (natural g v) =
      natural ((linearConjSL F m * Atlas.fieldEquivSL 3 σ) g)
        (semilinearCoordinates m σ v) := by
  change matrixCoordinates m (fieldCoordinates σ (natural g v)) = _
  rw [fieldCoordinates_intertwines]
  exact (natural_linearConj m _ _).symm

/-- Automorphisms preserving the binary natural module, through actual intertwiners. -/
def naturalStabilizer : Subgroup (MulAut SL) where
  carrier := {α | ∃ c : W ≃ₗ[ZMod 2] W,
    ∀ g v, c (natural g v) = natural (α g) (c v)}
  one_mem' := ⟨LinearEquiv.refl _ _,fun _ _ => rfl⟩
  mul_mem' := by
    rintro α β ⟨a,ha⟩ ⟨b,hb⟩
    refine ⟨b.trans a,fun g v => ?_⟩
    change a (b (natural g v)) = natural (α (β g)) (a (b v))
    rw [hb,ha]
  inv_mem' := by
    rintro α ⟨a,ha⟩
    refine ⟨a.symm,fun g v => ?_⟩
    apply a.injective
    change a (a.symm (natural g v)) = a (natural (α.symm g) (a.symm v))
    rw [a.apply_symm_apply,ha,α.apply_symm_apply,a.apply_symm_apply]

theorem linear_mem_naturalStabilizer (m : GL (Fin 3) F) :
    linearConjSL F m ∈ naturalStabilizer :=
  ⟨matrixCoordinates m,fun g v => (natural_linearConj m g v).symm⟩

theorem semilinear_mem_naturalStabilizer (m : GL (Fin 3) F) (σ : F ≃+* F) :
    linearConjSL F m * Atlas.fieldEquivSL 3 σ ∈ naturalStabilizer :=
  ⟨semilinearCoordinates m σ,semilinearCoordinates_intertwines m σ⟩

variable {G U : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) G U) {K P : Subgroup G}
  {I : Submodule (ZMod 2) U}

private theorem map_eq_of_natural_twist
    (hI : Homogeneous.IsIrrPlusWith ρ K P I) (e : K ≃* SL)
    (n : NaturalCentralSection ρ K e I) (s : P)
    (hs : (MulAut.congr e) (K.normalizerMonoidHom
      ⟨(s : G)⁻¹,hI.normalizes (P.inv_mem s.property)⟩) ∈ naturalStabilizer) :
    I.map (ρ s.val) = I := by
  let Q := Homogeneous.quotientImage ρ K I hI.invariant
  let q : Q.toSubmodule ≃ₗ[ZMod 2] W :=
    (Homogeneous.centralQuotientImageEquiv ρ K I).symm.trans n.coordinates
  have hq (k : K) (v : Q.toSubmodule) :
      q (Q.toRepresentation k v) = natural (e k) (q v) := by
    let q₀ := Homogeneous.centralQuotientImageEquiv ρ K I
    obtain ⟨w,rfl⟩ := q₀.surjective v
    rw [←Homogeneous.centralQuotientImageEquiv_equivariant ρ K I hI.invariant]
    change n.coordinates (q₀.symm (q₀ (centralQuotientRepresentation ρ K I hI.invariant k w))) =
      natural (e k) (n.coordinates (q₀.symm (q₀ w)))
    simpa only [q₀.symm_apply_apply] using n.equivariant k w
  obtain ⟨c,hc⟩ := hs
  apply hI.map_eq_of_central_twist ρ s (q.trans (c.trans q.symm))
  intro k v
  apply q.injective
  change q (q.symm (c (q (Q.toRepresentation k v)))) =
    q (Q.toRepresentation _ (q.symm (c (q v))))
  rw [q.apply_symm_apply,hq,hq,q.apply_symm_apply,hc]
  congr 2
  simp only [MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply]

/-- A homogeneous natural constituent has just two possible translates under
any normalizing subgroup containing the specified linear-graph actor. -/
theorem natural_conjugates
    (hI : Homogeneous.IsIrrPlusWith ρ K P I) (e : K ≃* SL)
    (n : NaturalCentralSection ρ K e I) (t : P) (m : GL (Fin 3) F)
    (ht : ∀ g, (e.symm g : G) * t.val = t.val *
      (e.symm (linearConjSL F m (SpecialLinearGroup.inverseTranspose g)) : G)) :
    ∀ s : P, I.map (ρ s.val) = I ∨ I.map (ρ s.val) = I.map (ρ t.val) := by
  let φ : P →* MulAut SL := (MulAut.congr e).toMonoidHom.comp
    (K.normalizerMonoidHom.comp (inclusion hI.normalizes))
  have htφ : φ t⁻¹ = linearConjSL F m * graphSL F := by
    apply MulEquiv.ext
    intro g
    apply e.symm.injective
    apply Subtype.ext
    change (e.symm (e (K.normalizerMonoidHom
      ⟨t.val⁻¹,hI.normalizes (P.inv_mem t.property)⟩ (e.symm g))) : G) = _
    rw [e.symm_apply_apply,Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp only [inv_inv,MulAut.mul_apply]
    change t.val⁻¹ * (e.symm g : G) * t.val =
      (e.symm (linearConjSL F m (graphSL F g)) : G)
    have hg : graphSL F g = SpecialLinearGroup.inverseTranspose g := by
      apply Subtype.ext
      exact (Matrix.adjugate_transpose g.val).symm
    rw [hg,mul_assoc,ht,inv_mul_cancel_left]
  intro s
  obtain ⟨a,σ,hs | hs⟩ := automorphism_form (φ s⁻¹)
  · exact Or.inl (map_eq_of_natural_twist ρ hI e n s
      (show φ s⁻¹ ∈ naturalStabilizer from hs ▸ semilinear_mem_naturalStabilizer a σ))
  have hr : φ (t⁻¹ * s)⁻¹ ∈ naturalStabilizer := by
    have he : φ (t⁻¹ * s)⁻¹ =
        (linearConjSL F a * Atlas.fieldEquivSL 3 σ) * (linearConjSL F m)⁻¹ := by
      have htinv : φ t = (linearConjSL F m * graphSL F)⁻¹ := by
        rw [←htφ,map_inv,inv_inv]
      rw [_root_.mul_inv_rev,inv_inv,map_mul,hs,htinv]
      group
    rw [he]
    exact naturalStabilizer.mul_mem (semilinear_mem_naturalStabilizer a σ)
      (naturalStabilizer.inv_mem (linear_mem_naturalStabilizer m))
  right
  have he := congrArg (Submodule.map (ρ t.val))
    (map_eq_of_natural_twist ρ hI e n (t⁻¹*s) hr)
  rw [←Submodule.map_comp] at he
  have hm : (ρ t.val).comp (ρ (t⁻¹*s).val) = ρ s.val := by
    change ρ t.val * ρ (t.val⁻¹ * s.val) = ρ s.val
    rw [←map_mul,mul_inv_cancel_left]
  rwa [hm] at he

/-- The whole homogeneous orbit is the sum of the original natural constituent
and its translate by the prescribed graph actor. -/
theorem natural_orbit_span
    (hI : Homogeneous.IsIrrPlusWith ρ K P I) (e : K ≃* SL)
    (n : NaturalCentralSection ρ K e I) (t : P) (m : GL (Fin 3) F)
    (ht : ∀ g, (e.symm g : G) * t.val = t.val *
      (e.symm (linearConjSL F m (SpecialLinearGroup.inverseTranspose g)) : G)) :
    Homogeneous.orbitSpan ρ P I = I ⊔ I.map (ρ t.val) := by
  apply le_antisymm (iSup_le fun s => ?_)
    (sup_le (Homogeneous.le_orbitSpan ρ P I)
      (le_iSup (fun s : P => I.map (ρ s.val)) t))
  rcases natural_conjugates ρ hI e n t m ht s with hs | hs
  · rw [hs]; exact le_sup_left
  · rw [hs]; exact le_sup_right

end Representation.SL3FourNaturalDual.HomogeneousOrbit
