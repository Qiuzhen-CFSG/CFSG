module
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.FixedCopy

/-!
# Normalizer action in the literal central quotient

The normalizer representation on V/C_V(X) restricts to the published
X-representation. Reindexing X as a normal subgroup of its normalizer gives
an actual order action on subrepresentations and transports actual module
isomorphisms. Left images use rho(t); source right conjugates use rho(t⁻¹).

Source: Aschbacher–Smith, Definition A.1.40 and Lemma A.1.42, printed pp.31–32.
-/
@[expose] public section
noncomputable section
namespace Representation.BinaryOffender.Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Reindex X as its actual normal subgroup inside N_G(X). -/
def centralRestrictionOrderIso (X : Subgroup G) :
    Subrepresentation (fixedQuotientRepresentation ρ X) ≃o
      Subrepresentation ((normalizerQuotientRepresentation ρ X).comp
        (X.subgroupOf (Subgroup.normalizer X)).subtype) where
  toFun A := ⟨A.toSubmodule, fun x _ hv =>
    A.apply_mem_toSubmodule ⟨x.val.val, x.property⟩ hv⟩
  invFun A := ⟨A.toSubmodule, fun x _ hv =>
    A.apply_mem_toSubmodule ⟨⟨x.val, X.le_normalizer x.property⟩, x.property⟩ hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

private theorem sameModule_centralRestriction_iff (X : Subgroup G)
    (A B : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    SameModule (centralRestrictionOrderIso ρ X A) (centralRestrictionOrderIso ρ X B) ↔
      SameModule A B := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, fun x => he ⟨⟨x.val, X.le_normalizer x.property⟩, x.property⟩⟩
  · rintro ⟨e, he⟩
    exact ⟨e, fun x => he ⟨x.val.val, x.property⟩⟩

/-- The action is the actual normalizer action, transported only across the
canonical identification of X with X inside its normalizer. -/
def centralTypeAction (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X) :
    TypeAction (fixedQuotientRepresentation ρ X) T where
  conjugate t := (centralRestrictionOrderIso ρ X).trans
    ((conjugateSubrepresentationOrderIso (normalizerQuotientRepresentation ρ X)
      (X.subgroupOf (Subgroup.normalizer X)) ⟨t.val, hT t.property⟩).trans
        (centralRestrictionOrderIso ρ X).symm)
  one A := by
    simp only [OrderIso.trans_apply]
    change (centralRestrictionOrderIso ρ X).symm
      (conjugateSubrepresentationOrderIso _ _ 1 (centralRestrictionOrderIso ρ X A)) = A
    rw [conjugateSubrepresentationOrderIso_one, OrderIso.symm_apply_apply]
  mul t u A := by
    simp only [OrderIso.trans_apply, OrderIso.apply_symm_apply]
    rw [← conjugateSubrepresentationOrderIso_mul]
    rfl
  same t A B := by
    simp only [OrderIso.trans_apply]
    have h := isaacs_6_5_nonempty_repEquiv_conjugateOrderIso_iff
      (normalizerQuotientRepresentation ρ X) (X.subgroupOf (Subgroup.normalizer X))
      ⟨t.val, hT t.property⟩ (centralRestrictionOrderIso ρ X A) (centralRestrictionOrderIso ρ X B)
    rw [← sameModule_iff_repEquiv, ← sameModule_iff_repEquiv] at h
    rw [sameModule_centralRestriction_iff] at h
    apply h.trans
    simpa only [OrderIso.apply_symm_apply] using (sameModule_centralRestriction_iff ρ X
      ((centralRestrictionOrderIso ρ X).symm
        (conjugateSubrepresentationOrderIso _ _ ⟨t.val,hT t.property⟩
          (centralRestrictionOrderIso ρ X A)))
      ((centralRestrictionOrderIso ρ X).symm
        (conjugateSubrepresentationOrderIso _ _ ⟨t.val,hT t.property⟩
          (centralRestrictionOrderIso ρ X B))))

/-- The actual translated central image. -/
abbrev centralConjugate (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (t : T) (A : Subrepresentation (fixedQuotientRepresentation ρ X)) :=
  (centralTypeAction ρ X T hT).conjugate t A

theorem centralConjugate_toSubmodule (X T : Subgroup G)
    (hT : T ≤ Subgroup.normalizer X) (t : T)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    (centralConjugate ρ X T hT t A).toSubmodule =
      A.toSubmodule.map (normalizerQuotientRepresentation ρ X ⟨t.val, hT t.property⟩) := by
  change (conjugateSubrepresentationOrderIso _ _ _
    (centralRestrictionOrderIso ρ X A)).toSubmodule = _
  rw [conjugateSubrepresentationOrderIso_toSubmodule]
  rfl

theorem centralTypeAction_span (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) :
    ((centralTypeAction ρ X T hT).span A).toSubmodule =
      centralOrbitSpan ρ X T hT A.toSubmodule := by
  rw [TypeAction.span, toSubmodule_iSup]
  exact iSup_congr fun t => centralConjugate_toSubmodule ρ X T hT t A

/-- Source right conjugates are images under inverse normalizer operators. -/
def centralRightConjugate (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) (t : T) :=
  centralConjugate ρ X T hT t⁻¹ A

theorem centralRightConjugate_toSubmodule (X T : Subgroup G)
    (hT : T ≤ Subgroup.normalizer X)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) (t : T) :
    (centralRightConjugate ρ X T hT A t).toSubmodule =
      A.toSubmodule.map (normalizerQuotientRepresentation ρ X ⟨t.val⁻¹, hT (T.inv_mem t.property)⟩) :=
  centralConjugate_toSubmodule ρ X T hT t⁻¹ A

theorem centralRightConjugate_mul (X T : Subgroup G) (hT : T ≤ Subgroup.normalizer X)
    (A : Subrepresentation (fixedQuotientRepresentation ρ X)) (t u : T) :
    centralRightConjugate ρ X T hT A (t * u) =
      centralRightConjugate ρ X T hT (centralRightConjugate ρ X T hT A t) u := by
  change (centralTypeAction ρ X T hT).conjugate (t * u)⁻¹ A = _
  rw [mul_inv_rev, TypeAction.mul]
  rfl

end Representation.BinaryOffender.Homogeneous
