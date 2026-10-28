module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure

/-!
# Cubic coefficient actions on the actual triality parabolics

The coefficient action on the elementary central quotient preserves both
root parabolics, their prime-to-p residuals, radicals and Levi complements.
It therefore acts on the literal local two-core quotients. Equivariance of
the Levi projection connects those actions to the original root Levi groups.

The invariance proofs adapt the saved outer-two work in
`fa133d5f612b4c2294c41ae1d9ba2604`, using the shared coefficient action now
published in `OuterOddSubgroups.CoefficientAction`.
Source: GLS3 §§2.5–2.6, particularly 2.5.12(d), and Aschbacher–Smith F.1.12,
printed p.264. The coefficient field throughout is GF(q³).
-/

@[expose] public section
noncomputable section

private theorem restrict_mem_iff {G : Type*} [Group G] (e : G ≃* G)
    (H : Subgroup G) (h : ∀ x, e x ∈ H ↔ x ∈ H) :
    H.map e.toMonoidHom = H := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).mpr hy
  · intro hx
    exact ⟨e.symm x, (h _).mp (by simpa using hx), e.apply_symm_apply x⟩

namespace Triality.Standard.Parabolics
open OuterOdd

@[simp] theorem coefficient_positiveRoot (P : Parameters) (e : CoefficientAut P)
    (i : Fin 4) (t : ExtensionField P) :
    coefficientSplit P e (positiveRoot P i t) = positiveRoot P i (e t) :=
  coefficientSplit_positive P e _ t

@[simp] theorem coefficient_negativeRoot (P : Parameters) (e : CoefficientAut P)
    (i : Fin 4) (t : ExtensionField P) :
    coefficientSplit P e (negativeRoot P i t) = negativeRoot P i (e t) :=
  coefficientSplit_negative P e _ t

@[simp] theorem coefficientSplit_weylWord (P : Parameters) (e : CoefficientAut P)
    (i : Fin 4) (t : ExtensionField P) :
    coefficientSplit P e (weylWord P i t) = weylWord P i (e t) := by
  simp only [weylWord, map_mul, coefficient_positiveRoot, coefficient_negativeRoot,
    map_neg, map_inv₀]

@[simp] theorem coefficientSplit_torusWord (P : Parameters) (e : CoefficientAut P)
    (i : Fin 4) (t : (ExtensionField P)ˣ) :
    coefficientSplit P e (torusWord P i t) =
      torusWord P i (Units.map e.toMonoidHom t) := by
  simp [torusWord]

/-- Coefficient automorphisms preserve the positive root subgroup. -/
theorem coefficient_positiveSubgroup (P : Parameters) (e : CoefficientAut P) :
    (positiveSubgroup P).map (coefficientSplit P e).toMonoidHom = positiveSubgroup P := by
  rw [positiveSubgroup, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, t, rfl⟩, rfl⟩
    exact ⟨i, e t, coefficientSplit_positive P e _ t⟩
  · rintro ⟨i, t, rfl⟩
    refine ⟨positiveRoot P i (e.symm t), ⟨i, e.symm t, rfl⟩, ?_⟩
    simp

/-- The torus words and positive curves defining the split Borel are preserved. -/
theorem coefficient_splitBorel (P : Parameters) (e : CoefficientAut P) :
    (splitBorel P).map (coefficientSplit P e).toMonoidHom = splitBorel P := by
  rw [splitBorel, Subgroup.map_sup, coefficient_positiveSubgroup, MonoidHom.map_closure]
  congr 2
  ext x
  constructor
  · rintro ⟨y, ⟨i, t, rfl⟩, rfl⟩
    exact ⟨i, Units.map e.toMonoidHom t, coefficientSplit_torusWord P e i t⟩
  · rintro ⟨i, t, rfl⟩
    refine ⟨torusWord P i (Units.map e.symm.toMonoidHom t),
      ⟨i, Units.map e.symm.toMonoidHom t, rfl⟩, ?_⟩
    have hu : Units.map e.toMonoidHom (Units.map e.symm.toMonoidHom t) = t :=
      Units.ext (e.apply_symm_apply t)
    exact (coefficientSplit_torusWord P e i _).trans (congrArg (torusWord P i) hu)

/-- Both node-orbit parabolics are invariant under all cubic coefficient automorphisms. -/
theorem coefficient_splitParabolic (P : Parameters) (e : CoefficientAut P) (a : Node) :
    (splitParabolic P a).map (coefficientSplit P e).toMonoidHom = splitParabolic P a := by
  rw [splitParabolic, Subgroup.map_sup, coefficient_splitBorel, MonoidHom.map_closure]
  congr 2
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, t, rfl⟩, rfl⟩
    exact ⟨i, hi, e t, coefficientSplit_negative P e _ t⟩
  · rintro ⟨i, hi, t, rfl⟩
    refine ⟨negativeRoot P i (e.symm t), ⟨i, hi, e.symm t, rfl⟩, ?_⟩
    simp

/-- Invariant split subgroups remain invariant after restriction and central quotient. -/
theorem coefficient_descendSubgroup (P : Parameters) (e : CoefficientAut P)
    (H : Subgroup (SplitGroup P))
    (hH : H.map (coefficientSplit P e).toMonoidHom = H) :
    (descendSubgroup P H).map (coefficientCarrier P e).toMonoidHom = descendSubgroup P H := by
  have hiff (x : SplitGroup P) : coefficientSplit P e x ∈ H ↔ x ∈ H := by
    constructor
    · intro hx
      rw [← hH] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (coefficientSplit P e).injective he ▸ hy
    · intro hx
      rw [← hH]
      exact ⟨x, hx, rfl⟩
  have hi : (H.comap (elementaryInclusion P)).map
      (coefficientElementary P e).toMonoidHom = H.comap (elementaryInclusion P) := by
    apply restrict_mem_iff
    intro x
    change elementaryInclusion P (coefficientElementary P e x) ∈ H ↔
      elementaryInclusion P x ∈ H
    exact hiff (elementaryInclusion P x)
  have hc : (coefficientCarrier P e).toMonoidHom.comp (toCarrier P) =
      (toCarrier P).comp (coefficientElementary P e).toMonoidHom := by
    ext x
    exact coefficientCarrier_toCarrier P e x
  change ((H.comap (elementaryInclusion P)).map (toCarrier P)).map _ =
    (H.comap (elementaryInclusion P)).map (toCarrier P)
  calc
    _ = (H.comap (elementaryInclusion P)).map
        ((coefficientCarrier P e).toMonoidHom.comp (toCarrier P)) := Subgroup.map_map _ _ _
    _ = (H.comap (elementaryInclusion P)).map
        ((toCarrier P).comp (coefficientElementary P e).toMonoidHom) := congrArg (fun f => (H.comap (elementaryInclusion P)).map f) hc
    _ = ((H.comap (elementaryInclusion P)).map
        (coefficientElementary P e).toMonoidHom).map (toCarrier P) :=
      (Subgroup.map_map _ _ _).symm
    _ = _ := congrArg (Subgroup.map (toCarrier P)) hi

theorem coefficient_unipotent (P : Parameters) (e : CoefficientAut P) :
    (unipotent P).map (coefficientCarrier P e).toMonoidHom = unipotent P :=
  coefficient_descendSubgroup P e _ (coefficient_positiveSubgroup P e)

theorem coefficient_borel (P : Parameters) (e : CoefficientAut P) :
    (borel P).map (coefficientCarrier P e).toMonoidHom = borel P :=
  coefficient_descendSubgroup P e _ (coefficient_splitBorel P e)

theorem coefficient_parabolic (P : Parameters) (e : CoefficientAut P) (a : Node) :
    (parabolic P a).map (coefficientCarrier P e).toMonoidHom = parabolic P a :=
  coefficient_descendSubgroup P e _ (coefficient_splitParabolic P e a)

/-- Restriction to the actual parabolic in the central quotient. -/
def coefficientParabolic (P : Parameters) (e : CoefficientAut P) (a : Node) :
    parabolic P a ≃* parabolic P a :=
  restrictCoefficientSubgroup (coefficientCarrier P e) _ (coefficient_parabolic P e a)

@[simp] theorem coefficientParabolic_val (P : Parameters) (e : CoefficientAut P)
    (a : Node) (x : parabolic P a) :
    (coefficientParabolic P e a x : Carrier P) = coefficientCarrier P e x := rfl

/-- The actual embedded O^{p′} local factors are coefficient invariant. -/
theorem coefficient_localFactor (P : Parameters) (e : CoefficientAut P) (a : Node) :
    (localFactor P a).map (coefficientCarrier P e).toMonoidHom = localFactor P a := by
  have hc : (coefficientCarrier P e).toMonoidHom.comp (parabolic P a).subtype =
      (parabolic P a).subtype.comp (coefficientParabolic P e a).toMonoidHom := rfl
  rw [localFactor, Subgroup.map_map, hc, ← Subgroup.map_map, Subgroup.map_primeToResidual]

/-- The resulting automorphism of each local factor, with its original embedding. -/
def coefficientLocalFactor (P : Parameters) (e : CoefficientAut P) (a : Node) :
    localFactor P a ≃* localFactor P a :=
  restrictCoefficientSubgroup (coefficientCarrier P e) _ (coefficient_localFactor P e a)

@[simp] theorem coefficientLocalFactor_val (P : Parameters) (e : CoefficientAut P)
    (a : Node) (x : localFactor P a) :
    (coefficientLocalFactor P e a x : Carrier P) = coefficientCarrier P e x := rfl


/-- The split root Levi is coefficient invariant, without any field restriction. -/
theorem coefficient_splitLevi (P : Parameters) (e : CoefficientAut P) (a : Node) :
    (splitLevi P a).map (coefficientSplit P e).toMonoidHom = splitLevi P a := by
  rw [splitLevi, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨i, hi, t, rfl | rfl⟩, rfl⟩
    · exact ⟨i, hi, e t, Or.inl (coefficient_positiveRoot P e i t)⟩
    · exact ⟨i, hi, e t, Or.inr (coefficient_negativeRoot P e i t)⟩
  · rintro ⟨i, hi, t, rfl | rfl⟩
    · exact ⟨positiveRoot P i (e.symm t), ⟨i, hi, e.symm t, Or.inl rfl⟩, by simp⟩
    · exact ⟨negativeRoot P i (e.symm t), ⟨i, hi, e.symm t, Or.inr rfl⟩, by simp⟩

theorem coefficient_levi (P : Parameters) (e : CoefficientAut P) (a : Node) :
    (levi P a).map (coefficientCarrier P e).toMonoidHom = levi P a :=
  coefficient_descendSubgroup P e _ (coefficient_splitLevi P e a)

/-- Restriction to the original root Levi subgroup. -/
def coefficientLevi (P : Parameters) (e : CoefficientAut P) (a : Node) :
    levi P a ≃* levi P a :=
  restrictCoefficientSubgroup (coefficientCarrier P e) _ (coefficient_levi P e a)

@[simp] theorem coefficientLevi_val (P : Parameters) (e : CoefficientAut P)
    (a : Node) (x : levi P a) :
    (coefficientLevi P e a x : Carrier P) = coefficientCarrier P e x := rfl

/-- Radicals are preserved in the actual carrier, through their proved core identity. -/
theorem coefficient_radical (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (a : Node) :
    (radical P a).map (coefficientCarrier P e).toMonoidHom = radical P a := by
  have hc : (coefficientCarrier P e).toMonoidHom.comp (localFactor P a).subtype =
      (localFactor P a).subtype.comp (coefficientLocalFactor P e a).toMonoidHom := rfl
  calc
    _ = ((pCore 2 (localFactor P a)).map (localFactor P a).subtype).map
        (coefficientCarrier P e).toMonoidHom :=
      congrArg (Subgroup.map (coefficientCarrier P e).toMonoidHom)
        (localFactor_twoCore_map P hp a).symm
    _ = (pCore 2 (localFactor P a)).map
        ((coefficientCarrier P e).toMonoidHom.comp (localFactor P a).subtype) :=
      Subgroup.map_map _ _ _
    _ = (pCore 2 (localFactor P a)).map
        ((localFactor P a).subtype.comp (coefficientLocalFactor P e a).toMonoidHom) :=
      congrArg (fun f => (pCore 2 (localFactor P a)).map f) hc
    _ = ((pCore 2 (localFactor P a)).map
        (coefficientLocalFactor P e a).toMonoidHom).map (localFactor P a).subtype :=
      (Subgroup.map_map _ _ _).symm
    _ = (pCore 2 (localFactor P a)).map (localFactor P a).subtype :=
      congrArg (Subgroup.map (localFactor P a).subtype)
        (pCore_map_iso 2 (coefficientLocalFactor P e a))
    _ = _ := localFactor_twoCore_map P hp a

/-- The coefficient action commutes with the literal Levi projection. -/
theorem coefficient_localLeviProjection (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (a : Node) (g : localFactor P a) :
    localLeviProjection P hp a (coefficientLocalFactor P e a g) =
      coefficientLevi P e a (localLeviProjection P hp a g) := by
  let π := localLeviProjection P hp a
  let i := Subgroup.inclusion (RadicalCoordinates.levi_le_localFactor P hp a)
  have hk : g / i (π g) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_div, localLeviProjection_inclusion, div_self']
  have hk' : coefficientLocalFactor P e a (g / i (π g)) ∈ π.ker := by
    rw [localLeviProjection_ker] at hk ⊢
    exact (coefficient_radical P hp e a).le
      ⟨(g / i (π g) : localFactor P a).val, hk, rfl⟩
  have he : coefficientLocalFactor P e a (i (π g)) =
      i (coefficientLevi P e a (π g)) := rfl
  rw [MonoidHom.mem_ker, map_div, map_div, he, localLeviProjection_inclusion] at hk'
  exact div_eq_one.mp hk'

/-- The intrinsic quotient of the local factor by its own two-core. -/
abbrev LocalTwoQuotient (P : Parameters) (a : Node) :=
  localFactor P a ⧸ pCore 2 (localFactor P a)

/-- Coefficient action on the literal local quotient. -/
def coefficientLocalTwoQuotient (P : Parameters) (e : CoefficientAut P) (a : Node) :
    LocalTwoQuotient P a ≃* LocalTwoQuotient P a :=
  QuotientGroup.congr _ _ (coefficientLocalFactor P e a)
    (pCore_map_iso 2 (coefficientLocalFactor P e a))

@[simp] theorem coefficientLocalTwoQuotient_mk (P : Parameters) (e : CoefficientAut P)
    (a : Node) (g : localFactor P a) :
    coefficientLocalTwoQuotient P e a (QuotientGroup.mk' (pCore 2 (localFactor P a)) g) =
      QuotientGroup.mk' (pCore 2 (localFactor P a)) (coefficientLocalFactor P e a g) := rfl

/-- The established quotient-to-Levi equivalence sends representatives to the projection. -/
theorem localFactorQuotientEquivLevi_mk (P : Parameters) (hp : P.prime = 2)
    (a : Node) (g : localFactor P a) :
    localFactorQuotientEquivLevi P hp a (QuotientGroup.mk' (pCore 2 (localFactor P a)) g) =
      localLeviProjection P hp a g := rfl

/-- Compatibility uses the actual quotient map and root Levi, rather than an abstract model tag. -/
theorem coefficientLocalTwoQuotient_equivLevi (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (a : Node) (x : LocalTwoQuotient P a) :
    localFactorQuotientEquivLevi P hp a (coefficientLocalTwoQuotient P e a x) =
      coefficientLevi P e a (localFactorQuotientEquivLevi P hp a x) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (localFactor P a)) x
  rw [coefficientLocalTwoQuotient_mk, localFactorQuotientEquivLevi_mk,
    localFactorQuotientEquivLevi_mk]
  exact coefficient_localLeviProjection P hp e a g

end Triality.Standard.Parabolics
