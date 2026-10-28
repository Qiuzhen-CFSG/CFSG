module
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.NormalizerActionExistence.Reflections
public import Theory.AlgebraicGroup.RootSubgroups.ReductiveIntegralCoroots
public import Theory.AlgebraicGroup.RootSystems.AffinePath

/-!
# Chambers of the actual torus roots

A realized root datum and a supplied `TorusCharacterRootGeometry` have the same
roots: both index the actual torus characters. We identify their negation and
root additions, then use finite-root reflection rigidity and the datum's existing
cocharacters to identify the Cartan pairings and reflection permutations.

The selected positive system therefore gives a positive subsystem of the supplied
root pairing. Its indecomposable roots are exactly `FundamentalRootsFor D P`.
A base for that subsystem supplies positivity under fundamental reflections.
Weyl transitivity on positive subsystems and generation by the reflections of
this same base supply a word in the published `reflectionGroup hD P` transporting
any other positive system. The proofs do not choose a root and include empty
root systems.

These are the two root-system premises of `nonempty_of_chamber_geometry` in the
parent normalizer-action assembly. Geometric existence of the supplied `R` remains
with that assembly; no additional coroot or chamber witness is assumed here.

Source: GLS3, Chapter 1, §§1.8–1.9 and §1.11; Borel, *Linear Algebraic Groups*,
second edition, §14.7 (printed pp.187–188), §14.8 and §14.15 T2.
-/

universe u
namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} (hD : D.IsRealization)

private noncomputable def actualRootEquiv : D.Root ≃ TorusRootIndex T :=
  Equiv.ofBijective
    (fun α => ⟨D.rootWeight α, by
      change D.rootWeight α ∈ TorusRootSet T
      rw [← hD.2.1]
      exact Set.mem_range_self α⟩)
    ⟨fun α β h => hD.1 (congrArg Subtype.val h), by
      intro χ
      obtain ⟨α, hα⟩ := (hD.2.1 ▸ χ.property : χ.val ∈ Set.range D.rootWeight)
      exact ⟨α, Subtype.ext hα⟩⟩

omit [IsAlgClosed k] in
private theorem actualRootEquiv_val (α : D.Root) :
    (actualRootEquiv hD α).val = D.rootWeight α := rfl

variable (R : TorusCharacterRootGeometry T)

omit [IsAlgClosed k] in
private theorem actualRootEquiv_neg (α : D.Root) :
    actualRootEquiv hD (D.neg α) =
      R.pairing.reflectionPerm (actualRootEquiv hD α) (actualRootEquiv hD α) := by
  apply Subtype.ext
  rw [R.root_neg, actualRootEquiv_val, actualRootEquiv_val, hD.2.2.2.1]

omit [IsAlgClosed k] in
private theorem actualRootEquiv_add_iff (hadd : D.IsRootAdditionComplete)
    (α β γ : D.Root) :
    R.pairing.root (actualRootEquiv hD γ) =
        R.pairing.root (actualRootEquiv hD α) + R.pairing.root (actualRootEquiv hD β) ↔
      D.add α β = some γ := by
  rw [R.root_add_iff]
  exact ⟨hadd α β γ, hD.2.2.2.2.1 α β γ⟩

private theorem actualRootEquiv_pairing (α β : D.Root) :
    (D.pairing α β : ℝ) =
      R.pairing.pairing (actualRootEquiv hD α) (actualRootEquiv hD β) := by
  have htwo : D.characterCorootPairing β
      (Additive.ofMul (actualRootEquiv hD β).val) = 2 := by
    rw [actualRootEquiv_val, hD.characterCorootPairing_rootWeight]
    exact hD.2.2.2.2.2.2.1 β
  have href (χ : TorusRootIndex T) : IsTorusRoot T
      (χ.val * (actualRootEquiv hD β).val ^
        (-D.characterCorootPairing β (Additive.ofMul χ.val))) := by
    obtain ⟨γ, rfl⟩ := (actualRootEquiv hD).surjective χ
    rw [actualRootEquiv_val, actualRootEquiv_val,
      hD.characterCorootPairing_rootWeight, ← hD.2.2.2.2.2.1]
    exact (actualRootEquiv hD (D.reflect β γ)).property
  simpa only [actualRootEquiv_val, hD.characterCorootPairing_rootWeight] using
    R.pairing_eq_of_integral_reflection (actualRootEquiv hD β)
      (D.characterCorootPairing β) htwo href (actualRootEquiv hD α)

private theorem actualRootEquiv_reflect (α β : D.Root) :
    actualRootEquiv hD (D.reflect α β) =
      R.pairing.reflectionPerm (actualRootEquiv hD α) (actualRootEquiv hD β) := by
  apply Subtype.ext
  rw [R.root_reflect _ _ (D.pairing β α) (actualRootEquiv_pairing hD R β α)]
  exact hD.2.2.2.2.2.1 α β

private def actualPositiveSubsystem (hadd : D.IsRootAdditionComplete)
    (P : Set D.Root) (hP : IsPositiveSystem D P) : R.pairing.PositiveSubsystem where
  carrier := (actualRootEquiv hD).symm ⁻¹' P
  add_mem := by
    intro α β γ hα hβ hγ
    obtain ⟨a, rfl⟩ := (actualRootEquiv hD).surjective α
    obtain ⟨b, rfl⟩ := (actualRootEquiv hD).surjective β
    obtain ⟨c, rfl⟩ := (actualRootEquiv hD).surjective γ
    simp only [Set.mem_preimage, Equiv.symm_apply_apply] at hα hβ ⊢
    exact hP.2.2 a hα b hβ c ((actualRootEquiv_add_iff hD R hadd a b c).mp hγ)
  mem_xor_neg := by
    intro α
    obtain ⟨a, rfl⟩ := (actualRootEquiv hD).surjective α
    rw [← actualRootEquiv_neg hD R]
    simp only [Set.mem_preimage, Equiv.symm_apply_apply]
    have hor : a ∈ P ∨ D.neg a ∈ P := by
      have h : a ∈ P ∪ D.neg ⁻¹' P := by rw [hP.2.1]; trivial
      exact h
    have hnot : ¬ (a ∈ P ∧ D.neg a ∈ P) := by
      intro h
      have : a ∈ P ∩ D.neg ⁻¹' P := h
      rw [hP.1] at this
      exact this
    exact hor.elim (fun h => Or.inl ⟨h, fun hn => hnot ⟨h, hn⟩⟩)
      (fun h => Or.inr ⟨h, fun hp => hnot ⟨hp, h⟩⟩)

omit [IsAlgClosed k] in
private theorem actualPositiveSubsystem_mem (hadd : D.IsRootAdditionComplete)
    (P : Set D.Root) (hP : IsPositiveSystem D P) (α : D.Root) :
    actualRootEquiv hD α ∈ actualPositiveSubsystem hD R hadd P hP ↔ α ∈ P := by
  change (actualRootEquiv hD).symm (actualRootEquiv hD α) ∈ P ↔ α ∈ P
  rw [Equiv.symm_apply_apply]

omit [IsAlgClosed k] in
private theorem actualPositiveSubsystem_indecomposable (hadd : D.IsRootAdditionComplete)
    (P : Set D.Root) (hP : IsPositiveSystem D P) (α : D.Root) :
    (actualPositiveSubsystem hD R hadd P hP).IsIndecomposable (actualRootEquiv hD α) ↔
      α ∈ FundamentalRootsFor D P := by
  rw [RootPairing.PositiveSubsystem.isIndecomposable_iff,
    actualPositiveSubsystem_mem hD R hadd P hP]
  constructor
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    intro β hβ γ hγ hsum
    apply h
    exact ⟨actualRootEquiv hD β, actualRootEquiv hD γ,
      (actualPositiveSubsystem_mem hD R hadd P hP β).mpr hβ,
      (actualPositiveSubsystem_mem hD R hadd P hP γ).mpr hγ,
      (actualRootEquiv_add_iff hD R hadd β γ α).mpr hsum⟩
  · rintro ⟨hα, h⟩
    refine ⟨hα, ?_⟩
    rintro ⟨β, γ, hβ, hγ, hsum⟩
    obtain ⟨b, rfl⟩ := (actualRootEquiv hD).surjective β
    obtain ⟨c, rfl⟩ := (actualRootEquiv hD).surjective γ
    exact h b ((actualPositiveSubsystem_mem hD R hadd P hP b).mp hβ)
      c ((actualPositiveSubsystem_mem hD R hadd P hP c).mp hγ)
      ((actualRootEquiv_add_iff hD R hadd b c α).mp hsum)

private theorem exists_actualBase (hadd : D.IsRootAdditionComplete)
    (P : Set D.Root) (hP : IsPositiveSystem D P) :
    ∃ b : R.pairing.Base, b.toPositiveSubsystem = actualPositiveSubsystem hD R hadd P hP := by
  obtain ⟨b⟩ := R.pairing.nonempty_base
  obtain ⟨g, hg⟩ := exists_weylGroup_translate_base_toPositiveSubsystem R.pairing b
    (actualPositiveSubsystem hD R hadd P hP)
  exact ⟨g • b, hg⟩

private theorem actualBase_support (hadd : D.IsRootAdditionComplete)
    (P : Set D.Root) (hP : IsPositiveSystem D P) (b : R.pairing.Base)
    (hb : b.toPositiveSubsystem = actualPositiveSubsystem hD R hadd P hP) (α : D.Root) :
    actualRootEquiv hD α ∈ b.support ↔ α ∈ FundamentalRootsFor D P := by
  rw [base_mem_support_iff_isIndecomposablePositive, hb,
    actualPositiveSubsystem_indecomposable hD R hadd P hP]

include hD R in
/-- A fundamental reflection preserves every other positive root of the supplied
realized datum, with its literal reflection function. -/
public theorem reflect_mem_positive_of_fundamental
    (hadd : D.IsRootAdditionComplete) {P : Set D.Root} (hP : IsPositiveSystem D P)
    (i : {α // α ∈ FundamentalRootsFor D P}) (β : D.Root)
    (hβ : β ∈ P) (hne : β ≠ i.val) : D.reflect i.val β ∈ P := by
  obtain ⟨b, hb⟩ := exists_actualBase hD R hadd P hP
  have hpos (α : D.Root) : b.IsPos (actualRootEquiv hD α) ↔ α ∈ P := by
    rw [← RootPairing.Base.mem_toPositiveSubsystem, hb,
      actualPositiveSubsystem_mem hD R hadd P hP]
  apply (hpos _).mp
  rw [actualRootEquiv_reflect hD R]
  exact ((hpos β).mpr hβ).reflectionPerm
    ((actualBase_support hD R hadd P hP b hb i.val).mpr i.property)
    (fun h => hne ((actualRootEquiv hD).injective h))

private noncomputable def actualWeylAction :
    R.pairing.weylGroup →* Equiv.Perm D.Root :=
  (actualRootEquiv hD).symm.permCongrHom.toMonoidHom.comp R.pairing.weylGroupToPerm

private theorem actualWeylAction_reflection (α : D.Root) :
    actualWeylAction hD R (RootPairing.weylGroup.ofIdx R.pairing (actualRootEquiv hD α)) =
      reflectionPerm hD α := by
  ext β
  rw [reflectionPerm_apply]
  apply (actualRootEquiv hD).injective
  change actualRootEquiv hD ((actualRootEquiv hD).symm
      (R.pairing.reflectionPerm (actualRootEquiv hD α) (actualRootEquiv hD β))) =
    actualRootEquiv hD (D.reflect α β)
  rw [Equiv.apply_symm_apply, actualRootEquiv_reflect hD R]

private theorem actualWeylAction_mem (hadd : D.IsRootAdditionComplete)
    (P : Set D.Root) (hP : IsPositiveSystem D P) (b : R.pairing.Base)
    (hb : b.toPositiveSubsystem = actualPositiveSubsystem hD R hadd P hP)
    (g : R.pairing.weylGroup) : actualWeylAction hD R g ∈ reflectionGroup hD P := by
  obtain ⟨l, rfl⟩ := b.exists_wordProd_eq g
  induction l with
  | nil => simpa only [b.wordProd_nil, map_one] using (reflectionGroup hD P).one_mem
  | cons j l ih =>
    rw [b.wordProd_cons, map_mul]
    apply (reflectionGroup hD P).mul_mem _ ih
    have hj : (actualRootEquiv hD).symm j.val ∈ FundamentalRootsFor D P := by
      apply (actualBase_support hD R hadd P hP b hb _).mp
      simpa only [Equiv.apply_symm_apply] using j.property
    have heq : actualWeylAction hD R (b.simpleReflection j) =
        reflectionPerm hD ((actualRootEquiv hD).symm j.val) := by
      have h := actualWeylAction_reflection hD R ((actualRootEquiv hD).symm j.val)
      simpa only [Equiv.apply_symm_apply, RootPairing.Base.simpleReflection] using h
    rw [heq]
    exact Subgroup.subset_closure ⟨⟨_, hj⟩, rfl⟩

include hD R in
/-- Words in the actual fundamental reflection permutations carry any positive
system to the selected one. This also holds when the root set is empty. -/
public theorem exists_reflectionGroup_positive_transport
    (hadd : D.IsRootAdditionComplete) {P : Set D.Root} (hP : IsPositiveSystem D P)
    (Q : Set D.Root) (hQ : IsPositiveSystem D Q) :
    ∃ w ∈ reflectionGroup hD P, ∀ α, w α ∈ P ↔ α ∈ Q := by
  obtain ⟨b, hb⟩ := exists_actualBase hD R hadd P hP
  obtain ⟨g, hg⟩ := exists_weylGroup_translate_base_toPositiveSubsystem R.pairing b
    (actualPositiveSubsystem hD R hadd Q hQ)
  refine ⟨actualWeylAction hD R g⁻¹, actualWeylAction_mem hD R hadd P hP b hb g⁻¹, ?_⟩
  intro α
  have hpos (χ : TorusRootIndex T) : b.IsPos χ ↔ (actualRootEquiv hD).symm χ ∈ P := by
    rw [← RootPairing.Base.mem_toPositiveSubsystem, hb]
    rfl
  have hq : (g • b).IsPos (actualRootEquiv hD α) ↔ α ∈ Q := by
    rw [← RootPairing.Base.mem_toPositiveSubsystem, hg,
      actualPositiveSubsystem_mem hD R hadd Q hQ]
  change (RootPairing.Base.mapAut g.val b).IsPos (actualRootEquiv hD α) ↔ α ∈ Q at hq
  rw [RootPairing.Base.isPos_mapAut_iff, hpos] at hq
  exact hq

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry.NormalizerActionExistence
