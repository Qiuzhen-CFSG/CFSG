module

public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RootGeometry
public import Theory.AlgebraicGroup.Borel.IntersectionGeometry.BruhatCoverage.SimpleExchange.RankOneGeometry.Inputs

/-!
Assembly of marked rank-one geometry for simple-reflection exchange.

The local SL₂ markings supply compatible opposite root curves. The checked
rank-one word calculation places their reflections in the torus normalizer.
Their prescribed root conjugation identifies their images in the normalizer
root action, whose torus kernel and reflection-generated image lift generation
to the full abstract normalizer. Finally, the positive-system partition gives
the root-sign alternative and simple reflections preserve the other positive
root groups. This constructs every field of `SimpleExchangeRootGeometry`
using the original root data and positive system.

The existence of `SimpleRootMarkings` and `NormalizerRootAction` from reductivity
remains explicit: this module supplies conditional assembly, not the missing
geometric existence theorem. Sources: GLS3, 1.9.5(f), 1.11.2–1.11.3; Borel,
§§13.18, 14.6–14.8 and 14.15 T2/T3.
-/

universe u

namespace Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}
variable {D : RootGroupData G T} {P : Set D.Root}

private theorem positive_root_le_borel (B : ClosedSubgroup G)
    (hBP : IsBorelOfPositiveSystem D P B) {α : D.Root} (hα : α ∈ P) :
    (D.rootSubgroup α).toSubgroup ≤ B.toSubgroup := by
  rw [hBP.torus_unipotent_generate, hBP.root_generated]
  exact le_sup_of_le_right (rootSubgroup_le_RootSubgroupGenerated D hα)

private theorem conjugated_mem (X : ClosedSubgroup G)
    (n x : Variety.Point G) (hx : x ∈ X.toSubgroup) :
    n * x * n⁻¹ ∈ (X.conjugate n).toSubgroup := by
  apply (X.mem_conjugate_iff n _).mpr
  simpa [mul_assoc] using hx

/-- The matrix reflection image, now regarded as an element of the full torus
normalizer by the rank-one normalization calculation. -/
@[expose] public def SimpleRootMarkings.lift (L : SimpleRootMarkings D P) (hD : D.IsRealization)
    (i : {α // α ∈ FundamentalRootsFor D P}) : T.normalizer.toSubgroup :=
  ⟨(L.marking i).hom BruhatGeneration.SL2.reflection, (L.marking i).reflection_mem hD⟩

/-- The chosen matrix lift induces the fundamental root reflection in the
normalizer action. Distinct root subgroups distinguish the root indices. -/
public theorem action_lift (L : SimpleRootMarkings D P) (W : NormalizerRootAction D P)
    (hD : D.IsRealization) (i : {α // α ∈ FundamentalRootsFor D P}) :
    W.action (L.lift hD i) = W.reflection i := by
  ext β
  rw [W.reflection_apply]
  apply hD.rootSubgroup_injective
  exact (W.transport (L.lift hD i) β).symm.trans (L.reflection_root i β)

/-- Lift generation from the Weyl image to the full normalizer. The torus
accounts for the exact kernel; no ambient B–N generation is assumed. -/
public theorem normalizer_generated (L : SimpleRootMarkings D P)
    (W : NormalizerRootAction D P) (hD : D.IsRealization) :
    Subgroup.closure ((T.toSubgroup : Set (Variety.Point G)) ∪
      Set.range (fun i => (L.marking i).hom BruhatGeneration.SL2.reflection)) =
        T.normalizer.toSubgroup := by
  let H := Subgroup.closure ((T.toSubgroup : Set (Variety.Point G)) ∪
    Set.range (fun i => (L.marking i).hom BruhatGeneration.SL2.reflection))
  have hTH : T.toSubgroup ≤ H := fun _ hx => Subgroup.subset_closure (Or.inl hx)
  have hlift (i : {α // α ∈ FundamentalRootsFor D P}) : (L.lift hD i).val ∈ H :=
    Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hHN : H ≤ T.normalizer.toSubgroup := by
    apply (Subgroup.closure_le _).mpr
    rintro x (hx | ⟨i, rfl⟩)
    · exact T.toSubgroup.le_normalizer hx
    · exact (L.marking i).reflection_mem hD
  apply le_antisymm hHN
  intro n hn
  let nn : T.normalizer.toSubgroup := ⟨n, hn⟩
  have himage : W.action.range ≤ (H.subgroupOf T.normalizer.toSubgroup).map W.action := by
    rw [W.range_eq]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨L.lift hD i, hlift i, action_lift L W hD i⟩
  obtain ⟨m, hm, hmn⟩ := himage (show W.action nn ∈ W.action.range from ⟨nn, rfl⟩)
  have hker : nn * m⁻¹ ∈ W.action.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmn, mul_inv_cancel]
  rw [W.kernel] at hker
  have hnm : n * m.val⁻¹ ∈ H := hTH hker
  have h := H.mul_mem hnm hm
  change n * m.val⁻¹ * m.val ∈ H at h
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- Every normalizer conjugate of a marked opposite pair has at least one
root subgroup in B. Apply the positive-system partition after inverse
conjugation, using the action's compatibility with negation. -/
public theorem transport_sign (L : SimpleRootMarkings D P) (W : NormalizerRootAction D P)
    (B : ClosedSubgroup G) (hP : IsPositiveSystem D P)
    (hBP : IsBorelOfPositiveSystem D P B)
    (i : {α // α ∈ FundamentalRootsFor D P}) (n : Variety.Point G)
    (hn : n ∈ T.normalizer.toSubgroup) :
    (∀ t, n⁻¹ * (L.marking i).hom (BruhatGeneration.SL2.upper t) * n ∈ B.toSubgroup) ∨
      (∀ t, n⁻¹ * (L.marking i).hom (BruhatGeneration.SL2.lower t) * n ∈ B.toSubgroup) := by
  let ni : T.normalizer.toSubgroup := ⟨n⁻¹, T.normalizer.toSubgroup.inv_mem hn⟩
  have hsign : W.action ni i.val ∈ P ∪ D.neg ⁻¹' P := by
    rw [hP.2.1]
    trivial
  rcases hsign with hpos | hneg
  · left
    intro t
    apply positive_root_le_borel B hBP hpos
    rw [← W.transport ni i.val]
    have ht : (L.marking i).hom (BruhatGeneration.SL2.upper t) ∈
        (D.rootSubgroup i.val : Set (Variety.Point G)) := by
      rw [← (L.marking i).upper_range]
      exact ⟨t, rfl⟩
    simpa only [ni, inv_inv] using conjugated_mem _ n⁻¹ _ ht
  · right
    intro t
    have hpos : W.action ni (D.neg i.val) ∈ P := by
      rw [W.neg]
      exact hneg
    apply positive_root_le_borel B hBP hpos
    rw [← W.transport ni (D.neg i.val)]
    have ht : (L.marking i).hom (BruhatGeneration.SL2.lower t) ∈
        (D.rootSubgroup (D.neg i.val) : Set (Variety.Point G)) := by
      rw [← (L.marking i).lower_range]
      exact ⟨t, rfl⟩
    simpa only [ni, inv_inv] using conjugated_mem _ n⁻¹ _ ht

/-- Conditional construction of the published exchange geometry, preserving
the supplied D and P literally. The two geometric input structures must still
be constructed from reductivity before this gives the source theorem. -/
@[expose] public def of_markings_normalizerAction (B : ClosedSubgroup G)
    (hD : D.IsRealization) (hadd : D.IsRootAdditionComplete)
    (hP : IsPositiveSystem D P) (hBP : IsBorelOfPositiveSystem D P B)
    (L : SimpleRootMarkings D P) (W : NormalizerRootAction D P) :
    SimpleExchangeRootGeometry B T where
  data := D
  realized := hD
  addition_complete := hadd
  positive := P
  isPositive := hP
  borel := hBP
  rankOne := fun i => (L.marking i).hom
  upper_range := fun i => (L.marking i).upper_range
  lower_range := fun i => (L.marking i).lower_range
  diagonal_mem := fun i => (L.marking i).diagonal_mem
  reflection_mem := fun i => (L.marking i).reflection_mem hD
  normalizer_generated := normalizer_generated L W hD
  reflection_other_positive := by
    intro i β hβ hne x hx
    apply positive_root_le_borel B hBP (W.other_positive i β hβ hne)
    rw [← L.reflection_root i β]
    exact conjugated_mem _ _ x hx
  transport_sign := transport_sign L W B hP hBP

/-- Existence of both independent geometric inputs suffices for exchange
geometry. The reductive existence theorem remains with the assembly owner. -/
public theorem nonempty_of_markings_normalizerAction (B : ClosedSubgroup G)
    (hD : D.IsRealization) (hadd : D.IsRootAdditionComplete)
    (hP : IsPositiveSystem D P) (hBP : IsBorelOfPositiveSystem D P B)
    (hL : Nonempty (SimpleRootMarkings D P))
    (hW : Nonempty (NormalizerRootAction D P)) :
    Nonempty (SimpleExchangeRootGeometry B T) := by
  obtain ⟨L⟩ := hL
  obtain ⟨W⟩ := hW
  exact ⟨of_markings_normalizerAction B hD hadd hP hBP L W⟩

end Theory.AlgebraicGroup.BorelIntersectionGeometry.RankOneGeometry
