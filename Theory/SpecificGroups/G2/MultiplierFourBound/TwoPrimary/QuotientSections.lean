module

public import Theory.SpecificGroups.G2.MultiplierFourBound.TwoPrimary.ExceptionalRelations
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.TorusEquivariance
public import Theory.GroupTheory.PerfectCentralCoverLocalSplitting

/-!
# Torus-equivariant root sections modulo the common G₂(4) defect

The full preimage of each positive root becomes abelian after quotienting a
perfect central cover by the short-root defect: `ExceptionalRelations` places
all six root defects in this one subgroup. A commutator with a lift of a
nonidentity root scalar then gives an additive section. The existing torus
normalization makes the six sections equivariant under every split-torus lift.

The quotient and its projection are exactly `Cover.quotientKernelSubgroup`,
including for the prescribed universal cover. These sections supply the
quotient-cover input to the exceptional positive-root collection argument;
relations between different roots remain a separate calculation.

Source: Aschbacher–Smith I.1.3(1), printed p.407 (PDF p.418), GLS III §6.1,
and Griess, Trans. AMS 183 (1973), 355–421, pp.357–371. The local section
construction adapts `MultiplierOrdinary.RootLifts` without changing its
ordinary-field interface. The root and torus maps retain their ATLAS
attribution through the imported modules.
-/

@[expose] public section

open scoped commutatorElement
namespace Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary
open MultiplierOrdinary PerfectCentralCovering Subgroup
variable {E : Type*} [Group E]

/-- An individual root defect in a central cover is a normal subgroup. -/
instance rootDefect_normal (c : Cover E FourBase) (i : Fin 6) :
    (rootDefect c.toMonoidHom i).Normal where
  conj_mem x hx g := by
    have hz := rootDefect_le_center c.toMonoidHom c.ker_le_center i hx
    simpa only [mem_center_iff.mp hz g, mul_assoc, mul_inv_cancel, mul_one] using hx

/-- Killing all individual root defects makes every full root preimage abelian. -/
theorem quotient_root_preimage_commute (c : Cover E FourBase)
    (D : Subgroup E) [D.Normal] (hD : D ≤ c.toMonoidHom.ker)
    (hroots : ∀ i, rootDefect c.toMonoidHom i ≤ D)
    (i : Fin 6) (v w : E ⧸ D)
    (hv : (c.quotientKernelSubgroup D hD).toMonoidHom v ∈ (positiveRootHom i).range)
    (hw : (c.quotientKernelSubgroup D hD).toMonoidHom w ∈ (positiveRootHom i).range) :
    Commute v w := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D v
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D w
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hroots i (commutator_mem_commutator hv hw)

private theorem exists_root_lift
    (f : E →* FourBase) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (c : FourFieldˣ) (hc : c ≠ 1) (i : Fin 6)
    (hcomm : ∀ v w : E, f v ∈ (positiveRootHom i).range →
      f w ∈ (positiveRootHom i).range → Commute v w) :
    ∃ u : Multiplicative FourField →* E, f.comp u = positiveRootHom i := by
  classical
  have hc1 : (c : FourField) ≠ 1 := fun h => hc (Units.ext h)
  obtain ⟨a, ha⟩ := hf (scalarTorus i c)
  choose b hb using fun x : FourField => hf (positiveRoot i x)
  let d : FourField := (c : FourField) - 1
  have hd : d ≠ 0 := sub_ne_zero.mpr hc1
  let s : FourField → E := fun x => ⁅a, b (d⁻¹ * x)⁆
  have hs (x : FourField) : f (s x) = positiveRoot i x := by
    dsimp [s]
    rw [map_commutatorElement, commutatorElement_def, ha, hb, scalarTorus_conjugate]
    have hinv (z : FourField) : (positiveRoot i z)⁻¹ = positiveRoot i (-z) :=
      ((positiveRootHom (F := FourField) i).map_inv (Multiplicative.ofAdd z)).symm
    rw [hinv, ← positiveRoot_add]
    congr 1
    calc
      (c : FourField) * (d⁻¹ * x) + -(d⁻¹ * x) = d * (d⁻¹ * x) := by dsimp [d]; ring
      _ = x := mul_inv_cancel_left₀ hd x
  have hs0 : s 0 = 1 := by
    dsimp [s]
    rw [mul_zero]
    have h0 : f (b 0) = f 1 := by rw [hb, positiveRoot_zero, map_one]
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl h0]
    simp
  have hsadd (x y : FourField) : s (x + y) = s x * s y := by
    have hsum : f (b (d⁻¹ * (x + y))) = f (b (d⁻¹ * x) * b (d⁻¹ * y)) := by
      rw [map_mul, hb, hb, hb, ← positiveRoot_add, mul_add]
    have hcomm' : Commute (b (d⁻¹ * x)) (s y) :=
      hcomm _ _ (by rw [hb]; exact ⟨.ofAdd _, rfl⟩)
        (by rw [hs]; exact ⟨.ofAdd _, rfl⟩)
    change ⁅a, b (d⁻¹ * (x + y))⁆ = _
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl hsum,
      commutatorElement_mul_right_eq_mul_conj]
    change s x * b (d⁻¹ * x) * s y * (b (d⁻¹ * x))⁻¹ = _
    rw [mul_assoc (s x), hcomm'.eq, ← mul_assoc, mul_assoc (s x * s y),
      mul_inv_cancel, mul_one]
  refine ⟨{
    toFun := fun x => s x.toAdd
    map_one' := hs0
    map_mul' := fun x y => hsadd x.toAdd y.toAdd }, ?_⟩
  exact MonoidHom.ext (fun x => hs x.toAdd)

/-- A common root-defect quotient has additive sections with the literal
split-torus action. -/
theorem quotient_torusEquivariant_sections (c : Cover E FourBase)
    (D : Subgroup E) [D.Normal] (hD : D ≤ c.toMonoidHom.ker)
    (hroots : ∀ i, rootDefect c.toMonoidHom i ≤ D) :
    ∃ L : RootSections (c.quotientKernelSubgroup D hD).toMonoidHom,
      L.TorusEquivariant := by
  have hcard : 1 < Nat.card FourFieldˣ := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]
    decide
  let : Nontrivial FourFieldˣ := (Finite.one_lt_card_iff_nontrivial).mp hcard
  obtain ⟨a, ha⟩ := exists_ne (1 : FourFieldˣ)
  let q := c.quotientKernelSubgroup D hD
  have hcomm := quotient_root_preimage_commute c D hD hroots
  choose u hu using fun i => exists_root_lift q.toMonoidHom q.surjective
    q.ker_le_center a ha i (hcomm i)
  let L : RootSections q.toMonoidHom := ⟨u, hu⟩
  exact L.exists_torusEquivariant q.surjective q.ker_le_center a ha hcomm

/-- For G₂(4), the one short-root defect kills all six individual defects,
so its quotient has torus-equivariant additive root sections. -/
theorem shortRootQuotient_torusEquivariant_sections (c : Cover E FourBase) :
    ∃ L : RootSections (c.quotientKernelSubgroup (rootDefect c.toMonoidHom 2)
      (rootDefect_le_kernel c.toMonoidHom 2)).toMonoidHom, L.TorusEquivariant := by
  exact quotient_torusEquivariant_sections c (rootDefect c.toMonoidHom 2)
    (rootDefect_le_kernel c.toMonoidHom 2)
    (ExceptionalRelations.rootDefect_le_short c.toMonoidHom c.surjective c.ker_le_center)

/-- Normality for the separately named universal projection. -/
instance universal_rootDefect_normal (i : Fin 6) :
    (rootDefect (universalProjection FourBase) i).Normal :=
  rootDefect_normal (universalCover FourBase) i

/-- The root-section input on the literal universal-cover quotient. -/
theorem universal_shortRootQuotient_torusEquivariant_sections :
    ∃ L : RootSections ((universalCover FourBase).quotientKernelSubgroup
      (rootDefect (universalProjection FourBase) 2)
      (rootDefect_le_kernel (universalProjection FourBase) 2)).toMonoidHom,
      L.TorusEquivariant :=
  shortRootQuotient_torusEquivariant_sections (universalCover FourBase)

end Atlas.G2.FiniteCover.MultiplierFourBound.TwoPrimary

end
