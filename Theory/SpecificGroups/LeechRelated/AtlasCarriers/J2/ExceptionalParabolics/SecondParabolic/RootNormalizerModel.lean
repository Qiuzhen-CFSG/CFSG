module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.RootCoordinates
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.BlockGeometry
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.SourceActionSplitting
public import Theory.GroupTheory.NormalSymmetricThreeCubic
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# The native Hall–Janko second parabolic in root-normalizer coordinates

The native radical coordinates identify its center with a four-group.
Six explicit normalizer words induce six distinct center automorphisms,
so the center action is full. Native self-centralization, order 1152 and
the quotient S₃ × C₃ now satisfy the intrinsic automizer recognition.
The proved Sylow-three splitting identifies the entire native normalizer
with the explicit root semidirect product and preserves its radical inclusion.

The source alpha endpoint uses this native comparison after its independent
root-normalizer recognition. Aligning the full Borel and the other endpoint
is a further marked comparison, not a consequence of equal group orders.
Source: DGS, *Groups and Graphs* (1985), (10.9), p.163; Aschbacher,
*Sporadic Groups* (1994), 46.14, pp.257–258. The native words retain the
ATLAS J2G1-p100B0 provenance of the imported carrier modules.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.RootCoordinates
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.SylowData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate

private def centerAction : p₂ →* MulAut (center q₂) :=
  (MulAut.characteristic (center q₂)).comp q₂.normalizerMonoidHom

private def centerWitness (i : Fin 4) : center q₂ :=
  ⟨⟨RankOneFourNormalizer.fourElement i,qElement_mem _⟩,by
    obtain ⟨x,hx,he⟩ := RankOneFourNormalizer.fourElement_mem i
    exact (show x = ⟨RankOneFourNormalizer.fourElement i,qElement_mem _⟩ from Subtype.ext he) ▸ hx⟩

private def actionRep (i : Fin 6) : p₂ :=
  (⟨sGenerator 3,s_le_p₂ (subset_closure ⟨3,rfl⟩)⟩ : p₂) ^ (i.val / 3) *
    (⟨oddGenerator 0,oddGenerator_mem_p₂ 0⟩ : p₂) ^ (i.val % 3)

private def actionTable (i : Fin 6) : Equiv.Perm (Fin 100) :=
  (sGenTable 3) ^ (i.val / 3) * (oddTable 0) ^ (i.val % 3)

private theorem actionRep_table (i : Fin 6) :
    inclusion (actionRep i : Carrier) = actionTable i := by
  simp only [actionRep,Subgroup.coe_mul,Subgroup.coe_pow,map_mul,map_pow,
    sGenerator_inclusion,oddGenerator_inclusion,actionTable]

private theorem centerAction_table (i : Fin 6) (j : Fin 4) :
    inclusion (((centerAction (actionRep i) (centerWitness j) : center q₂) : q₂) : Carrier) =
      actionTable i * qTable (RankOneFourNormalizer.Checks.fourIndex j) * (actionTable i)⁻¹ := by
  change inclusion ((actionRep i : Carrier) *
    RankOneFourNormalizer.fourElement j * (actionRep i : Carrier)⁻¹) = _
  rw [map_mul,map_mul,map_inv,actionRep_table]
  exact congrArg (fun p => actionTable i * p * (actionTable i)⁻¹) (qElement_inclusion _)

set_option maxRecDepth 100000 in
private theorem action_distinct_check : ∀ i j : Fin 6,
    (actionTable i * qTable 5 * (actionTable i)⁻¹) 0 =
      (actionTable j * qTable 5 * (actionTable j)⁻¹) 0 →
    (actionTable i * qTable 5 * (actionTable i)⁻¹) 1 =
      (actionTable j * qTable 5 * (actionTable j)⁻¹) 1 →
    (actionTable i * qTable 6 * (actionTable i)⁻¹) 0 =
      (actionTable j * qTable 6 * (actionTable j)⁻¹) 0 →
    (actionTable i * qTable 6 * (actionTable i)⁻¹) 1 =
      (actionTable j * qTable 6 * (actionTable j)⁻¹) 1 → i = j := by
  apply allFin
  decide +kernel

private theorem action_reps_injective : Function.Injective (fun i => centerAction (actionRep i)) := by
  intro i j h
  have h1 := congrArg (fun f : MulAut (center q₂) =>
    inclusion (((f (centerWitness 1) : center q₂) : q₂) : Carrier)) h
  have h2 := congrArg (fun f : MulAut (center q₂) =>
    inclusion (((f (centerWitness 2) : center q₂) : q₂) : Carrier)) h
  rw [centerAction_table,centerAction_table] at h1 h2
  exact action_distinct_check i j
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h1)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) h1)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h2)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) h2)

private theorem centerAction_surjective : Function.Surjective centerAction := by
  let : IsKleinFour (center q₂) := {
    card_four := (Nat.card_congr centerEquiv.symm.toEquiv).trans (by simp)
    exponent_two := (Monoid.exponent_eq_of_mulEquiv centerEquiv.symm).trans (by simp) }
  have hc := IsKleinFour.card_mulAut (center q₂)
  let f : Fin 6 → MulAut (center q₂) := fun i => centerAction (actionRep i)
  have hf : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨action_reps_injective,by simpa using hc.symm⟩
  intro a
  obtain ⟨i,hi⟩ := hf.2 a
  exact ⟨actionRep i,hi⟩

/-- Native coordinates on the radical inside its full normalizer. -/
def relativeRootEquiv : q₂.subgroupOf p₂ ≃* Matrix.PSL3Four.RootNormalizerModel.Root :=
  (subgroupOfEquivOfLe q₂.le_normalizer).trans rootEquiv

/-- Every automorphism of the radical center comes from the literal native normalizer. -/
theorem full_center_action : ∀ b : MulAut (center (q₂.subgroupOf p₂)), ∃ a : p₂,
    ∀ z : center (q₂.subgroupOf p₂),
      MulAut.conjNormal a z = (b z : q₂.subgroupOf p₂) := by
  let e : center (q₂.subgroupOf p₂) ≃* center q₂ :=
    centerCongr (subgroupOfEquivOfLe (show q₂ ≤ p₂ from q₂.le_normalizer))
  intro b
  obtain ⟨a,ha⟩ := centerAction_surjective (MulAut.congr e b)
  refine ⟨a,fun z => ?_⟩
  have hz := congrArg (fun w : center q₂ => ((w : q₂) : Carrier))
    (MulEquiv.congr_fun ha (e z))
  change (a : Carrier) * ((z : q₂.subgroupOf p₂) : p₂) * (a : Carrier)⁻¹ =
    ((e (b (e.symm (e z))) : q₂) : Carrier) at hz
  rw [e.symm_apply_apply] at hz
  apply Subtype.ext
  apply Subtype.ext
  exact hz

/-- The native core is self-centralizing inside its full normalizer. -/
theorem relative_selfCentralizing :
    centralizer (q₂.subgroupOf p₂ : Set p₂) ≤ q₂.subgroupOf p₂ := by
  intro x hx
  apply RankOneFourNormalizer.centralizer_le_q₂
  intro y hy
  exact congrArg Subtype.val (hx ⟨y,q₂.le_normalizer hy⟩ hy)

/-- The full native second parabolic is the explicit root-normalizer model,
with the original radical inclusion retained literally. -/
theorem exists_model_equiv :
    ∃ (f : p₂ ≃* Matrix.PSL3Four.RootNormalizerModel.Model)
      (d : q₂.subgroupOf p₂ ≃* Matrix.PSL3Four.RootNormalizerModel.Root),
      ∀ q : q₂.subgroupOf p₂, f (q : p₂) = SemidirectProduct.inl (d q) := by
  let Q := q₂.subgroupOf p₂
  obtain ⟨d,hd⟩ := Matrix.PSL3Four.RootNormalizerModel.SourceAction.exists_adjusted_coordinates
    Q relativeRootEquiv relative_selfCentralizing PairNormalizer.card_p₂ full_center_action
    (NormalSymmetricThreeFactor.exists_central_cubic_coset Q p₂_quotient_equiv.some)
  obtain ⟨f,hf⟩ := Matrix.PSL3Four.RootNormalizerModel.SourceAction.exists_model_equiv
    Q d relative_selfCentralizing hd
  exact ⟨f,d,hf⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.RootCoordinates
