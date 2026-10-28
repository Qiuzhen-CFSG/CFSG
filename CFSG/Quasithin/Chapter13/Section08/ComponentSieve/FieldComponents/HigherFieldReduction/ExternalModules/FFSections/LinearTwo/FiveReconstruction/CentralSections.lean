module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.SectionModel
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.ProjectiveCentralCover
public import Theory.Representation.BinaryOffender.IrreducibleMovedTransport

/-!
# Vanishing of the central bottom in the exceptional orbit

The five-letter core is projective for A₅. Reindexing the actual constituent
by its marked A₅ equivalence makes its central-quotient projection an
equivariant surjection onto this projective module. The Irr⁺ commutator
identity forces that projection to be injective. Distinct normalizer
conjugates then form a direct sum, and each has zero fixed space. Their
sum therefore has zero fixed space as well.

In particular the literal bottom W∩C_U(K) is zero when W is the sum of the
two source cubic conjugates. No assertion about U/W, or a splitting of U,
is assumed or concluded here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.6(1),
printed p.408, and the A₅ deduction in 13.8.20, printed p.954.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

variable {G U E N : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
    [Group E] [AddCommGroup N] [Module (ZMod 2) N]
    (ρ : Representation (ZMod 2) G U) (K : Subgroup G)
    (σ : Representation (ZMod 2) E N) (J L : Subgroup E)
    (e : MarkedActionEquiv σ J L (BinaryPermutation.naturalRepresentation (Fin 5))
      (alternatingGroup (Fin 5))) (b : K ≃* L)

include e in
/-- Projectivity removes the literal central kernel of an Irr⁺ five-letter constituent. -/
theorem constituent_disjoint_fixed
    (I : Submodule (ZMod 2) U) (hI : IsIrrPlus ρ K I)
    (a : centralQuotient ρ K I ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (centralQuotientRepresentation ρ K I hI.choose k v) =
      σ (b k) (a v)) : Disjoint I (fixedSpace ρ K) := by
  let d := componentEquiv σ J L e b
  let c := coreCoordinates σ J L e a
  let τ : Representation (ZMod 2) (alternatingGroup (Fin 5)) I := ((invariantSubspace ρ K I hI.choose).toRepresentation).comp d.symm.toMonoidHom
  let q := ((fixedSpace ρ K).comap I.subtype).mkQ
  let p : τ.IntertwiningMap (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) :=
    { toLinearMap := c.toLinearMap.comp q
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro v
        change c (centralQuotientRepresentation ρ K I hI.choose (d.symm g) (q v)) =
          BinaryPermutation.alternatingCoreRepresentation (Fin 5) g (c (q v))
        simpa only [d, MulEquiv.apply_symm_apply] using
          coreCoordinates_equivariant σ J L e _ b a ha (d.symm g) (q v) }
  have hp : Function.Surjective p := c.surjective.comp (Submodule.mkQ_surjective _)
  have hk : ∀ w, p w = 0 → ∀ g, τ g w = w := by
    intro w hw g
    have hq : q w = 0 := c.injective (hw.trans (map_zero c).symm)
    have hz : w ∈ (fixedSpace ρ K).comap I.subtype :=
      (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K).comap I.subtype)).mp hq
    exact Subtype.ext (hz (d.symm g))
  have hc : Coinvariants.ker τ = ⊤ := by
    have hle : I ≤ (Coinvariants.ker τ).map I.subtype := by
      apply hI.choose_spec.1.ge.trans
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, v, hv, rfl⟩
      let k' : K := ⟨k, hk⟩
      let v' : I := ⟨v, hv⟩
      refine ⟨τ (d k') v' - v', Coinvariants.sub_mem_ker (ρ := τ) (d k') v', ?_⟩
      change ρ (d.symm (d k')).val v - v = ρ k v - v
      rw [d.symm_apply_apply]
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hle v.property
    exact (Subtype.ext he : w = v) ▸ hw
  let := BinaryPermutation.alternatingFive_core_projective
  have hinj := p.injective_of_projective_of_fixed_kernel hp hk hc
  rw [Submodule.disjoint_def]
  intro v hv hz
  have he : p ⟨v, hv⟩ = 0 := by
    change c (q ⟨v, hv⟩) = 0
    rw [show q ⟨v, hv⟩ = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hz, map_zero]
  exact congrArg Subtype.val (hinj (he.trans (map_zero p).symm))

variable [K.Normal]

include e in
/-- Distinct actual cubic conjugates have no fixed vectors in their sum. -/
theorem orbit_disjoint_fixed
    (I : Submodule (ZMod 2) U) (hI : IsIrrPlus ρ K I)
    (a : centralQuotient ρ K I ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (centralQuotientRepresentation ρ K I hI.choose k v) =
      σ (b k) (a v))
    (x : G) (hne : I ≠ I.map (ρ x)) :
    Disjoint (I ⊔ I.map (ρ x)) (fixedSpace ρ K) := by
  have hi := constituent_disjoint_fixed ρ K σ J L e b I hI a ha
  have hx : x ∈ normalizer K := by rw [Subgroup.normalizer_eq_top]; trivial
  have hIx := hI.map_normalizer ρ hx
  have hj : Disjoint (I.map (ρ x)) (fixedSpace ρ K) := by
    rw [Submodule.disjoint_def]
    rintro v ⟨u, hu, rfl⟩ hz
    have hu0 := (Submodule.disjoint_def.mp hi) u hu
      ((fixedSpace_stable_of_normal ρ K (mem_top x) u).mp hz)
    rw [hu0, map_zero]
  have hd : Disjoint I (I.map (ρ x)) := by
    rw [Submodule.disjoint_def]
    intro v hv hw
    have hcentral :=
      (hI.le_or_inf_sup_fixedSpace_le ρ hIx.choose).resolve_left
        (fun h => hne (hI.eq_of_le ρ hIx h))
    exact (Submodule.disjoint_def.mp hi) v hv
      (hcentral ⟨hv, Submodule.mem_sup_left hw⟩)
  rw [Submodule.disjoint_def]
  intro v hv hz
  obtain ⟨i, hiI, j, hjJ, rfl⟩ := Submodule.mem_sup.mp hv
  have hif : i ∈ fixedSpace ρ K := by
    intro k
    apply sub_eq_zero.mp
    apply (Submodule.disjoint_def.mp hd)
    · exact I.sub_mem ((hI.choose k.property i).mpr hiI) hiI
    · have he : ρ k i - i = -(ρ k j - j) := by
        have hf := hz k
        rw [map_add] at hf
        have : (ρ k i - i) + (ρ k j - j) = 0 := by
          calc
            _ = ρ k i + ρ k j - (i + j) := by abel
            _ = 0 := sub_eq_zero.mpr hf
        exact eq_neg_of_add_eq_zero_left this
      change ρ k i - i ∈ I.map (ρ x)
      rw [he]
      exact (I.map (ρ x)).neg_mem
        ((I.map (ρ x)).sub_mem ((hIx.choose k.property j).mpr hjJ) hjJ)
  have hi0 := (Submodule.disjoint_def.mp hi) i hiI hif
  subst i
  simp only [zero_add] at hz ⊢
  exact (Submodule.disjoint_def.mp hj) j hjJ hz

include e in
/-- In the source two-conjugate orbit, the actual central bottom vanishes. -/
theorem centralBottom_eq_bot
    (W : Subrepresentation ρ)
    (I : Submodule (ZMod 2) U) (hI : IsIrrPlus ρ K I)
    (a : centralQuotient ρ K I ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (centralQuotientRepresentation ρ K I hI.choose k v) =
      σ (b k) (a v))
    (x : G) (hne : I ≠ I.map (ρ x))
    (hW : W.toSubmodule = I ⊔ I.map (ρ x)) :
    LinearTwo.centralBottom ρ K W = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change W.toSubmodule ⊓ fixedSpace ρ K = ⊥
  rw [hW]
  exact (orbit_disjoint_fixed ρ K σ J L e b I hI a ha x hne).eq_bot

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

end
