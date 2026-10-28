module
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.Restriction
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.CentralizerCoordinates.RootSpace
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.NaturalLocalAction.CentralizerCoordinates.GroupComparison

public import Theory.AtlasPort.LinearGroups.G2.ShortRootProducts.CentralizerCore.Containment

/-!
# The actual J₂ centralizer module in K.4.5

Assume only that the marked noncentral involution is conjugate to a nonzero
C-root element in the actual octonion G₂ model. Its entire centralizer lies
in the long parabolic by the proved octonion containment theorem. Restricting
the block projection to the literal embedded A₅ gives an isomorphism to SL₂(K).
The commuting E₄ has zero A/B parameters and, by order four, is exactly the
conjugate C-root group.

The quotient coordinates from RootSpace then give an actual intertwiner
W ≃ K × K² for the full E₄ × A₅ action, with trivial first summand and the
natural SL₂ action on the second. They also give, as binary submodule
equalities, W = C_V(a) = C_V(centralFour) = [V,centralFour]. No dimension,
fixed-dimension, quadraticity or cubicity assertion is assumed. The parent
NaturalLocalAction task retains the placement and numerical/actor conclusions.

Source: Aschbacher–Smith, K.4.5, printed p.460/PDF p.471, using B.4.6(6).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.JankoTwo
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open Atlas.G2.ShortRootProducts.CentralizerCore
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores
open NaturalLocalAction
open scoped MatrixGroups
open Matrix

namespace MarkedModule
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)

include D in
private theorem field_finite : Finite K := by
  let : FiniteDimensional (ZMod 2) K :=
    FiniteDimensional.of_finrank_pos (by rw [D.fieldDegree]; decide)
  exact Module.finite_of_finite (ZMod 2)

include D in
private theorem field_card : Nat.card K = 4 := by
  let : Finite K := D.field_finite
  let : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
    ZMod.card, D.fieldDegree]
  norm_num

/-- The literal full centralizer, conjugated into the chosen C-root coordinates. -/
def shortRootCentralizerEmbedding (g : Model K) : E4 × A5 →* Model K :=
  (MulAut.conj g⁻¹).toMonoidHom.comp (D.carrierEmbedding.comp centralizerEmbedding)

private theorem shortRootCentralizerEmbedding_injective (g : Model K) :
    Function.Injective (D.shortRootCentralizerEmbedding g) :=
  (MulAut.conj g⁻¹).injective.comp
    (D.carrierEmbedding_injective.comp centralizerEmbedding_injective)

private theorem shortRootCentralizer_factors
    (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) (x : E4 × A5) :
    ∃ (p : Multiplicative (K × K)) (t : K) (M : SL(2,K)),
      D.shortRootCentralizerEmbedding g x = longRootHom p * rootC t * PairStabilizer.blockHom M := by
  have ha : MulAut.conj g⁻¹ (D.carrierEmbedding a) = rootC r := by
    rw [he]
    simp [MulAut.conj_apply, mul_assoc]
  have hc : Commute (centralizerEmbedding x) a :=
    mem_centralizer_singleton_iff.mp (a_centralizer_equiv.symm x).property
  have hh := (hc.map D.carrierEmbedding).map (MulAut.conj g⁻¹).toMonoidHom
  change Commute (D.shortRootCentralizerEmbedding g x)
    (MulAut.conj g⁻¹ (D.carrierEmbedding a)) at hh
  rw [ha] at hh
  have hm : D.shortRootCentralizerEmbedding g x ∈
      centralizer ({rootC r} : Set (Model K)) := mem_centralizer_singleton_iff.mpr hh.eq
  exact centralizer_rootC_factor r hr hm

omit [CharP K 2] [Algebra (ZMod 2) K] in
private theorem shortRootGroup_card : Nat.card (shortRootGroup (F := K)) = Nat.card K := by
  let e : Multiplicative K ≃* shortRootGroup (F := K) :=
    MulEquiv.ofBijective (shortRootHom (F := K)).rangeRestrict ⟨by
      intro x y h
      have hxy : rootC x.toAdd = rootC y.toAdd :=
        congrArg (fun z : shortRootGroup (F := K) => z.val) h
      exact Multiplicative.toAdd.injective (Atlas.G2.rootC_injective hxy),
      (shortRootHom (F := K)).rangeRestrict_surjective⟩
  exact (Nat.card_congr e.toEquiv).symm

/-- Actual block quotient and root-group image of the native centralizer. -/
theorem shortRootCentralizer_comparison
    (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) :
    ∃ φ : A5 ≃* SL(2,K),
      (∀ x : E4 × A5, ∃ (p : Multiplicative (K × K)) (t : K),
        D.carrierEmbedding (centralizerEmbedding x) =
          MulAut.conj g (longRootHom p * rootC t * PairStabilizer.blockHom (φ x.2))) ∧
      centralFour.map D.carrierEmbedding =
        (shortRootGroup (F := K)).map (MulAut.conj g).toMonoidHom := by
  let : Finite K := D.field_finite
  obtain ⟨φ,hφ,hC⟩ := CentralizerCoordinates.GroupComparison.comparison
    (D.shortRootCentralizerEmbedding g) (D.shortRootCentralizer_factors g r hr he)
    D.field_card (D.shortRootCentralizerEmbedding_injective g)
  refine ⟨φ, ?_, ?_⟩
  · intro x
    obtain ⟨p,t,hpt⟩ := hφ x
    refine ⟨p,t,?_⟩
    have h := congrArg (MulAut.conj g) hpt
    simpa [shortRootCentralizerEmbedding, MulAut.conj_apply, mul_assoc] using h
  · have hle : centralFour.map D.carrierEmbedding ≤
        (shortRootGroup (F := K)).map (MulAut.conj g).toMonoidHom := by
      rintro _ ⟨_, ⟨⟨c,e⟩,hc,rfl⟩,rfl⟩
      have he : e = 1 := hc.2
      subst e
      obtain ⟨t,ht⟩ := hC c
      refine ⟨rootC t, ⟨Multiplicative.ofAdd t,rfl⟩, ?_⟩
      have h := congrArg (MulAut.conj g) ht
      simpa [shortRootCentralizerEmbedding, MulAut.conj_apply, mul_assoc] using h.symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective D.carrierEmbedding_injective,
      Subgroup.card_map_of_injective (MulAut.conj g).injective,
      centralFour_card, shortRootGroup_card, D.field_card]

/-- The source comparison on the literal W and literal E₄ × A₅ action, with
all three binary fixed/commutator equalities and the actual root-group image. -/
theorem localW_shortRoot_comparison
    (g : Model K) (r : K) (hr : r ≠ 0)
    (he : D.carrierEmbedding a = MulAut.conj g (rootC r)) :
    ∃ φ : A5 ≃* SL(2,K), ∃ E : D.localW.toSubmodule ≃ₗ[K] K × (Fin 2 → K),
      (∀ (c : E4) (e : A5) (w : D.localW.toSubmodule),
        E (D.localW.toRepresentation (c,e) w) = ((E w).1, (φ e).val *ᵥ (E w).2)) ∧
      centralFour.map D.carrierEmbedding =
        (shortRootGroup (F := K)).map (MulAut.conj g).toMonoidHom ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        fixedSpace D.naturalCarrierAction (zpowers a) ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        fixedSpace D.naturalCarrierAction centralFour ∧
      D.localW.toSubmodule.restrictScalars (ZMod 2) =
        subspaceCommutator D.naturalCarrierAction ⊤ centralFour := by
  obtain ⟨φ,hφ,hC⟩ := D.shortRootCentralizer_comparison g r hr he
  refine ⟨φ,D.localWCoordinates g r hr he,?_,hC,
    D.localW_eq_fixedSpace_a g r hr he,
    D.localW_eq_centralFour_fixed g r hr he hC.le,
    D.localW_eq_centralFour_commutator g r hr he hC.le⟩
  intro c e w
  obtain ⟨p,t,hpt⟩ := hφ (c,e)
  exact D.localWCoordinates_action_factor g r hr he (c,e) p t (φ e) hpt w

end MarkedModule
end CFSG.Quasithin.ChapterK.JankoTwo
