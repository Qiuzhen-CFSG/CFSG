module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.ModelInput
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.Complement
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.CentralLine
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.FrattiniStructure
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.NaturalQuotient
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.ReducedAction

/-!
# The abelian HS covering core and its natural Frattini section

Earlier centralizer facts and literal model incidences imply that the cover
core is abelian. A model Sylow-seven subgroup lifts to a Sylow subgroup of M;
its fixed subgroup in Q is exactly Z(K), embedded relatively in M. Coprime
action gives the internal direct product, and the covering map identifies the
displacement factor with the model two-core. The central line in Qbar is the
literal image of Z(K). The marked complement gives E ≃ C₂³, its placement in
the centralizer core, and its disjointness from the center. Squaring in the
model C₄³ then identifies the quotient by the central line with the natural
three-dimensional module, using compatible vector and actor coordinates.

All cover incidences, abelianness, decomposition and Frattini premises are
discharged here. The remaining inputs are exactly ModelInput (owned by
qt-i22-hs-normalizer-model-geometry) and CentralizerInput (owned by
qt-i22-hs-centralizer-restriction). The higher HS assembly must supply them;
nonsplitting and the full I.2.2(5) source conclusion are separate results.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.AbelianSection
open Sporadic.LeechRelated.HS.BlockNormalizer
open Sporadic.LeechRelated.HS.EvenLocalCandidates

local instance base_elementary : IsElementaryAbelian 2 baseElementary :=
  elementary_isElementaryAbelian 2

variable {K : Type*} [Group K]

/-- An actual consumer of all three lifted incidence statements. -/
theorem core_incidence_and_abelian [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : CentralizerInput e u) (m : ModelInput) :
    coreCenter u ≤ M e ∧
      (Q e).map (M e).subtype ≤ centralizerTwoResidual u ∧
      normalClosure ((coreCenter u).subgroupOf (M e) : Set (M e)) = Q e ∧
      IsMulCommutative (Q e) := by
  refine ⟨coreCenter_le_M_of_model e u c.center_image m.center_le_normalizer,
    Q_le_residual_of_model e hZ u c.center_le c.residual_image m.core_le_residual,
    normalClosure_coreCenter_eq_Q_of_model e hZ u c.center_le c.center_image
      m.center_le_normalizer m.center_generates, ?_⟩
  exact Q_isMulCommutative_of_model_incidence e hZ u c.center_le c.residual_image
    c.center_image c.centralizes m.core_le_residual m.center_le_normalizer m.center_generates

/-- The source coprime decomposition, including a Sylow witness and the
equivalence of its displacement factor induced by the literal localMap. -/
theorem exists_coprime_core [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : CentralizerInput e u) (m : ModelInput) :
    ∃ Y : Sylow 7 (M e),
      (Y : Subgroup (M e)).map (localMap e) = (m.seven : Subgroup baseNormalizer) ∧
      Q e = ⁅Q e, (Y : Subgroup (M e))⁆ ⊔ centralFactor e ∧
      Disjoint ⁅Q e, (Y : Subgroup (M e))⁆ (centralFactor e) ∧
      Nonempty (Q e ≃* (↥⁅Q e, (Y : Subgroup (M e))⁆ × ↥(centralFactor e))) ∧
      Nonempty (↥⁅Q e, (Y : Subgroup (M e))⁆ ≃* Multiplicative (Fin 3 → ZMod 4)) := by
  let : IsMulCommutative (Q e) := (core_incidence_and_abelian e hZ u c m).2.2.2
  obtain ⟨Y, hmap, hsplit, hd, hprod⟩ :=
    Q_decomposition_of_model_seven e hZ m.seven m.seven_fixed
  exact ⟨Y, hmap, hsplit, hd, hprod,
    ⟨(complementModelEquiv e hZ _ hsplit hd).trans m.coordinates⟩⟩

/-- The two factors remain disjoint inside the literal embedded Qbar. The
second factor is the range of the original center map defining centralLine. -/
theorem quotient_complement_disjoint_central_image [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (D : Subgroup (M e))
    (hED : E e ≤ D) (hd : Disjoint D (centralFactor e)) :
    Disjoint ((D.map (QuotientGroup.mk' (E e))).subgroupOf (Qbar e))
      (centralFrattiniMap e hZ).range := by
  apply disjoint_def.mpr
  intro x hx hz
  apply Subtype.ext
  apply disjoint_def.mp (quotient_complement_disjoint_centralFactor e D hED hd) hx
  rw [← centralFrattiniMap_range_map e hZ]
  exact mem_map_of_mem (Qbar e).subtype hz

/-- The source decomposition and every Frattini incidence, with no cover
decomposition or order assumption. In particular the chosen Sylow subgroup
maps to the specified model Sylow subgroup under the original localMap. -/
theorem exists_coprime_frattini_section [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : CentralizerInput e u) (m : ModelInput) :
    ∃ Y : Sylow 7 (M e),
      (Y : Subgroup (M e)).map (localMap e) = (m.seven : Subgroup baseNormalizer) ∧
      Q e = ⁅Q e, (Y : Subgroup (M e))⁆ ⊔ centralFactor e ∧
      Disjoint ⁅Q e, (Y : Subgroup (M e))⁆ (centralFactor e) ∧
      Nonempty (Q e ≃* (↥⁅Q e, (Y : Subgroup (M e))⁆ × ↥(centralFactor e))) ∧
      Nonempty (↥⁅Q e, (Y : Subgroup (M e))⁆ ≃* Multiplicative (Fin 3 → ZMod 4)) ∧
      E e ≤ ⁅Q e, (Y : Subgroup (M e))⁆ ∧
      Nonempty (E e ≃* Multiplicative (Fin 3 → ZMod 2)) ∧
      Nat.card (E e) = 8 ∧
      E e ≤ (centralizerCore u).subgroupOf (M e) ∧
      Disjoint (E e) (centralFactor e) ∧
      ((E e).map (localMap e)).map baseNormalizer.subtype = baseElementary ∧
      Disjoint (⁅Q e, (Y : Subgroup (M e))⁆.map (QuotientGroup.mk' (E e)))
        ((centralFactor e).map (QuotientGroup.mk' (E e))) ∧
      Disjoint ((⁅Q e, (Y : Subgroup (M e))⁆.map
        (QuotientGroup.mk' (E e))).subgroupOf (Qbar e))
        (centralFrattiniMap e hZ).range := by
  obtain ⟨Y, hmap, hsplit, hd, hprod, hcoords⟩ := exists_coprime_core e hZ u c m
  obtain ⟨hED, hEiso, hE, hER, hEZ, himage, hquot, _⟩ :=
    frattini_structure_of_coprime_decomposition e hZ u c m Y hsplit hd
  exact ⟨Y, hmap, hsplit, hd, hprod, hcoords, hED, hEiso, hE, hER, hEZ, himage,
    hquot, quotient_complement_disjoint_central_image e hZ _ hED hd⟩

/-- The faithful four-dimensional Frattini action has exactly the literal
central invariant line. Its quotient has actual natural coordinates with a
compatible actor identification and the marked square formula in HS.
All extra premises of natural_central_quotient are proved from the inputs. -/
theorem natural_frattini_section [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : CentralizerInput e u) (m : ModelInput) :
    centralLine e hZ = (frattiniRepresentation e).invariants ∧
      Module.finrank (ZMod 2) (centralLine e hZ) = 1 ∧
      Module.finrank (ZMod 2) (Additive (Qbar e)) = 4 ∧
      Function.Injective (frattiniRepresentation e) ∧
      ∃ f : (Additive (Qbar e) ⧸ centralLine e hZ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2),
        (∀ a v, f (NaturalQuotient.quotientRepresentation e hZ a v) =
          (NaturalQuotient.actorEquiv e hZ a : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ f v) ∧
        (∀ q : Q e,
          ((NaturalQuotient.baseCoordinates.symm
            (f (Submodule.Quotient.mk (Additive.ofMul (coreMap e q))))).toMul :
              Sporadic.LeechRelated.HS.Carrier) = modelMap e (q : K) ^ 2) := by
  let : IsMulCommutative (Q e) := (core_incidence_and_abelian e hZ u c m).2.2.2
  obtain ⟨Y, _, hsplit, hd, _, _⟩ := exists_coprime_core e hZ u c m
  obtain ⟨_, _, hE, _, hEZ, himage, _, _⟩ :=
    frattini_structure_of_coprime_decomposition e hZ u c m Y hsplit hd
  obtain ⟨hc, hline, hdim, hfaithful, hintertwines, hsquare⟩ :=
    NaturalQuotient.natural_central_quotient m e hZ himage hEZ hE
  exact ⟨hc, hline, hdim, hfaithful, NaturalQuotient.quotientCoordinates m e hZ himage,
    hintertwines, hsquare⟩

/-- The actual natural reduced action expected by B.4.8(2) and the HS
nonsplitting consumer. No naturality or invariant-space premise remains. -/
noncomputable def naturalFrattiniActionEquiv [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : CentralizerInput e u) (m : ModelInput) :
    ActionEquiv (reducedAction (frattiniRepresentation e))
      (linearNatural BinaryField.two 3) := by
  let h := natural_frattini_section e hZ u c m
  exact NaturalQuotient.reducedActionEquivOfCoordinates e hZ h.1
    (Classical.choose h.2.2.2.2) (Classical.choose_spec h.2.2.2.2).1

/-- The precise abelian-section inputs of Nonsplit.nonsplit_and_fusion,
using its literal kernel, relative commutator and reduced-action conventions.
The higher assembly retains model perfectness, odd index, its involution
witness and the earlier universal B.4.8(2) theorem. -/
theorem nonsplit_inputs [Finite K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (c : CentralizerInput e u) (m : ModelInput) :
    ∃ Y : Sylow 7 (M e),
      Disjoint (localMap e).ker (E e) ∧
      ⁅Q e, (Y : Subgroup (M e))⁆ ⊔ (localMap e).ker = Q e ∧
      Nat.card (E e) = 8 ∧
      E e ≤ (centralizerCore u).subgroupOf (M e) ∧
      Nonempty (ActionEquiv (reducedAction (frattiniRepresentation e))
        (linearNatural BinaryField.two 3)) := by
  obtain ⟨Y, _, hsplit, _, _, _, _, _, hE, hER, hEZ, _, _, _⟩ :=
    exists_coprime_frattini_section e hZ u c m
  refine ⟨Y, ?_, ?_, hE, hER, ⟨naturalFrattiniActionEquiv e hZ u c m⟩⟩
  · rw [localMap_ker]
    exact hEZ.symm
  · rw [localMap_ker]
    exact hsplit.symm

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.AbelianSection
