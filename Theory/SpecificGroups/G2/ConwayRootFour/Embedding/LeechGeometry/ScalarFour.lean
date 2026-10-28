module

public import Theory.AtlasPort.Janko2.Conway.IcosianAlternatingConwayProduct
public import Theory.AtlasPort.OtherSporadic.Conway.LeechQuotientActions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# A tetrahedral scalar subgroup in the actual Conway quotient

The existing icosian scalar comparison embeds the alternating group on five
points in the Leech central quotient. Restrict it to four points to obtain
`I`, and map its normal Klein four subgroup to obtain `U`. The relative
identity `I_core` identifies this U with O₂(I); no ambient normality is used.
The existing projective icosian J₂ image centralizes I.

We define V = C_(Λ/2Λ)(U) using the actual quotient action and prove that
C_G(I) preserves V. The separate assertion `CentralizerFaithful` is the
remaining kernel calculation on V, not an assumed instance or a theorem.
The local-coordinate construction consumes these exact subgroups and V.

Source: Aschbacher, *Sporadic Groups* (1994), Section 48, printed p.269,
and the local construction in Lemma 49.5, printed pp.283–284. The imported
icosian and Leech models are attributed ATLAS ports. This module constructs
the subgroups but does not identify their involutions with the source
root-four class; the required marking remains a genuine conjugacy obligation.
-/

@[expose] public noncomputable section

open Atlas.Codes Atlas.Lattices Atlas.Conway
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry

/-- Four of the five points in the existing scalar projective action. -/
def fourPoints : Finset (Fin 5) := {0, 1, 2, 3}

theorem fourPoints_card : Nat.card fourPoints = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The actual scalar A₅ in the Leech central quotient. -/
def scalarFive : alternatingGroup (Fin 5) →* LeechCentralQuotient :=
  icosianScalarProjectiveToCo1.comp icosianScalarProjectiveAlternating.symm.toMonoidHom

theorem scalarFive_injective : Function.Injective scalarFive :=
  icosianScalarProjectiveToCo1_injective.comp icosianScalarProjectiveAlternating.symm.injective

/-- Extend a permutation of the chosen four points, then use the scalar embedding. -/
def scalarFour : alternatingGroup fourPoints →* LeechCentralQuotient :=
  scalarFive.comp (alternatingGroup.ofSubtype fourPoints)

theorem scalarFour_injective : Function.Injective scalarFour :=
  scalarFive_injective.comp alternatingGroup.ofSubtype_injective

/-- The specified tetrahedral subgroup of the concrete scalar A₅. -/
def I : Subgroup LeechCentralQuotient := scalarFour.range

/-- Its actual normal Klein four subgroup. -/
def U : Subgroup LeechCentralQuotient :=
  (alternatingGroup.kleinFour fourPoints).map scalarFour

def tetrahedralEquiv : alternatingGroup fourPoints ≃* I :=
  MonoidHom.ofInjective scalarFour_injective

def fourEquiv : alternatingGroup.kleinFour fourPoints ≃* U :=
  Subgroup.equivMapOfInjective _ scalarFour scalarFour_injective

theorem I_card : Nat.card I = 12 := by
  rw [← Nat.card_congr tetrahedralEquiv.toEquiv]
  exact alternatingGroup.card_of_card_eq_four fourPoints_card

theorem U_card : Nat.card U = 4 := by
  rw [← Nat.card_congr fourEquiv.toEquiv]
  exact alternatingGroup.kleinFour_card_of_card_eq_four fourPoints_card

instance U_isKleinFour : IsKleinFour U where
  card_four := U_card
  exponent_two := by
    rw [← Monoid.exponent_eq_of_mulEquiv fourEquiv]
    exact alternatingGroup.exponent_kleinFour_of_card_eq_four fourPoints_card

theorem U_le_I : U ≤ I := Subgroup.map_le_range _ _

private theorem tetrahedral_core :
    pCore 2 (alternatingGroup fourPoints) = alternatingGroup.kleinFour fourPoints := by
  obtain ⟨S : Sylow 2 (alternatingGroup fourPoints)⟩ :=
    Sylow.nonempty (G := alternatingGroup fourPoints)
  have hS := alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four fourPoints_card S
  apply le_antisymm
  · simpa only [hS] using pCore_isPGroup.le_sylow_of_normal S
  · exact le_sSup ⟨alternatingGroup.normal_kleinFour fourPoints_card, hS ▸ S.isPGroup'⟩

/-- The two-core is taken inside I and then mapped to the ambient Conway quotient. -/
theorem I_core : I.pCoreIn 2 = U := by
  unfold Subgroup.pCoreIn
  rw [← pCore_map_iso 2 tetrahedralEquiv, Subgroup.map_map, tetrahedral_core]
  rfl

/-- Normality is relative to the tetrahedral subgroup. -/
theorem I_le_normalizer_U : I ≤ Subgroup.normalizer (U : Set LeechCentralQuotient) := by
  let _ := alternatingGroup.normal_kleinFour fourPoints_card
  have h := (alternatingGroup.kleinFour fourPoints).le_normalizer_map scalarFour
  simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, I, U] using h

/-- A three-cycle in the chosen tetrahedral group. -/
def threeCycle : alternatingGroup fourPoints :=
  ⟨Equiv.swap ⟨0, by decide⟩ ⟨1, by decide⟩ *
    Equiv.swap ⟨1, by decide⟩ ⟨2, by decide⟩, by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide⟩

def y : LeechCentralQuotient := scalarFour threeCycle

theorem y_order : orderOf y = 3 := by
  rw [y, orderOf_injective scalarFour scalarFour_injective]
  exact orderOf_eq_prime (by decide : threeCycle ^ 3 = 1) (by decide : threeCycle ≠ 1)

/-- The order-three subgroup used to recover the four-element scalar field. -/
def Y : Subgroup LeechCentralQuotient := Subgroup.zpowers y

theorem Y_card : Nat.card Y = 3 := by rw [Y, Nat.card_zpowers, y_order]

theorem Y_le_I : Y ≤ I := Subgroup.zpowers_le.mpr ⟨threeCycle, rfl⟩

/-- Centralizing the tetrahedral group, rather than just its four-group. -/
def centralizerI : Subgroup LeechCentralQuotient := Subgroup.centralizer (I : Set _)

theorem janko_mem_centralizerI (g : IcosianProjectiveModel) :
    icosianProjectiveToCo1 g ∈ centralizerI := by
  rintro _ ⟨a, rfl⟩
  exact (icosianScalarProjective_commute
    (icosianScalarProjectiveAlternating.symm (alternatingGroup.ofSubtype fourPoints a)) g).eq

/-- The source's fixed space inside the literal lattice quotient. -/
def fixedSpace : Submodule Bit LeechModTwo where
  carrier := {v | ∀ u ∈ U, quotientModTwoRepresentation u v = v}
  zero_mem' := by intro u hu; exact map_zero _
  add_mem' := by intro v w hv hw u hu; rw [map_add, hv u hu, hw u hu]
  smul_mem' := by intro c v hv u hu; rw [map_smul, hv u hu]

theorem mem_fixedSpace (v : LeechModTwo) :
    v ∈ fixedSpace ↔ ∀ u ∈ U, quotientModTwoRepresentation u v = v := Iff.rfl

theorem centralizerI_preserves_fixedSpace {g : LeechCentralQuotient}
    (hg : g ∈ centralizerI) {v : LeechModTwo} (hv : v ∈ fixedSpace) :
    quotientModTwoRepresentation g v ∈ fixedSpace := by
  intro u hu
  have hc : u * g = g * u := hg u (U_le_I hu)
  calc
    quotientModTwoRepresentation u (quotientModTwoRepresentation g v) =
        quotientModTwoRepresentation (u * g) v := by rw [map_mul]; rfl
    _ = quotientModTwoRepresentation (g * u) v := by rw [hc]
    _ = quotientModTwoRepresentation g v := by rw [map_mul]; exact congrArg _ (hv u hu)

/-- The geometric kernel assertion on the literal U-fixed space. Its proof
must use the actual Leech action, not just centralization of U. -/
def CentralizerFaithful : Prop :=
  ∀ g ∈ centralizerI,
    (∀ v ∈ fixedSpace, quotientModTwoRepresentation g v = v) → g = 1

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry
