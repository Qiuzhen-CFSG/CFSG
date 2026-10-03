module

public import Stellmacher.Recognition.GTwoSixtyFourInitialEightGeometry
public import Stellmacher.Recognition.GTwoSixtyFourPairNormalizerReduction
public import Theory.GroupTheory.NormalAbelianSylowCentralizerControl
public import Theory.GroupTheory.C4SquareElementaryIntersection

/-!
# The initial vertex's plane image on a normal elementary eight

An elementary eight in the initial core, normalized by the initial vertex,
is self-centralizing in the supplied Sylow. Its normalizer is two-local and
has trivial odd core. Burnside transfer in the centralizer therefore makes
the eight self-centralizing in the ambient group. The initial vertex has
order 192, so its conjugation image has order 24.

The invariant plane is the intersection with the C₄ × C₄ base of the
initial core. This base is the two-core of the initial two-residual and
hence normal in the initial vertex. Its index two in the core, together
with its four involutions, gives the plane order four.

Source: Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`, and the
generalized-dihedral core geometry. The construction of the eight is not
needed for this action theorem.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- Every initial-vertex-normal elementary eight in the initial core carries
an actual order-24 plane stabilizer image. -/
public theorem gTwo_card64_initial_eight_plane_image
    {G : Type*} [Group G] [Finite G] (_hN : IsNTwoGroup G)
    (hcore : ∀ V : Subgroup G, IsTwoLocal V → pPrimeCore 2 V = ⊥)
    (data : GTwoTwoDerivedTypeData G) (hcard : Nat.card data.sylowIntersection = 64)
    (U : Subgroup G) [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) :
    letI := data.groupK
    letI := data.finiteK
    U ≤ (QAt data.Γ data.criticalPath.a).map data.embedding →
    (GAt data.Γ data.criticalPath.a).map data.embedding ≤
      Subgroup.normalizer (U : Set G) →
    Nonempty (ElementaryEightPlaneImage U) := by
  let := data.groupK
  let := data.finiteK
  intro hUQ hPN
  let P0 := GAt data.Γ data.criticalPath.a
  let E0 := EAt data.Γ data.criticalPath.a
  let Q0 := QAt data.Γ data.criticalPath.a
  let A0 := twoCoreIn E0
  let P := P0.map data.embedding
  let Q := Q0.map data.embedding
  let A := A0.map data.embedding
  have hSP : (data.sylowIntersection : Subgroup G) ≤ P := by
    rw [← data.intersection_eq]
    exact inf_le_left
  have hSN := hSP.trans hPN
  have hselfS := (gTwo_card64_initial_eight_geometry data hcard U hU hSN hUQ).2
  have hne : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hU
    omega
  have hself : Subgroup.centralizer (U : Set G) = U :=
    data.sylowIntersection.centralizer_eq_of_inf_eq_of_normalizer_pPrimeCore_eq_bot
      U hSN hselfS (hcore _ ⟨U, hne, IsElementaryAbelian.isPGroup 2 U, rfl⟩)
  have hUP : U ≤ P := (hselfS.ge.trans inf_le_left).trans hSP
  have hPcard : Nat.card P = 192 := by
    rw [Subgroup.card_map_of_injective data.embedding_injective]
    exact (gTwo_card64_vertex_structure data hcard).2.1
  have hQcard : Nat.card Q = 32 := by
    rw [Subgroup.card_map_of_injective data.embedding_injective]
    exact (gTwo_card64_vertex_structure data hcard).1
  have hAQ : A ≤ Q := by
    apply Subgroup.map_mono
    obtain ⟨_, _, _, _, hgen⟩ := gTwo_card64_outside_inverter data hcard
    change A0 ≤ Q0
    dsimp only [A0, Q0, E0]
    rw [hgen]
    exact le_sup_left
  have hAmodel : Nonempty (A ≃* C4 × C4) := by
    obtain ⟨e⟩ := data.caseA.twoCore_model
    exact ⟨(A0.equivMapOfInjective data.embedding data.embedding_injective).symm.trans e⟩
  have hE : E0 = twoResidualIn P0 := data.Γ.twoResidualAt_def _
  have hEP : E0 ≤ P0 := by rw [hE]; exact twoResidualIn_le _
  have hEN : (E0.subgroupOf P0).Normal := by rw [hE]; exact twoResidualIn_normal _
  have hAP : A0 ≤ P0 := (twoCoreIn_le E0).trans hEP
  have hAN : (A0.subgroupOf P0).Normal := twoCoreIn_normal_of_normal E0 P0 hEP hEN
  have hPA : P ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mp hAN)).trans
      (Subgroup.le_normalizer_map data.embedding)
  apply elementaryEight_plane_image_of_normalizing_subgroup U P hU hPcard hPN
    (by rw [hself]; exact inf_eq_right.mpr hUP) (A.subgroupOf U)
    (Subgroup.c4_square_intersection_elementary_eight_card A Q U hAmodel hAQ hQcard hU hUQ)
  intro p u
  change (p : G) * (u : G) * (p : G)⁻¹ ∈ A ↔ (u : G) ∈ A
  exact (Subgroup.mem_normalizer_iff.mp (hPA p.property) (u : G)).symm

end Stellmacher.Recognition
