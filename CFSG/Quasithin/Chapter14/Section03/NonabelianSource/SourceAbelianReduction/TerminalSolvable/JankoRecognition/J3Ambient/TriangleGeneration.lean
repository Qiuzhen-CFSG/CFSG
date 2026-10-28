module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.TriangleSimultaneousComplement

/-!
# The literal third parabolic is the common central preimage

The actual point intersection has index five in the order-120 subgroup
containing both original intersections. Its A₄ × C₂ model has no element
inverting a cubic. The genuine inverter in the pair intersection is therefore
outside it. Prime index forces the two actual intersections to generate the
whole central preimage, identifying the original third parabolic itself.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

variable {G : Type*} [Group G] [Finite G]

private theorem join_eq_of_index_five (X Y R : Subgroup G)
    (hXR : X ≤ R) (hYR : Y ≤ R) (hX : Nat.card X = 24) (hR : Nat.card R = 120)
    (y : G) (hy : y ∈ Y) (hyX : y ∉ X) : X ⊔ Y = R := by
  let J := X ⊔ Y
  have hJR : J ≤ R := sup_le hXR hYR
  let U := X.subgroupOf R
  let V := J.subgroupOf R
  have hU : Nat.card U = 24 := (Nat.card_congr (subgroupOfEquivOfLe hXR).toEquiv).trans hX
  have hi : U.index = 5 := by
    have hh := U.card_mul_index
    rw [hU,hR] at hh
    omega
  have hUV : U < V := by
    refine lt_of_le_of_ne (subgroupOf_mono R le_sup_left) ?_
    intro he
    have hyV : (⟨y,hYR hy⟩ : R) ∈ V := mem_sup_right hy
    rw [←he] at hyV
    exact hyX hyV
  have hv : V.index < 5 := hi ▸ index_strictAnti hUV
  have hd : V.index ∣ 5 := hi ▸ index_dvd_of_le hUV.le
  have hVi : V.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hd with h | h
    · exact h
    · omega
  have hVtop : V = ⊤ := index_eq_one.mp hVi
  apply le_antisymm hJR
  intro r hr
  exact (show (⟨r,hr⟩ : R) ∈ V from hVtop ▸ mem_top _)

set_option maxHeartbeats 800000 in
/-- The literal third parabolic has order 120 and retains exactly the
original central involution as its intersection with the full local core. -/
theorem literal_triangle_generation
    {D : Seed G} (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    let f := j SingerField.fieldElement
    let R := third j.range (overlap j) f
    R ≤ Janko23.involutionCentralizer f ∧
      Janko23.ambientCore f ⊓ R = zpowers f ∧
      Janko23.ambientCore f ⊔ R = Janko23.involutionCentralizer f ∧ Nat.card R = 120 := by
  let f := j SingerField.fieldElement
  let s := j cubic
  let H := Janko23.involutionCentralizer f
  let X := j.range ⊓ H
  let Y := normalizer (overlap j : Set G) ⊓ H
  obtain ⟨R,hRH,hXR,hYR,hQR,hgen,hR⟩ := literal_triangle_simultaneous_complement P hc A C a j hj
  obtain ⟨y,hy,_hy2,hys,_hYgen⟩ := literal_triangle_pair_generators P hc A C a j hj
  let eX : X ≃* (alternatingGroup (Fin 4) × Multiplicative (ZMod 2)) :=
    PointCentralizer.imagePointCentralizerEquiv j hj.1
  have hX : Nat.card X = 24 := by
    rw [Nat.card_congr eX.toEquiv,Nat.card_prod,
      alternatingGroup.card_of_card_eq_four (by simp)]
    norm_num [Nat.card_eq_fintype_card]
  have hsX : s ∈ X := by
    refine ⟨⟨cubic,rfl⟩,mem_centralizer_singleton_iff.mpr ?_⟩
    exact ((cubic_commutes_complement
      ⟨SingerField.fieldElement,(mem_pointComplement _).mpr rfl⟩).map j).eq
  let sX : X := ⟨s,hsX⟩
  have hs : orderOf sX = 3 :=
    (orderOf_coe sX).symm.trans ((orderOf_injective j hj.1 _).trans cubic_order)
  have hyX : y ∉ X := by
    intro hyX
    let yX : X := ⟨y,hyX⟩
    have hno : ∀ u v : alternatingGroup (Fin 4) × Multiplicative (ZMod 2),
        u^3=1 → u≠1 → v*u*v⁻¹ ≠ u⁻¹ := by decide +kernel
    have hu := orderOf_eq_prime_iff.mp ((eX.orderOf_eq sX).trans hs)
    apply hno (eX sX) (eX yX) hu.1 hu.2
    have hh : yX*sX*yX⁻¹=sX⁻¹ := Subtype.ext hys
    simpa only [map_mul,map_inv] using congrArg eX hh
  have he : X ⊔ Y = R := join_eq_of_index_five X Y R hXR hYR hX hR y hy hyX
  change X ⊔ Y ≤ H ∧ Janko23.ambientCore f ⊓ (X ⊔ Y) = zpowers f ∧
    Janko23.ambientCore f ⊔ (X ⊔ Y) = H ∧ Nat.card (X ⊔ Y : Subgroup G) = 120
  rw [he]
  exact ⟨hRH,hQR,hgen,hR⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
