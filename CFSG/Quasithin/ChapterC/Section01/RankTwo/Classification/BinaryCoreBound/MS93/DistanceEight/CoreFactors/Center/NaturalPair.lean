module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.Upper
public import Theory.Representation.BinaryThreeHomSaturation.NaturalPair
public import Theory.GroupTheory.HomSupExtension
/-!
# The actual natural pair on the third residual layer

The core commutator row is onto Hom(first dual,H), and its kernel is exactly
the second-hat intersection. Extend the row across the second hat, retaining
the original conjugation formula, and choose two scalar coordinates on H.
Double-dual coordinates then give the natural pair with the same SL3 marking
as CommonFacts. Every source premise is discharged from CommonFacts and Earlier.

This proves (4.5.4)(iv) with the natural action used by its proof and by
(4.5)(vii); the printed word "dual" in the statement of (iv) conflicts with
those two passages. No new orientation, generation or independence input is used.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.895,898--899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open NormalizerTransfer PathCentrality Higher DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem extended_row_action (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    [IsMulCommutative (H R (alpha R))]
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (q : (core R (alpha R) ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :
      Subgroup (FreeAmalgam R)) →* (Multiplicative W →* H R (alpha R)))
    (hk : q.ker = (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
      (core R (alpha R) ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)))
    (he : ∀ a : core R (alpha R), q (inclusion le_sup_left a) =
      coreCommutatorRow common earlier p s a) :
    ∀ (m : M) (x y : (core R (alpha R) ⊔
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Subgroup (FreeAmalgam R))),
      (y : FreeAmalgam R) = embedM R m * x * (embedM R m)⁻¹ →
      ∀ v : W, q y (Multiplicative.ofAdd (dual (common.natural.marking (source.projection m)) v)) =
        q x (Multiplicative.ofAdd v) := by
  let K := core R (alpha R)
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  have hlocal : K ≤ stabilizer R (alpha R) := fun _ hx => (DistanceTwo.core_le_Q _ hx).1
  have hn : K ≤ normalizer B := hlocal.trans (hatW_normalized R _ _ _)
  have hB : Mbar R ≤ normalizer B := by
    simpa only [B,alpha,stabilizer_m_base] using hatW_normalized R (alpha R)
      (p.walk.getVert 6) (p.walk.getVert 8)
  have hkill (b : B) : q (inclusion le_sup_right b) = 1 := MonoidHom.mem_ker.mp (hk ▸ b.property)
  intro m x y hy v
  have hx : (x : FreeAmalgam R) ∈ (K : Set (FreeAmalgam R)) * (B : Set (FreeAmalgam R)) := by
    rw [← coe_mul_of_left_le_normalizer_right K B hn]
    exact x.property
  obtain ⟨a,ha,b,hb,hab⟩ := hx
  let a' : K := ⟨embedM R m * a * (embedM R m)⁻¹,
    le_normalizer_iff.mp HomSaturation.core_normalized _ ⟨m,rfl⟩ _ ha⟩
  let b' : B := ⟨embedM R m * b * (embedM R m)⁻¹,
    le_normalizer_iff.mp hB _ ⟨m,rfl⟩ _ hb⟩
  have hx' : x = inclusion le_sup_left (⟨a,ha⟩ : K) * inclusion le_sup_right (⟨b,hb⟩ : B) :=
    Subtype.ext hab.symm
  have hy' : y = inclusion le_sup_left a' * inclusion le_sup_right b' := by
    apply Subtype.ext
    change (y : FreeAmalgam R) =
      (embedM R m * a * (embedM R m)⁻¹) * (embedM R m * b * (embedM R m)⁻¹)
    rw [hy,← hab]
    group
  rw [hy',hx',map_mul,map_mul,hkill,hkill,mul_one,mul_one,he,he]
  exact coreCommutatorRow_action common earlier p s m ⟨a,ha⟩ a' rfl v

/-- The actual core modulo its second-hat intersection is a marked natural pair. -/
theorem core_second_marked_natural_pair (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nonempty (MarkedPairSection source common
      (core R (alpha R) ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false) := by
  let := H_elementary_of_central R (alpha R)
    (geometry.V_local _ rfl common.large_distance) (earlier.centrality _ rfl)
  obtain ⟨s⟩ := Quotients.FirstDirect.markedDualSection common earlier p
  let K := core R (alpha R)
  let B := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  have hK : K ≤ stabilizer R (alpha R) := fun _ hx => (DistanceTwo.core_le_Q _ hx).1
  have hB : B ≤ stabilizer R (alpha R) :=
    (hatW_le_radius R (Early.Orbit.SourceApplications.higherPath geometry p).two_step_distances.1.le
      (Early.Orbit.SourceApplications.higherPath geometry p).two_step_distances.2.1.le).trans
      ((Escape.Propagation.RadiusFour.VBall_le_Q (alpha R) rfl 4
        (by rw [earlier.distance]; decide)).trans (fun _ hx => hx.1))
  have hn : K ≤ normalizer B := hK.trans (hatW_normalized R _ _ _)
  have hBn : Mbar R ≤ normalizer B := by
    simpa only [B,alpha,stabilizer_m_base] using hatW_normalized R (alpha R)
      (p.walk.getVert 6) (p.walk.getVert 8)
  obtain ⟨q,honto,hker,he⟩ := MonoidHom.exists_sup_extension hn
    (coreCommutatorRow common earlier p s) (coreCommutatorRow_surjective common earlier p s)
    (coreCommutatorRow_kernel common earlier p s)
  have hH : Nat.card (H R (alpha R)) = 4 := Nat.le_antisymm
    (Early.H_card_le_four common earlier rfl) (Early.First.Layer.H_card_lower common earlier (alpha R) rfl)
  obtain ⟨e⟩ := Representation.BinaryThreeHom.exists_binary_pair_equiv hH
  let E := Representation.BinaryThreeHom.groupPairEquiv e
  refine ⟨{
    local_group := sup_le hK hB
    lower_le := le_sup_right
    normalized := (le_inf HomSaturation.core_normalized hBn).trans
      (normalizer_inf_normalizer_le_normalizer_sup K B)
    quotient := E.toMonoidHom.comp q
    onto := E.surjective.comp honto
    kernel := ?_
    action := ?_ }⟩
  · ext x
    change E (q x) = 1 ↔ x ∈ B.subgroupOf (K ⊔ B)
    rw [map_eq_one_iff E E.injective]
    exact SetLike.ext_iff.mp hker x
  · intro m x y hy
    exact Representation.BinaryThreeHom.groupPairEquiv_action e (q x) (q y)
      (common.natural.marking (source.projection m))
      (extended_row_action common earlier p s q hker he m x y hy)

/-- Source (4.5.4)(iv), with the original vertices and the natural action required by (4.5)(vii). -/
theorem moving_marked_natural_pair (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    Nonempty (MarkedPairSection source common
      (⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        Ltilde R (alpha R)⁆ ⊔ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)) false) := by
  rw [← core_eq_third_residual common earlier p]
  exact core_second_marked_natural_pair common earlier p
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
