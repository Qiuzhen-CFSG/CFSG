module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.LocalControl.Auxiliary
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Comparison.CriticalImage.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.Reduction

/-!
# The G₂ local clauses of the critical-distance criterion

The original Frattini condition makes Y joined with the starting X-layer an
elementary two-group. Thus Y centralizes the critical commutator. The exact
endpoint actor kernel and its natural pointwise stabilizer put [Y,Z_z] inside
that commutator. This proves MS93 (2.3)(c) for every actual critical pair.

The imported auxiliary construction proves (2.3)(d) on the same actual edge.
Together these discharge the local-control record and force critical distance
four whenever it exceeds two. Excluding distance four remains a later argument.
Source: MS93 (2.3), pp.857–859, and the G₂ case of (3.8), pp.877–879.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo
open ChapterC BinaryMS.MS93 Comparison.CriticalImage
universe u

/-- The full source (2.3)(c), with the original far endpoint and Frattini join. -/
theorem commutatorControl_knownSimple {G : Type*} [Group G] [Finite G]
    {L R : Subgroup G} (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    CriticalCriterion.CommutatorControl (R.subgroupOf (L ⊔ R)) (geometry h) := by
  let T := R.subgroupOf (L ⊔ R)
  let g := geometry h
  have hpos := (positive_even h e).1
  have hC := edgeCentralizer h e
  intro a ha z hc
  have hz := critical_endpoint_color T a ha _ hc
  have hba : 0 < criticalDistance T a (g.exists_critical a ha) := by
    rw [g.distance_constant a ha]; exact hpos
  have hbz : 0 < criticalDistance T z (g.exists_critical z hz) := by
    rw [g.distance_constant z hz]; exact hpos
  have hrev := critical_reverse T g hC a ha hba z hz hc
  obtain ⟨da⟩ := endpointModel_knownSimple h e ha
  obtain ⟨dz⟩ := endpointModel_knownSimple h e hz
  refine ⟨Z T z,⟨g.omega_bound z hz hbz,hrev.2,?_⟩⟩
  intro t ht Y hY hΦ
  have hXt : X T a ≤ Q T t := by
    apply X_le_Q_of_dist_lt T g hC a ha t
    have he := hc.1
    have hp := ht.2
    change (cosetGraph T).dist a t + 1 = (cosetGraph T).dist a z at hp
    change (cosetGraph T).dist a z = criticalDistance T a (g.exists_critical a ha) at he
    omega
  have hjoin : Y ⊔ X T a ≤ Q T t := sup_le hY hXt
  have hQS : Q T t ≤ stabilizer T z :=
    CriticalCriterion.edge_le_stabilizer T hz ht.1
  let := CriticalCriterion.finite_of_le_stabilizer T (hjoin.trans hQS)
  have hp : IsPGroup 2 (Q T t) := by
    obtain ⟨f,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common T z t).mp ht.1
    · have hh := Q_act T f (beta T)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh,show Q T (hVertex T 1) = T.map (embedM T) from Q_beta T]
      exact ((edge_two_group h).map _).map _
    · cases hz
  let : Fact (IsPGroup 2 (Y ⊔ X T a : Subgroup (FreeAmalgam T))) :=
    ⟨hp.of_injective (inclusion hjoin) (inclusion_injective hjoin)⟩
  let : IsElementaryAbelian 2 (Y ⊔ X T a : Subgroup (FreeAmalgam T)) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hΦ
  have hcent : Y ≤ centralizer (X T a : Set (FreeAmalgam T)) := by
    intro y hy x hx
    exact congrArg Subtype.val (mul_comm
      (⟨x,mem_sup_right hx⟩ : ↥(Y ⊔ X T a)) ⟨y,mem_sup_left hy⟩)
  have hD : ⁅Z T a,Z T z⁆ ≤ X T a :=
    (Comparison.critical_image_le_start g a z ha hc).trans (g.omega_bound a ha hba)
  exact (critical_commutator_le g hC a z ha hpos hc da dz Y
    (hY.trans hQS) (hcent.trans (centralizer_le hD))).trans
      ((commutator_mono (g.omega_bound a ha hba) (g.omega_bound z hz hbz)).trans le_sup_left)

/-- The commutator clause of (2.3) is proved; the actual edge auxiliary remains. -/
theorem localControl_of_auxiliary {G : Type*} [Group G] [Finite G]
    {L R : Subgroup G} (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (haux : ∀ a (ha : color (R.subgroupOf (L ⊔ R)) a = false) z,
      CriticalPair (R.subgroupOf (L ⊔ R)) a z ((geometry h).exists_critical a ha) →
      ∀ t, Adjacent (R.subgroupOf (L ⊔ R)) a t →
        (cosetGraph (R.subgroupOf (L ⊔ R))).dist t z + 1 =
          (cosetGraph (R.subgroupOf (L ⊔ R))).dist a z →
        ∃ A, CriticalCriterion.EdgeWitness (R.subgroupOf (L ⊔ R)) (geometry h) a t A) :
    LocalControl h :=
  ⟨commutatorControl_knownSimple h e,haux⟩

/-- Apply the proved commutator clause to the original critical-distance criterion. -/
theorem distance_four_of_auxiliary {G : Type*} [Group G] [Finite G]
    {L R : Subgroup G} (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hb : 2 < (geometry h).b (R.subgroupOf (L ⊔ R)))
    (haux : ∀ a (ha : color (R.subgroupOf (L ⊔ R)) a = false) z,
      CriticalPair (R.subgroupOf (L ⊔ R)) a z ((geometry h).exists_critical a ha) →
      ∀ t, Adjacent (R.subgroupOf (L ⊔ R)) a t →
        (cosetGraph (R.subgroupOf (L ⊔ R))).dist t z + 1 =
          (cosetGraph (R.subgroupOf (L ⊔ R))).dist a z →
        ∃ A, CriticalCriterion.EdgeWitness (R.subgroupOf (L ⊔ R)) (geometry h) a t A) :
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 4 :=
  distance_four_of_localControl h e hb (localControl_of_auxiliary h e haux)

/-- Both source (2.3)(c,d) hold for every original small G₂ MS pair. -/
theorem localControl_knownSimple : LocalControlInput.{u} := by
  intro J _ _ L R h e _
  exact localControl_of_auxiliary h e (edgeWitness_knownSimple h e)

/-- The actual critical distance above two is four, with no local-control premise. -/
theorem distance_four_knownSimple {G : Type*} [Group G] [Finite G]
    {L R : Subgroup G} (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hb : 2 < (geometry h).b (R.subgroupOf (L ⊔ R))) :
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 4 :=
  distance_four_of_localControl h e hb (localControl_knownSimple G L R h e hb)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo
