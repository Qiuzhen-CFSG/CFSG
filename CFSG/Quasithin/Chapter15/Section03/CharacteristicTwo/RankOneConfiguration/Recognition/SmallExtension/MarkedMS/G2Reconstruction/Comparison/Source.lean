module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Comparison.CriticalImage.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Comparison.LocalSource

/-!
# G₂ critical comparison from the literal endpoint geometry

The starting kernel centralizes the critical commutator. In a marked natural
endpoint quotient, that commutator covers a self-orthogonal space. Invariance
of the octonion polar form therefore puts every displacement in that space.
Lifting through the original projection retains its full kernel; placement
of that kernel in the starting omega-center gives the requested bound.

The endpoint marking and both placements are now constructed in the imported
source modules. The final theorem discharges `DistanceTwoComparisonInput`.
Critical distance two remains independent of this local calculation.
Source: Meierfrankenfeld--Stellmacher (1993), pp.866--868,870--871.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC BinaryMS.MS93
namespace G2Reconstruction.Comparison
universe u
variable {M : Type u} [Group M] [Finite M] {T : Subgroup M}

omit [Finite M] in
/-- The polar-form argument, lifted through the actual endpoint projection.
No splitting of its fixed kernel is assumed. -/
theorem endpoint_commutator_le_image_sup_kernel (z : Vertex T)
    (d : EndpointModel T z) (D Y : Subgroup (FreeAmalgam T))
    (hY : Y ≤ stabilizer T z)
    (hc : Y ≤ centralizer (D : Set (FreeAmalgam T)))
    (W : Submodule (ZMod 2) NaturalSpace)
    (hW : LinearMap.BilinForm.orthogonal Atlas.G2.Natural.BinaryPointFlag.pairing W = W)
    (hcover : ∀ w ∈ W, Multiplicative.ofAdd w ∈
      (D.subgroupOf (Z T z)).map d.projection) :
    ⁅Z T z,Y⁆ ≤ D ⊔ d.projection.ker.map (Z T z).subtype := by
  let π := d.projection
  let α : Y →* Atlas.G2.Model (ZMod 2) := d.actor.comp (inclusion hY)
  have hn : Y ≤ normalizer (Z T z : Set (FreeAmalgam T)) :=
    hY.trans (Z_normalized T z)
  have hact (y : Y) (v : Z T z) :
      π ⟨y.val*v.val*y.val⁻¹,
        (mem_normalizer_iff.mp (hn y.property) v.val).mp v.property⟩ =
      Multiplicative.ofAdd (Atlas.G2.Restricted.NaturalCoordinates.action
        (ZMod 2) (α y) (π v).toAdd) :=
    d.intertwines ⟨y.val,hY y.property⟩ v
  have hfix (y : Y) : ∀ w ∈ W,
      Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (α y) w = w := by
    intro w hw
    obtain ⟨v,hv,he⟩ := hcover w hw
    have hconj : y.val*v.val*y.val⁻¹ = v.val := by
      have hh := hc y.property v.val hv
      rw [←hh,mul_inv_cancel_right]
    have heq : (⟨y.val*v.val*y.val⁻¹,
        (mem_normalizer_iff.mp (hn y.property) v.val).mp v.property⟩ : Z T z) = v :=
      Subtype.ext hconj
    have hi := hact y v
    rw [heq] at hi
    have hi' := congrArg Multiplicative.toAdd hi
    change π v = Multiplicative.ofAdd w at he
    simpa only [he,toAdd_ofAdd] using hi'.symm
  have hdisp (y : Y) (v : NaturalSpace) :
      Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (α y) v-v ∈ W := by
    rw [←hW]
    intro w hw
    change Atlas.G2.Natural.BinaryPointFlag.pairing w
      (Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (α y) v-v) = 0
    rw [map_sub]
    have hi := Atlas.G2.Natural.BinaryPointFlag.pairing_invariant (α y) w v
    rw [hfix y w hw] at hi
    exact sub_eq_zero.mpr hi
  rw [commutator_comm]
  apply commutator_le.mpr
  intro y hy v hv
  have hcv : ⁅y,v⁆ ∈ Z T z :=
    le_normalizer_iff_commutator_le_right.mp hn (commutator_mem_commutator hy hv)
  let c : Z T z := ⟨⁅y,v⁆,hcv⟩
  have he : π c = π ⟨y*v*y⁻¹,(mem_normalizer_iff.mp (hn hy) v).mp hv⟩ *
      (π ⟨v,hv⟩)⁻¹ := by
    rw [←map_inv,←map_mul]
    rfl
  have hw : (π c).toAdd ∈ W := by
    rw [he,hact ⟨y,hy⟩ ⟨v,hv⟩]
    simpa only [toAdd_mul,toAdd_inv,toAdd_ofAdd,sub_eq_add_neg] using
      hdisp ⟨y,hy⟩ (π ⟨v,hv⟩).toAdd
  obtain ⟨v',hv',he'⟩ := hcover (π c).toAdd hw
  let k : Z T z := c*v'⁻¹
  have hk : k ∈ π.ker := by
    change π k = 1
    rw [map_mul,map_inv]
    exact mul_inv_eq_one.mpr (by simpa only [ofAdd_toAdd] using he'.symm)
  have hk' : k.val ∈ π.ker.map (Z T z).subtype := mem_map_of_mem _ hk
  have hm := (D ⊔ π.ker.map (Z T z).subtype).mul_mem
    (mem_sup_right hk') (mem_sup_left hv')
  change (⁅y,v⁆*v'.val⁻¹)*v'.val ∈ D ⊔ π.ker.map (Z T z).subtype at hm
  simpa only [inv_mul_cancel_right] using hm

/-- Apply the natural polar-form calculation to an actual critical endpoint.
The conclusion is stronger than the requested Frattini-plus-X bound. -/
theorem critical_comparison_of_endpoint_placement
    (g : Geometry T) (a z : Vertex T) (ha : color T a = false)
    (hb : g.b T = 2) (hc : CriticalPair T a z (g.exists_critical a ha))
    (d : EndpointModel T z) (hp : EndpointPlacement T a z d) :
    ⁅Q T a,Z T z⁆ ≤ X T a := by
  have hd : (cosetGraph T).dist a z = 2 :=
    hc.1.trans ((g.distance_constant a ha).trans hb)
  obtain ⟨_,_,_,hactor⟩ := distance_two_source_actor g a z ha hb hc
  obtain ⟨hker,W,hW,hcover⟩ := hp
  have hpos : 0 < g.b T := by omega
  have hR : ⁅Z T a,Z T z⁆ ≤ X T a :=
    (critical_image_le_start g a z ha hc).trans
      (g.omega_bound a ha (by rw [g.distance_constant a ha]; exact hpos))
  rw [commutator_comm]
  exact (endpoint_commutator_le_image_sup_kernel z d _ _
    (Q_le_stabilizer_of_dist_two T a z ha hd)
    (hactor.trans inf_le_right) W hW hcover).trans (sup_le hR hker)

/-- Conditional final assembly for this task. Both literal earlier-source
contracts must be discharged to obtain DistanceTwoComparisonInput. -/
theorem distanceTwoComparison_of_endpoint_inputs
    (hm : EndpointModelInput.{u}) (hp : EndpointPlacementInput.{u}) :
    DistanceTwoComparisonInput.{u} := by
  intro J _ _ L R h e hb z hc
  obtain ⟨d⟩ := hm J L R h e hb z hc
  exact (critical_comparison_of_endpoint_placement (geometry h) _ z rfl hb hc d
    (hp J L R h e hb z hc d)).trans le_sup_right

/-- The original whole-core application. Critical distance is independent of
the two local inputs and remains explicit until its separate producer finishes. -/
theorem frattini_small_of_endpoint_inputs
    {J : Type u} [Group J] [Finite J] {L R : Subgroup J}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hd : DistanceTwoInput.{u}) (hm : EndpointModelInput.{u})
    (hp : EndpointPlacementInput.{u}) : FrattiniSmall L R :=
  frattini_small_of_distance_inputs h e hd (distanceTwoComparison_of_endpoint_inputs hm hp)

/-- The G₂ critical comparison at the specified distance-two pair. -/
theorem distanceTwoComparison_knownSimple : DistanceTwoComparisonInput.{u} :=
  distanceTwoComparison_of_endpoint_inputs endpointModelInput_knownSimple
    CriticalImage.endpointPlacement_knownSimple


end G2Reconstruction.Comparison
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
