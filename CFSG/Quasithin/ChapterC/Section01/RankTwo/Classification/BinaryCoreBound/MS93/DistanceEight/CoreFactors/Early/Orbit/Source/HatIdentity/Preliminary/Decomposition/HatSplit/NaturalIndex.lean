module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Representation
public import Theory.SpecificGroups.PSL3Two.OuterInvolutionSinger
public import Theory.GroupTheory.TwoLayerFixedIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.Action
/-!
# The two natural layers inside the moving radius

The actual natural coordinates of V/B remain onto on Vcirc=[V,Ltilde]:
a lift of a Singer matrix has bijective displacement on the natural three-space.
Their kernel contains U, while the residual fixed subgroup is disjoint from
U and also lies in that kernel. Since U and the natural quotient both have
order eight, multiplicativity of relative indices gives fixed index at least
64 in Vcirc. No splitting of V or of Vcirc/H is required.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4) and (4.5.3)(i),
printed pp.890 and 897.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace RankOnePairing.NaturalFactor
variable {G : Type*} [Group G] {π : G →* SL} {V B L : Subgroup G}
private theorem singer_displacement_surjective :
    Function.Surjective (fun v : Fin 3 → ZMod 2 =>
      Matrix.PSL3Two.OuterInvolutionSinger.singer.val.mulVec v - v) := by decide

/-- The natural coordinate map remains onto on the actual residual commutator.
An element above a Singer matrix has bijective displacement on the three-space. -/
theorem commutator_coordinates_surjective
    (n : NaturalFactor π ⊤ V B) (hL : L.map π = ⊤)
    (hW : ⁅V,L⁆ ≤ V) :
    Function.Surjective (n.coordinates.comp (inclusion hW)) := by
  intro y
  obtain ⟨v,hv⟩ := singer_displacement_surjective y.toAdd
  obtain ⟨x,hx⟩ := n.surjective (Multiplicative.ofAdd v)
  obtain ⟨l,hl,he⟩ := (show n.marking.symm Matrix.PSL3Two.OuterInvolutionSinger.singer ∈
      L.map π from hL.symm ▸ mem_top _)
  let z : V := ⟨l*(x:G)*l⁻¹,
    (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp x.property⟩
  let c : (⁅V,L⁆ : Subgroup G) := ⟨⁅l,(x:G)⁆, by
    rw [commutator_comm]; exact commutator_mem_commutator hl x.property⟩
  refine ⟨c, ?_⟩
  have hz : inclusion hW c = z*x⁻¹ := Subtype.ext rfl
  change n.coordinates (inclusion hW c) = y
  rw [hz,map_mul,map_inv]
  apply Multiplicative.toAdd.injective
  change (n.coordinates z).toAdd + -(n.coordinates x).toAdd = y.toAdd
  rw [← sub_eq_add_neg]
  rw [n.action l (mem_top _) x z rfl, he, n.marking.apply_symm_apply, hx]
  exact hv
end RankOnePairing.NaturalFactor
end CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
open Escape.Initial.Natural.Splitting PathCentrality
open Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

theorem moving_fixed_index_ge64
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {b : Vertex R} (hb : color R b = false) :
    (64 : ℕ) ≤ (centralizer (pResidual 2 (stabilizer R b) : Set (stabilizer R b))).relIndex
      ⁅(V R b).subgroupOf (stabilizer R b),pResidual 2 (stabilizer R b)⁆ := by
  let G := stabilizer R b
  let := finite_stabilizer R b
  let V₀ := (V R b).subgroupOf G
  let Z₀ := (Z R b).subgroupOf G
  let U₀ := (U R b).subgroupOf G
  let K := pResidual 2 G
  let W := ⁅V₀,K⁆
  let C := W ⊓ centralizer (K : Set G)
  let := geometry.Z_normal b
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R b)
  obtain ⟨s⟩ := earlier.natural_section b hb
  have hgen : K ⊔ (Q R b).subgroupOf G = ⊤ := by
    apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
      (show Q R b ≤ G from fun _ hx => hx.1)]
    change Ltilde R b ⊔ Q R b = (⊤ : Subgroup G).map G.subtype
    rw [source.local_generation b hb, ← MonoidHom.range_eq_map,range_subtype]
  let n := sectionCoordinates s.module_section (isPPerfect_pResidual 2)
    (source.V_isPGroup geometry common.large_distance b hb).comap_subtype hgen
  have hmap : K.map s.projection = ⊤ := by
    have hh := congrArg (Subgroup.map s.projection) hgen
    rw [Subgroup.map_sup, ← s.module_section.projection_kernel, map_ker_self, sup_bot_eq,
      map_top_of_surjective _ s.module_section.projection_surjective] at hh
    exact hh
  have hWV : W ≤ V₀ := commutator_le_left _ _
  let f := n.coordinates.comp (inclusion hWV)
  have hf : Function.Surjective f := n.commutator_coordinates_surjective hmap hWV
  have hUG : U R b ≤ G := (DistanceEight.U_le_Z R b).trans (Z_le_stabilizer R b)
  have hVG : V R b ≤ G := (PathCentrality.V_le_Q R hb common.large_distance).trans (fun _ hx => hx.1)
  have hUW : U₀ ≤ W := by
    apply (Subgroup.map_le_map_iff_of_injective G.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hUG]
    have hwmap : W.map G.subtype = Vcirc R b := by
      rw [map_commutator,map_subgroupOf_eq_of_le hVG]; rfl
    rw [hwmap]
    exact commutator_mono (Z_le_VBall R b 2) le_rfl
  have hUk : U₀.subgroupOf W ≤ f.ker := by
    intro x hx
    change n.coordinates (inclusion hWV x) = 1
    rw [← MonoidHom.mem_ker,n.kernel]
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hWV x.property, fun l hl => ?_⟩
    exact commutator_le_right K Z₀
      (commutator_mem_commutator hl (show (x:G) ∈ Z₀ from DistanceEight.U_le_Z R b hx))
  have hCk : C.subgroupOf W ≤ f.ker := by
    intro x hx
    change n.coordinates (inclusion hWV x) = 1
    rw [← MonoidHom.mem_ker,n.kernel]
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hWV x.property,fun l hl => ?_⟩
    change ⁅l,(x:G)⁆ ∈ Z₀
    have he : ⁅l,(x:G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hx.2 l hl)
    exact he.symm ▸ Z₀.one_mem
  have hdis : Disjoint U₀ C := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    apply Subtype.ext
    apply (Escape.EdgeTransfer.U_fixed_eq_bot (LocalCommutator.moduleFacts common) b hb).le
    refine ⟨hx.1,?_⟩
    rintro _ ⟨l,hl,rfl⟩
    exact congrArg Subtype.val (hx.2.2 l hl)
  have hh := fixed_index_lower_of_two_layers W U₀ C hUW inf_le_left f hf hUk hCk hdis
  have hUcard : Nat.card U₀ = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUG).toEquiv).trans (common.natural.card_at b hb)
  have hTcard : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; norm_num
  rw [hUcard,hTcard] at hh
  simpa only [C,inf_relIndex_left] using hh
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
