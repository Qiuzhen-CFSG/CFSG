module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalMovedSpace
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFullSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer

/-!
# Original cubic commutator indices and edge planes

The commutator of the original moving cover with any actor has central
index equal to the order of its natural displacement space. For a two-actor,
its permutation-image order is exactly its index over the original two-core:
the odd quotient E/Q is retained. Image order greater than two therefore
forces central commutator index at least four, both on U and on the full Z.

In the plane branch the whole edge commutator has central index four.
Every large edge subactor fills the same commutator plane modulo the full
central seed, and its literal commutator has order four or eight. Both
moving covers, their entire central attachment, and the original graph
are retained. No distance or critical-path hypotheses are needed.

The internal imports reuse the existing cubic cover coordinates, faithful
edge coordinates, full-seed commutator equality, and central-attachment
bound. No private declaration occurs in a public statement, and no natural
Replacement hypothesis is instantiated.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), pp.866--867, and the H comparison in (5.11)(2), p.924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)

/-- The full original cover commutator modulo the ambient center has the
natural displacement order, for both permitted cover sizes. -/
theorem cover_commutator_central_index (A : Subgroup M) :
    (center M).relIndex ⁅W,A⁆ =
      2 ^ fixedCodim (naturalRepresentation (Fin 6)) (A.map π) := by
  let := h.relative_normal
  let f := coverProjection h e hz hk
  let ρ := naturalRepresentation (Fin 6)
  let p := coverMap h e hz hk
  let J := ⁅W,A⁆
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have hW : subgroupSpace W W = ⊤ := by
    ext v
    exact iff_of_true v.toMul.property trivial
  have hJ : subgroupSpace W J =
      subspaceCommutator (coverAction h e hz hk) ⊤ (A.map π) := by
    rw [subgroupSpace_commutator W π (CubicEven.projection_surjective h e hz hk)
      hker W A le_rfl,hW]
  have hm := subspaceCommutator_map_embedding ρ (coverAction h e hz hk)
    (MonoidHom.id (Equiv.Perm (Fin 6))) p
    (fun g v => (coverMap_equivariant h e hz hk g v).symm) (A.map π) ⊤
  rw [Subgroup.map_id,Submodule.map_top,
    LinearMap.range_eq_top.mpr (coverMap_surjective h e hz hk),←hJ] at hm
  have hcard : Nat.card ((J.subgroupOf W).map f) =
      Nat.card ((subgroupSpace W J).map p) := by
    apply Nat.card_congr
    exact {
      toFun := fun v => ⟨v.val.toAdd,by
        obtain ⟨x,hx,he⟩ := v.property
        exact ⟨Additive.ofMul x,hx,congrArg Multiplicative.toAdd he⟩⟩
      invFun := fun v => ⟨Multiplicative.ofAdd v.val,by
        obtain ⟨x,hx,he⟩ := v.property
        exact ⟨x.toMul,hx,congrArg Multiplicative.ofAdd he⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hkf : f.ker = (center M).subgroupOf W := coverProjection_kernel_center h e hz hk
  rw [←relIndex_subgroupOf (L := W) (commutator_le_left W A),←hkf,relIndex_ker]
  change Nat.card ((⁅W,A⁆.subgroupOf W).map f) = _
  rw [hcard,←hm,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    NaturalPairing.moved_finrank_eq_fixedCodim]

include h e hz hk in
/-- A large original two-actor has commutator central index at least four.
The two-group hypothesis retains the actual odd quotient E/Q. -/
theorem cover_large_actor_commutator_index (A : Subgroup M)
    (htwo : IsPGroup 2 A) (hlarge : 2 < (pCore 2 M).relIndex A) :
    4 ≤ (center M).relIndex ⁅W,A⁆ := by
  have hcard : 2 < Nat.card (A.map π) := by
    rwa [CubicAction.permutation_image_card_of_two h e hz hk A htwo]
  have hdim : 2 ≤ fixedCodim (naturalRepresentation (Fin 6)) (A.map π) := by
    by_contra! hsmall
    have hne : A.map π ≠ ⊥ := by
      intro he
      rw [he,card_bot] at hcard
      omega
    obtain ⟨t,_,ht,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
      (A.map π) hne (by
        change fixedCodim (naturalRepresentation (Fin 6)) _ ≤ 1
        omega)
    rw [he,Nat.card_zpowers,ht.orderOf] at hcard
    omega
  rw [cover_commutator_central_index h e hz hk]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hdim

private theorem centralizer_comap_of_range
    {F H : Type*} [Group F] [Group H] (i : F →* H) (hi : Function.Injective i)
    (P : Subgroup H) (hir : i.range = P) :
    (centralizer (P : Set H)).comap i = center F := by
  ext x
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro g
    apply hi
    simpa only [map_mul] using hx (i g) (hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩))
  · intro hx g hg
    obtain ⟨y,rfl⟩ := hir.symm ▸ hg
    simpa only [map_mul] using congrArg i ((mem_center_iff.mp hx) y)

include h e hz hk in
/-- The moving-cover lower bound at every original component vertex. -/
theorem graph_large_actor_moving_commutator_index
    {a : Vertex Rg} (ha : color Rg a = false)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg a)
    (htwo : IsPGroup 2 A) (hlarge : 2 < (Q Rg a).relIndex A) :
    4 ≤ (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex
      ⁅U Rg a,A⁆ := by
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a ha
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hidx : 2 < (pCore 2 M).relIndex (A.comap i) := by
    rw [←relIndex_map_map_of_injective _ _ hi,hmA,hiQ]
    exact hlarge
  have hC := centralizer_comap_of_range i hi (stabilizer Rg a) hir
  have hm : (⁅W,A.comap i⁆ : Subgroup M).map i = ⁅U Rg a,A⁆ := by
    rw [map_commutator,hiU,hmA]
  rw [←hm,←relIndex_comap,hC]
  exact cover_large_actor_commutator_index h e hz hk (A.comap i)
    (htwo.comap_of_injective i hi) hidx

include h e hz hk in
/-- The full seed inherits the bound without removing its central attachment. -/
theorem graph_large_actor_seed_commutator_index
    {a : Vertex Rg} (ha : color Rg a = false)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg a)
    (htwo : IsPGroup 2 A) (hlarge : 2 < (Q Rg a).relIndex A) :
    4 ≤ (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex
      ⁅Z Rg a,A⁆ := by
  have hJZ : ⁅Z Rg a,A⁆ ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_left.mp (hA.trans (Z_normalized Rg a))
  let := finite_Z Rg a
  let : Finite (⁅Z Rg a,A⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hJZ) (inclusion_injective _)
  exact (graph_large_actor_moving_commutator_index h e hz hk ha A hA htwo hlarge).trans
    (relIndex_le_of_le_right (commutator_mono (DistanceEight.U_le_Z Rg a) le_rfl)
      index_ne_zero_of_finite)

/-- The whole original plane radical commutator has central index four. -/
theorem plane_cover_commutator_central_index (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom) :
    (center M).relIndex ⁅W,Rg⁆ = 4 := by
  rw [cover_commutator_central_index h e hz hk,hfull,fixedCodim_map_conj]
  rw [CFSG.Quasithin.ChapterB.Offenders.Six.fixedCodim_D.2.2.2]
  rfl

include h e hz hk in
/-- The full incident edge commutator has central index four on the original graph. -/
theorem plane_graph_edge_commutator_central_index
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex
      ⁅Z Rg a,Q Rg t⁆ = 4 := by
  obtain ⟨i,hi,hir,hiR,_,hiU⟩ := remaining_edge_coordinates h e hz ha hat
  have hC := centralizer_comap_of_range i hi (stabilizer Rg a) hir
  rw [full_seed_commutator_eq_moving h e hz ha hat _ le_rfl,
    ←hiU,←hiR,←map_commutator,←relIndex_comap,hC]
  exact plane_cover_commutator_central_index h e hz hk u hfull

private theorem central_completion_of_index_four {F : Type*} [Group F]
    (P C H J : Subgroup F) [Finite C] [Finite H] [Finite J]
    (hHP : H ≤ P) (hJP : J ≤ P) (hHJ : H ≤ J)
    (hC : C ≤ centralizer (P : Set F))
    (hH : C.relIndex H = 4) (hJ : C.relIndex J = 4) :
    H ⊔ C = J ⊔ C := by
  have hCH : C ≤ normalizer (H : Set F) :=
    (hC.trans (centralizer_le hHP)).trans (Subgroup.centralizer_le_normalizer _)
  have hCJ : C ≤ normalizer (J : Set F) :=
    (hC.trans (centralizer_le hJP)).trans (Subgroup.centralizer_le_normalizer _)
  have hmono : H ⊔ C ≤ J ⊔ C := sup_le_sup_right hHJ C
  have ht := relIndex_mul_relIndex C (H ⊔ C) (J ⊔ C) le_sup_right hmono
  rw [relIndex_sup_of_normalizes _ _ hCH,relIndex_sup_of_normalizes _ _ hCJ,hH,hJ] at ht
  have hindex : (H ⊔ C).relIndex (J ⊔ C) = 1 := by omega
  exact le_antisymm hmono (relIndex_eq_one.mp hindex)

include h e hz hk in
/-- Every large edge subactor fills the full edge commutator plane modulo
the entire central seed. Its literal commutator has order four or eight. -/
theorem plane_graph_large_actor_commutator_plane
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map π =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom)
    {a t : Vertex Rg} (ha : color Rg a = false) (hat : Adjacent Rg a t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t)
    (hlarge : 2 < (Q Rg a).relIndex A) :
    let C := Z Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
    (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex ⁅Z Rg a,A⁆ = 4 ∧
      (Nat.card (⁅Z Rg a,A⁆ : Subgroup (FreeAmalgam Rg)) = 4 ∨
        Nat.card (⁅Z Rg a,A⁆ : Subgroup (FreeAmalgam Rg)) = 8) ∧
      ⁅Z Rg a,A⁆ ⊔ C = ⁅Z Rg a,Q Rg t⁆ ⊔ C := by
  let C := Z Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  let H := ⁅Z Rg a,A⁆
  let J := ⁅Z Rg a,Q Rg t⁆
  have hQG : Q Rg t ≤ stabilizer Rg a :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hJG : J ≤ Z Rg a :=
    le_normalizer_iff_commutator_le_left.mp (hQG.trans (Z_normalized Rg a))
  have hHJ : H ≤ J := commutator_mono le_rfl hA
  have hHZ : H ≤ Z Rg a := hHJ.trans hJG
  let := finite_Z Rg a
  let : Finite J := Finite.of_injective (inclusion hJG) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  let : Finite C := Finite.of_injective
    (inclusion (show C ≤ Z Rg a from inf_le_left)) (inclusion_injective _)
  have hupper := plane_graph_edge_commutator_central_index h e hz hk u hfull ha hat
  have htwo : IsPGroup 2 A := by
    obtain ⟨i,_,_,hiR,_⟩ := remaining_edge_coordinates h e hz ha hat
    exact ((hiR ▸ h.relative_radical.isPGroup.map i) : IsPGroup 2 (Q Rg t)).to_le hA
  have hlower := graph_large_actor_seed_commutator_index h e hz hk
    ha A (hA.trans hQG) htwo hlarge
  have hmono := relIndex_le_of_le_right
    (H := centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) hHJ index_ne_zero_of_finite
  have hexact : (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex H = 4 := by
    change (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex J = 4 at hupper
    exact Nat.le_antisymm (hmono.trans_eq hupper) hlower
  have hHU : H ≤ U Rg a := by
    change ⁅Z Rg a,A⁆ ≤ _
    rw [full_seed_commutator_eq_moving h e hz ha hat A hA]
    exact le_normalizer_iff_commutator_le_left.mp ((hA.trans hQG).trans (U_normalized a))
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  let CZ := centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  let : Finite (U Rg a ⊓ CZ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite (H ⊓ CZ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hcent : Nat.card (H ⊓ CZ : Subgroup (FreeAmalgam Rg)) ≤ 2 :=
    (card_le_of_le (inf_le_inf_right CZ hHU)).trans
      (moving_central_attachment_card_le_two h e hz hk ha)
  have hpos : 0 < Nat.card (H ⊓ CZ : Subgroup (FreeAmalgam Rg)) := Nat.card_pos
  have hsize := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) (H ⊓ CZ) H bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hsize
  change Nat.card (H ⊓ CZ : Subgroup (FreeAmalgam Rg)) *
    (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex H = Nat.card H at hsize
  rw [hexact] at hsize
  have horder : Nat.card H = 4 ∨ Nat.card H = 8 := by omega
  have hidx (K : Subgroup (FreeAmalgam Rg)) (hK : K ≤ Z Rg a) :
      C.relIndex K = (centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))).relIndex K := by
    change (C.subgroupOf K).index = _
    congr 1
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hK x.property,hx⟩⟩
  refine ⟨hexact,horder,
    central_completion_of_index_four (Z Rg a) C H J hHZ hJG hHJ ?_ ?_ ?_⟩
  · exact inf_le_right.trans (centralizer_le (Z_le_stabilizer Rg a))
  · rw [hidx H hHZ]
    exact hexact
  · rw [hidx J hJG]
    exact hupper

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

