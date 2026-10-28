module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.LocalPackage.SmallMoverQuotient
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootIndex
/-!
# The unique maximum through the original small-mover quotient

The maximal-family correspondence preserves the entire join. Full preimages
of the symplectic roots have the source relative order and centralizer index
four, so the original product exclusion (5.1) implies the coordinate root
exclusion. A unique maximum with nontrivial quotient image therefore has
relative order at least sixteen and lies in one of the precise coordinate
plane alternatives.

Source: Meierfrankenfeld–Stellmacher (1993), (5.1) and (5.4)(a), printed
pp.913–915. The compatible flag maximizing condition from (5.0) is still
needed to identify the plane alternative with the chosen parabolic label;
this module makes no unmarked fixed-label assertion.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative Pointwise
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage.ModelSmallMovers
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers
variable {K G : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
  [Group G] [Finite G]
variable (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] [Finite V]
variable (q : G →* L (K := K)) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))
variable (p : (NormalElementaryQuotient.representation V q hq hker).IntertwiningMap
  (binaryNatural (K := K))) (hp : IsCover p)
variable (hK : Nat.card K=4)

include hp in
theorem coordinates_join (T : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range) :
    coordinates q hK (Subgroup.SmallMover.join V q.ker T 16)=
      join (coordinates q hK T) := by
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  let J := Subgroup.SmallMover.join V q.ker T 16
  have hJi : J.map q ≤ i.range :=
    (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hT
  apply map_injective (derivedEmbedding_injective _)
  rw [coordinates_map q hK J hJi]
  apply le_antisymm
  · change (sSup (Subgroup.SmallMover.Maximal V q.ker T 16)).map q ≤ _
    rw [sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro E
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hE
    rw [←coordinates_map q hK E ((map_mono hE.1.1).trans hT)]
    exact map_mono (le_sSup (maximal_coordinates V q hq hker p hp hK T E hkT hT hE))
  · change (sSup (Maximal (coordinates q hK T))).map i ≤ J.map q
    rw [sSup_eq_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro B
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hB
    obtain ⟨C,hC⟩ := (maximal_coordinates_bijective V q hq hker p hp hK T hkT hT).surjective ⟨B,hB⟩
    have heq : coordinates q hK C.val=B := congrArg Subtype.val hC
    rw [←heq,coordinates_map q hK C.val ((map_mono C.property.1.1).trans hT)]
    exact map_mono (le_sSup C.property)

omit [V.Normal] [IsElementaryAbelian 2 V] [Finite V] [Algebra (ZMod 2) K] [Finite G] in
include hq in
theorem coordinates_preimage (A : Subgroup (unipotent (F := K))) :
    coordinates q hK ((A.map (derivedEmbedding (by omega : 2<Nat.card K))).comap q)=A := by
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  change ((A.map i).comap q |>.map q).comap i=A
  rw [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top),
    comap_map_eq_self (by rw [i.ker_eq_bot (derivedEmbedding_injective _)]; exact bot_le)]

omit [V.Normal] [IsElementaryAbelian 2 V] [Finite V] [Algebra (ZMod 2) K] [Finite G] in
theorem preimage_le_radical (T : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (A : Subgroup (unipotent (F := K))) (hA : A ≤ coordinates q hK T) :
    (A.map (derivedEmbedding (by omega : 2<Nat.card K))).comap q ≤ T := by
  have hh := comap_mono (f := q) ((map_mono hA).trans_eq (coordinates_map q hK T hT))
  exact hh.trans_eq (comap_map_eq_self hkT)

omit [Finite G] in
include hp in
theorem preimage_centralizer_index (A : Subgroup (unipotent (F := K))) :
    (centralizer ((A.map (derivedEmbedding (by omega : 2<Nat.card K))).comap q : Set G)).relIndex V =
      movingIndex A := by
  rw [centralizer_index_eq_natural V q hq hker p hp,
    map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)]
  exact derivedEmbedding_movingIndex _ _

omit [V.Normal] [IsElementaryAbelian 2 V] [Finite V] [Algebra (ZMod 2) K] [Finite G] in
include hq in
theorem preimage_relIndex (A : Subgroup (unipotent (F := K))) :
    q.ker.relIndex ((A.map (derivedEmbedding (by omega : 2<Nat.card K))).comap q)=Nat.card A := by
  rw [relIndex_ker,map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top),
    card_map_of_injective (derivedEmbedding_injective _)]

include hp in
theorem source_rootExclusion_coordinates (T : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hsource : ∀ E A : Subgroup G, E≤T → A≤T →
      q.ker.relIndex E=4 → (centralizer (E:Set G)).relIndex V=4 →
      q.ker.relIndex A=4 → (centralizer (A:Set G)).relIndex V=4 →
      ¬ (Subgroup.SmallMover.join V q.ker T 16 : Set G) ⊆ (E:Set G)*(A:Set G)) :
    RootExclusion (coordinates q hK T) := by
  intro s t hs ht hprod
  let i := derivedEmbedding (F := K) (by omega : 2<Nat.card K)
  let E := ((rootFamily s).map i).comap q
  let A := ((rootFamily t).map i).comap q
  have hE : E≤T := preimage_le_radical q hK T hkT hT _ hs
  have hA : A≤T := preimage_le_radical q hK T hkT hT _ ht
  have hcardE : q.ker.relIndex E=4 := (preimage_relIndex q hq hK _).trans ((card_rootFamily s).trans hK)
  have hcardA : q.ker.relIndex A=4 := (preimage_relIndex q hq hK _).trans ((card_rootFamily t).trans hK)
  have hindexE : (centralizer (E:Set G)).relIndex V=4 :=
    (preimage_centralizer_index V q hq hker p hp hK _).trans (movingIndex_rootFamily_four hK s)
  have hindexA : (centralizer (A:Set G)).relIndex V=4 :=
    (preimage_centralizer_index V q hq hker p hp hK _).trans (movingIndex_rootFamily_four hK t)
  apply hsource E A hE hA hcardE hindexE hcardA hindexA
  intro x hx
  let J := Subgroup.SmallMover.join V q.ker T 16
  have hJi : J.map q ≤ i.range := (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hT
  have hxm : q x ∈ (coordinates q hK J).map i := by
    rw [coordinates_map q hK J hJi]
    exact mem_map_of_mem q hx
  obtain ⟨y,hy,hyx⟩ := hxm
  rw [coordinates_join V q hq hker p hp hK T hkT hT] at hy
  obtain ⟨a,ha,b,hb,hab⟩ := hprod hy
  obtain ⟨u,hu⟩ := hq (i a)
  have hv : u⁻¹*x ∈ A := by
    change q (u⁻¹*x) ∈ (rootFamily t).map i
    have hqx : q x=i a*i b := hyx.symm.trans (by rw [←hab,map_mul])
    rw [map_mul,map_inv,hu,hqx,inv_mul_cancel_left]
    exact mem_map_of_mem i hb
  exact ⟨u,show u∈E from (by change q u ∈ (rootFamily s).map i; rw [hu]; exact mem_map_of_mem i ha),
    u⁻¹*x,hv,mul_inv_cancel_left u x⟩

include hp in
theorem maximal_coordinates_singleton (T E : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hmax : Subgroup.SmallMover.Maximal V q.ker T 16={E}) :
    Maximal (coordinates q hK T)={coordinates q hK E} := by
  have hE : E∈Subgroup.SmallMover.Maximal V q.ker T 16 := hmax ▸ Set.mem_singleton E
  ext B
  constructor
  · intro hB
    obtain ⟨C,hC⟩ := (maximal_coordinates_bijective V q hq hker p hp hK T hkT hT).surjective ⟨B,hB⟩
    have he : C.val=E := Set.mem_singleton_iff.mp (hmax ▸ C.property)
    have hb : coordinates q hK C.val=B := congrArg Subtype.val hC
    exact Set.mem_singleton_iff.mpr (hb.symm.trans (congrArg (coordinates q hK) he))
  · rintro rfl
    exact maximal_coordinates V q hq hker p hp hK T E hkT hT hE

include hp in
theorem unique_maximal_quotient_large (T E : Subgroup G) (hkT : q.ker ≤ T)
    (hT : T.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range)
    (hmax : Subgroup.SmallMover.Maximal V q.ker T 16={E})
    (hne : (Subgroup.SmallMover.join V q.ker T 16).map q ≠ ⊥)
    (hsource : ∀ E A : Subgroup G, E≤T → A≤T →
      q.ker.relIndex E=4 → (centralizer (E:Set G)).relIndex V=4 →
      q.ker.relIndex A=4 → (centralizer (A:Set G)).relIndex V=4 →
      ¬ (Subgroup.SmallMover.join V q.ker T 16 : Set G) ⊆ (E:Set G)*(A:Set G)) :
    16 ≤ q.ker.relIndex (Subgroup.SmallMover.join V q.ker T 16) ∧
      (coordinates q hK (Subgroup.SmallMover.join V q.ker T 16) ≤ CentralRootGeometry.wing true ∨
        ∃ l : K, coordinates q hK (Subgroup.SmallMover.join V q.ker T 16)=finitePlane l ∧
          coordinates q hK T ≤ CentralRootGeometry.wing false) := by
  let J := Subgroup.SmallMover.join V q.ker T 16
  have hJi : J.map q ≤ (derivedEmbedding (by omega : 2<Nat.card K)).range :=
    (map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hT
  have hn : join (coordinates q hK T) ≠ ⊥ := by
    rw [←coordinates_join V q hq hker p hp hK T hkT hT]
    intro hz
    apply hne
    rw [←coordinates_map q hK J hJi,hz,Subgroup.map_bot]
  have hh := unique_maximal_large hK
    (maximal_coordinates_singleton V q hq hker p hp hK T E hkT hT hmax) hn
    (source_rootExclusion_coordinates V q hq hker p hp hK T hkT hT hsource)
  rw [←coordinates_join V q hq hker p hp hK T hkT hT] at hh
  refine ⟨?_,hh.2⟩
  rw [relIndex_ker,←coordinates_map q hK J hJi,
    card_map_of_injective (derivedEmbedding_injective _)]
  exact hh.1

end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage.ModelSmallMovers
