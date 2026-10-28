module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalNonsplitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootProductExclusion

/-!
# Full-kernel saturation from the actual root-pair index

Lift the two full roots through the original quotient map, retaining the
whole kernel and exact fixed indices on U. Source (5.1) excludes their
product as the image of the entire maximum-small-mover join.

Equal neighboring mover orders now force full-Q containment when the
neighbor has index two over a square-order root pair. Otherwise its image
is at least twice as large as the original mover's image. Both bounds are
then equalities: the root pair fills the plane intersection and is itself
a maximum small mover, contradicting (5.1). The same marked plane bounds
the literal intersection of the two original movers by q squared.

Source: MS93 (5.5), printed p.917, the full-Q and intersection calculation.
ContainedKernelAlternative applies these results to the original contained
endpoint, the actual unequal neighbor, and the same selected residual
conjugator. No field restriction or removal of central attachments occurs.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Source (5.1) excludes a full root pair as the entire image of the
original maximum-small-mover join, through this same quotient map. -/
theorem Input.replacement_small_mover_not_root_pair
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (s r : Option B.Carrier) :
    ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f ≠
        rootImage s ⊔ rootImage r := by
  intro heq
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let C (s : Option B.Carrier) := (rootImage s).comap f
  let D (s : Option B.Carrier) := (C s).map S.subtype
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hkJ : f.ker ≤ J₀ := by
    intro x hx
    exact hQJ (hfQ ▸ mem_map_of_mem S.subtype hx)
  have hCT (v : Option B.Carrier) (hv : rootImage v ≤ J₀.map f) : D v ≤ Q d.radical t := by
    have hc : C v ≤ J₀ := (comap_mono hv).trans_eq (comap_map_eq_self hkJ)
    have hh := map_mono hc (f := S.subtype)
    rw [map_subgroupOf_eq_of_le hJS] at hh
    exact hh.trans (Subgroup.SmallMover.join_le _ _ _ _)
  have hcard (v : Option B.Carrier) : (Q d.radical a).relIndex (D v) = Nat.card F := by
    dsimp only [D]
    rw [←hfQ,relIndex_map_map_of_injective _ _ S.subtype_injective,relIndex_ker]
    dsimp only [C]
    rw [map_comap_eq_self_of_surjective hf]
    change Nat.card ((rootFamily v).map unipotent.subtype) = _
    rw [card_map_of_injective unipotent.subtype_injective,card_rootFamily,hBF]
  have hmove (v : Option B.Carrier) :
      (centralizer (D v : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F := by
    dsimp only [D]
    rw [←map_subgroupOf_eq_of_le hUS,
      Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective,hindex]
    dsimp only [C]
    rw [map_comap_eq_self_of_surjective hf]
    have hm := binary_movingIndex (rootFamily (F := B.Carrier) v)
    rw [movingIndex_rootFamily] at hm
    change 2 ^ fixedCodim
      ((restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype)
      (rootFamily v) = Nat.card B.Carrier at hm
    rw [fixedCodim,fixedSpace_comp_map] at hm
    exact hm.trans hBF
  have hp : ((rootImage s ⊔ rootImage r : Subgroup (Sp B.Carrier)) : Set _) =
      (rootImage s : Set (Sp B.Carrier)) * (rootImage r : Set (Sp B.Carrier)) := by
    apply coe_mul_of_right_le_normalizer_left
    let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
    have hsP : rootImage s ≤ P := map_mono (rootFamily_le_wing s)
    have hrP : rootImage r ≤ P := map_mono (rootFamily_le_wing r)
    let := CentralRootGeometry.wing_elementary (F := B.Carrier) true
    let : IsMulCommutative P := inferInstance
    exact hrP.trans ((P.le_centralizer.trans (centralizer_le hsP)).trans
      (Subgroup.centralizer_le_normalizer _))
  apply h.replacement_root_product_excluded d geometry hb ha hat (D s) (D r)
    (hCT s (heq ▸ le_sup_left)) (hCT r (heq ▸ le_sup_right))
    (hcard s) (hcard r) (hmove s) (hmove r)
  intro x hx
  let x₀ : S := ⟨x,hJS hx⟩
  have hx' : f x₀ ∈ ((rootImage s : Set (Sp B.Carrier)) * (rootImage r : Set (Sp B.Carrier))) := by
    rw [←hp,←heq]
    exact mem_map_of_mem f hx
  obtain ⟨y,hy,z,hz,hyz⟩ := hx'
  obtain ⟨y₀,hy₀⟩ := hf y
  refine ⟨y₀.val,mem_map_of_mem S.subtype (show y₀∈C s from by change f y₀ ∈ rootImage s; rwa [hy₀]),
    (y₀⁻¹*x₀).val,show (y₀⁻¹*x₀).val ∈ D r from mem_map_of_mem S.subtype (show y₀⁻¹*x₀∈C r from ?_),?_⟩
  · change f (y₀⁻¹*x₀) ∈ rootImage r
    rw [map_mul,map_inv,hy₀,←hyz,inv_mul_cancel_left]
    exact hz
  · change y₀.val * (y₀.val⁻¹*x)=x
    group

omit h d in
private theorem double_image_of_missing_kernel {G D : Type*} [Group G] [Finite G] [Group D]
    (f : G →* D) (J E : Subgroup G) (hkJ : f.ker ≤ J)
    (hc : Nat.card J = Nat.card E) (hkE : ¬ f.ker ≤ E) :
    2 * Nat.card (J.map f) ≤ Nat.card (E.map f) := by
  let N := f.ker ⊓ E
  have hN : N ≤ f.ker := inf_le_left
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G) N f.ker bot_le hN
  rw [relIndex_bot_left,relIndex_bot_left] at hmul
  have hJ := Subgroup.SmallMover.card_kernel_mul_image f J hkJ
  have hE := relIndex_mul_relIndex (⊥ : Subgroup G) N E bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left] at hE
  have hNE : N.relIndex E = Nat.card (E.map f) := by
    dsimp only [N]
    rw [inf_relIndex_right,relIndex_ker]
  rw [hNE] at hE
  have hm : N.relIndex f.ker * Nat.card (J.map f) = Nat.card (E.map f) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N))
    calc
      Nat.card N * (N.relIndex f.ker * Nat.card (J.map f)) =
          Nat.card f.ker * Nat.card (J.map f) := by rw [←mul_assoc,hmul]
      _ = Nat.card E := hJ.trans hc
      _ = Nat.card N * Nat.card (E.map f) := hE.symm
  have h0 : N.relIndex f.ker ≠ 0 := index_ne_zero_of_finite
  have h1 : N.relIndex f.ker ≠ 1 := by
    intro he
    exact hkE ((relIndex_eq_one.mp he).trans inf_le_right)
  rw [←hm]
  exact Nat.mul_le_mul_right _ (by omega)

/-- A root pair of index two in the unequal mover forces it to contain
 the full original kernel. Missing that kernel would identify the original
 maximum mover with the forbidden root pair of MS93 (5.1). -/
theorem Input.replacement_root_pair_index_two_kernel
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (s r : Option B.Carrier) (hsr : s ≠ r)
    (hi : (rootImage s ⊔ rootImage r).relIndex
      (((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f) = 2) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) := by
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let E₀ := E.subgroupOf S
  let W := rootImage s ⊔ rootImage r
  let V := W.comap f
  let := finite_stabilizer d.radical a
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hES : E ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hkJ : f.ker ≤ J₀ := by
    intro x hx
    exact hQJ (hfQ ▸ mem_map_of_mem S.subtype hx)
  have hjoin : Subgroup.SmallMover.join U₀ f.ker T (Nat.card F^2) = J₀ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hJS]
  have hJE : Nat.card J₀ = Nat.card E₀ := by
    rw [←card_map_of_injective S.subtype_injective (K := J₀),
      ←card_map_of_injective S.subtype_injective (K := E₀),
      map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES]
    exact small_mover_neighbor_card_eq d.radical hat hct _
  have hjlarge : Nat.card F^2 ≤ Nat.card (J₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh]
    exact h.replacement_small_mover_join_index d geometry hb ha hat
  have hWcard : Nat.card W = Nat.card F^2 := by
    change Nat.card ((rootFamily s).map unipotent.subtype ⊔ (rootFamily r).map unipotent.subtype : Subgroup (Sp B.Carrier)) = _
    rw [←Subgroup.map_sup,card_map_of_injective unipotent.subtype_injective,rootFamily_sup_card hsr,hBF]
  by_contra hnot
  have hkE : ¬ f.ker ≤ E₀ := by
    intro hle
    have hh := map_mono hle (f := S.subtype)
    rw [hfQ,map_subgroupOf_eq_of_le hES] at hh
    exact hnot hh
  have hdouble := double_image_of_missing_kernel f J₀ E₀ hkJ hJE hkE
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (Sp B.Carrier))
    (W ⊓ E₀.map f) (E₀.map f) bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hi] at hmul
  have hcap : Nat.card (W ⊓ E₀.map f : Subgroup (Sp B.Carrier)) ≤ Nat.card F^2 := by
    exact (card_le_of_le inf_le_left).trans_eq hWcard
  have hJsize : Nat.card (J₀.map f) = Nat.card F^2 := by omega
  have hcapEq : W ⊓ E₀.map f = W := eq_of_le_of_card_ge inf_le_left (by omega)
  have hWE : W ≤ E₀.map f := hcapEq ▸ inf_le_right
  have hWT : W ≤ T.map f := hWE.trans (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _)))
  have hkT : f.ker ≤ T := hkJ.trans (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))
  have hVT : V ≤ T := (comap_mono hWT).trans_eq (comap_map_eq_self hkT)
  have hVmap : V.map f = W := map_comap_eq_self_of_surjective hf _
  have hVcard : Nat.card J₀ = Nat.card V := by
    rw [←Subgroup.SmallMover.card_kernel_mul_image f J₀ hkJ,
      ←Subgroup.SmallMover.card_kernel_mul_image f V (ker_le_comap f W),hVmap,hWcard,hJsize]
  have hVindex : (centralizer (V : Set S)).relIndex U₀ ≤ Nat.card F^2 := by
    rw [hindex,hVmap]
    have hm := movingIndex_le_field_sq_of_le_wing (rootFamily s ⊔ rootFamily r)
      (sup_le (rootFamily_le_wing s) (rootFamily_le_wing r))
    rw [←binary_movingIndex] at hm
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype)
      (rootFamily s ⊔ rootFamily r) ≤ _ at hm
    rw [fixedCodim,fixedSpace_comp_map,Subgroup.map_sup,hBF] at hm
    exact hm
  have heq := Subgroup.SmallMover.eq_join_of_card_eq_of_index_le U₀ f.ker T
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos)
    (hjoin.symm ▸ hkJ) (by rw [hjoin,relIndex_ker]; exact hjlarge) V hVT
    (hjoin.symm ▸ hVcard) hVindex
  rw [hjoin] at heq
  have hbad : J₀.map f = rootImage s ⊔ rootImage r := by rw [←heq,hVmap]
  exact h.replacement_small_mover_not_root_pair d geometry hb ha hat B hB f hf hfQ hindex s r hbad

/-- The same marked plane intersection bounds the literal two-mover
intersection modulo Q. The original mover is either in that plane or
already has image order at most q². -/
theorem Input.replacement_unequal_plane_intersection_bound
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (W : Subgroup (Sp B.Carrier)) (hW : Nat.card W ≤ Nat.card F^2)
    (hEW : (((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f) ⊓
        (CentralRootGeometry.wing true).map unipotent.subtype ≤ W) :
    (Q d.radical a).relIndex
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2) ⊓
        Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) (Nat.card F^2)) ≤
          Nat.card F^2 := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let E₀ := E.subgroupOf S
  let J₁ := (J₀.map f).subgroupOf unipotent
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hES : E ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hJU : J₀.map f ≤ unipotent := (map_mono (comap_mono (Subgroup.SmallMover.join_le _ _ _ _))).trans hTf
  have hJmap : J₁.map unipotent.subtype = J₀.map f := map_subgroupOf_eq_of_le hJU
  have hmove : movingIndex J₁ ≤ Nat.card B.Carrier^2 := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) J₁ ≤ _
    rw [fixedCodim,fixedSpace_comp_map,hJmap]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) J₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,hindex] at hh
    change 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (J₀.map f) ≤ _
    rw [←hh,hBF]
    exact (h.replacement_unequal_original_quadratic d geometry hb ha hat hct hne).1.le
  have hbound : Nat.card ((J₀ ⊓ E₀).map f) ≤ Nat.card F^2 := by
    by_cases hw : J₁ ≤ CentralRootGeometry.wing true
    · have hJP : J₀.map f ≤ (CentralRootGeometry.wing true).map unipotent.subtype := by
        rw [←hJmap]
        exact map_mono hw
      have hle : (J₀ ⊓ E₀).map f ≤ W :=
        (le_inf (map_mono inf_le_right) ((map_mono inf_le_left).trans hJP)).trans hEW
      exact (card_le_of_le hle).trans hW
    · obtain ⟨l,hl⟩ := Degree.exists_plane_coordinates_of_not_le_wing J₁ hmove hw
      have hjp : J₁ ≤ finitePlane l := by
        intro x hx
        obtain ⟨⟨b,u,w,v⟩,rfl⟩ := CentralRootGeometry.element_surjective x
        exact (element_mem_finitePlane _ _ _ _ _).mpr (hl b u w v hx)
      have hjc : Nat.card (J₀.map f) ≤ Nat.card F^2 := by
        rw [←hJmap,card_map_of_injective unipotent.subtype_injective]
        exact (card_le_of_le hjp).trans_eq ((card_finitePlane l).trans (by rw [hBF]))
      exact (card_le_of_le (map_mono inf_le_left)).trans hjc
  have hh := relIndex_map_map_of_injective f.ker (J₀ ⊓ E₀) S.subtype_injective
  rw [hfQ,map_inf _ _ _ S.subtype_injective,
    map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hES,relIndex_ker] at hh
  exact hh.le.trans hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
