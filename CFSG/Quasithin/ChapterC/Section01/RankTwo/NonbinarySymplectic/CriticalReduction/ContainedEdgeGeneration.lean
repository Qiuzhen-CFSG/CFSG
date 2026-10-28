module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedPairGeneration
public import Theory.SpecificGroups.SymplecticFour.PointIndividualGeneration

/-!
# Edge generation at the same contained-endpoint selector

The marked endpoint and unequal mover already generate the point-local
rank-one quotient. Apply the point-local supplement dichotomy to the larger
join with the actual selected edge. A proper supplement would put the
original smaller mover J inside a square-order root pair. Its established
square lower bound forces equality, contrary to MS93 (5.1).

The whole point local and the unequal mover then generate the symplectic
quotient. The full Q-kernel in the edge lifts this to the literal vertex
group. No centralization of the whole endpoint is inferred from its image.
ContainedIndividualGeneration uses this on the same u,v and markings as
the individual/paired generation alternative.
Source: MS93 (5.5)(a), printed pp.915--917.
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

/-- The same marked rank-one selector generates with the entire selected
edge: a proper point-local supplement would make the original smaller
mover the root pair forbidden by MS93 (5.1). -/
theorem Input.replacement_contained_marked_edge_generation
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f)
    (u v : stabilizer d.radical a) (s w : Sp B.Carrier)
    (hs : s∈planeLocal) (hsp : s∉pointParabolic)
    (hw : f u*f v=w) (hws : w*s∈pointLocal)
    (hcore : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 ≤ pointLocal)
    (hAP : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map
      ((MulAut.conj (f u)).toMonoidHom.comp f) ≤
        (CentralRootGeometry.wing true).map unipotent.subtype)
    (hproj : ((((Z d.radical z).subgroupOf (stabilizer d.radical a)).map
      ((MulAut.conj (f u)).toMonoidHom.comp f)).subgroupOf pointLocal).map pointQuotient =
        Matrix.SpecialLinearGroup.upperUnipotent B.Carrier)
    (hgen : ((((Z d.radical z).subgroupOf (stabilizer d.radical a) ⊔
      ((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map
          (MulAut.conj v).toMonoidHom).map
            ((MulAut.conj (f u)).toMonoidHom.comp f)).subgroupOf pointLocal).map pointQuotient = ⊤) :
    (Z d.radical z).subgroupOf (stabilizer d.radical a) ⊔
      ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map
        (MulAut.conj v).toMonoidHom = ⊤ := by
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let Eorig := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let E₀ := Eorig.subgroupOf S
  let f' := (MulAut.conj (f u)).toMonoidHom.comp f
  let N := (A ⊔ T.map (MulAut.conj v).toMonoidHom).map f'
  let D := N.subgroupOf pointLocal
  let := finite_stabilizer d.radical a
  have hnB : 1<B.degree := by rw [hB]; exact h.nonbinary
  have hBF : Nat.card B.Carrier=Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hf' : Function.Surjective f' := (MulAut.conj (f u)).surjective.comp hf
  have hker : f'.ker=f.ker := by
    ext y
    exact (MulAut.conj (f u)).map_eq_one_iff
  have hm (C : Subgroup S) : (C.map (MulAut.conj v).toMonoidHom).map f' =
      (C.map f).map (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change f u*f (v*x*v⁻¹)*(f u)⁻¹=w*f x*w⁻¹
    rw [map_mul,map_mul,map_inv,←hw]
    group
  have hET : E₀ ≤ T := comap_mono (Subgroup.SmallMover.join_le _ _ _ _)
  have hJT : J₀ ≤ T := comap_mono (Subgroup.SmallMover.join_le _ _ _ _)
  have hEN : (E₀.map f).map (MulAut.conj w).toMonoidHom ≤ N := by
    rw [←hm]
    exact map_mono ((map_mono hET).trans le_sup_right)
  have hfullRank : D.map pointQuotient = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact map_mono (comap_mono (map_mono (sup_le_sup_left (map_mono hET) A)))
  have hsupp : D ⊔ pointRadical = ⊤ := by
    rw [←pointQuotient_ker,←comap_map_eq,hfullRank,comap_top]
  have hEf : E₀.map f ≤ unipotent := (map_mono hET).trans hTf
  let E₁ := (E₀.map f).subgroupOf unipotent
  have hE₁ : E₁.map unipotent.subtype=E₀.map f := map_subgroupOf_eq_of_le hEf
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hES : Eorig ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hbig : Nat.card B.Carrier^2 < movingIndex E₁ := by
    rw [←binary_movingIndex]
    change _ < 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) E₁
    rw [fixedCodim,fixedSpace_comp_map,hE₁]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hindex] at hh
    change _ < 2 ^ fixedCodim (restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)) (E₀.map f)
    rw [←hh,hBF]
    exact (h.replacement_unequal_individual_indices d geometry hb path.start_color hat hct hne).2
  have hout : ¬ E₀.map f ≤ (CentralRootGeometry.wing true).map unipotent.subtype := by
    intro hle
    have he : E₁ ≤ CentralRootGeometry.wing true := by
      apply (map_le_map_iff_of_injective unipotent.subtype_injective).mp
      rwa [hE₁]
    exact hbig.not_ge (movingIndex_le_field_sq_of_le_wing E₁ he)
  have hD : D=⊤ := by
    rcases PointSupplement.supplement_dichotomy B.card_eq hnB D hsupp with he | hc
    · exact he
    exfalso
    have hAL : A.map f' ≤ pointLocal := hAP.trans ((map_subtype_le _).trans inf_le_left)
    have hlarge' : Nat.card B.Carrier^2 ≤ Nat.card ((A.map f').subgroupOf pointLocal) := by
      rw [←card_map_of_injective pointLocal.subtype_injective,map_subgroupOf_eq_of_le hAL,
        ←relIndex_ker,hker]
      have hh := relIndex_map_map_of_injective f.ker A S.subtype_injective
      rw [hfQ,map_subgroupOf_eq_of_le
        (path.endpoint_Z_le_start_stabilizer (by omega : 0<geometry.b d.radical))] at hh
      rw [←hh,hBF]
      exact hlarge
    obtain ⟨_,_,hDR,_⟩ := PointSupplement.central_kernel_large_endpoint B.card_eq hnB D
      ((A.map f').subgroupOf pointLocal) hc (comap_mono (map_mono le_sup_left)) hproj hlarge'
    obtain ⟨r,b,hb',hpair,hsize,_,_⟩ := MoverNormalizer.marked_plane_intersection_root_pair
      B.card_eq hnB N (E₀.map f) hEf hout s w hs hsp hws hEN hcore hDR
    have hC : (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 =
        ((CentralRootGeometry.wing true).map unipotent.subtype).map (MulAut.conj w).toMonoidHom := by
      rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj w).injective,pCoreIn,
        planeParabolic_core_map_eq_radical B.card_eq hnB]
      exact congrArg (Subgroup.map (MulAut.conj w).toMonoidHom)
        SymplecticConjugatePair.planeRadical_eq_wing
    have hJcap : (J₀.map f).map (MulAut.conj w).toMonoidHom ≤
        N ⊓ (planeParabolic.map (MulAut.conj w).toMonoidHom).pCoreIn 2 := by
      apply le_inf
      · rw [←hm]
        exact map_mono ((map_mono hJT).trans le_sup_right)
      · rw [hC]
        exact map_mono (map_le_iff_le_comap.mpr hJplane)
    have hback (C : Subgroup (Sp B.Carrier)) :
        (C.map (MulAut.conj w).toMonoidHom).map (MulAut.conj w⁻¹).toMonoidHom=C := by
      rw [Subgroup.map_map]
      have hh : (MulAut.conj w⁻¹).toMonoidHom.comp (MulAut.conj w).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp [MulAut.conj_apply,mul_assoc]
      rw [hh,Subgroup.map_id]
    have hle := map_mono hJcap (f := (MulAut.conj w⁻¹).toMonoidHom)
    rw [hback,hpair] at hle
    have hcardJ : Nat.card B.Carrier^2 ≤ Nat.card (J₀.map f) := by
      rw [←relIndex_ker]
      have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
      rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
      rw [←hh,hBF]
      exact h.replacement_small_mover_join_index d geometry hb path.start_color hat
    have hcardPair : Nat.card (rootImage (some r) ⊔ rootImage (some (r+b)) : Subgroup (Sp B.Carrier)) =
        Nat.card B.Carrier^2 := by
      rw [←hpair,card_map_of_injective (MulAut.conj w⁻¹).injective]
      exact hsize
    exact h.replacement_small_mover_not_root_pair d geometry hb path.start_color hat B hB f hf hfQ
      hindex (some r) (some (r+b)) (eq_of_le_of_card_ge hle (hcardPair.le.trans hcardJ))
  have hwP : w∉pointParabolic := by
    intro hwP
    exact hsp (by simpa only [inv_mul_cancel_left] using
      pointParabolic.mul_mem (pointParabolic.inv_mem hwP) (pointLocal_le hws))
  have hN : N=⊤ := by
    have hLN : pointLocal ≤ N := by
      intro y hy
      exact (show (⟨y,hy⟩ : pointLocal) ∈ D from hD.symm ▸ mem_top _)
    by_contra hnot
    apply PointIndividualGeneration.conjugate_mover_not_point B.card_eq hnB E₁
      (fixed_eq_point_and_movingIndex_of_square_lt E₁ hbig).1 w hwP
    rw [hE₁]
    exact hEN.trans (PointPairGeneration.overgroup_pointLocal N hLN hnot)
  have hkT : f'.ker ≤ T := by
    obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
      (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
    have hQT : Q d.radical a ≤ Q d.radical t := by
      rw [←hjQ,←hjR]
      exact map_mono (h.replacement_core_le d)
    intro y hy
    exact hQT (hfQ ▸ mem_map_of_mem S.subtype (hker ▸ hy))
  have hkTv : f'.ker ≤ T.map (MulAut.conj v).toMonoidHom := by
    intro y hy
    refine ⟨v⁻¹*y*v,hkT ?_,?_⟩
    · change f' (v⁻¹*y*v)=1
      simp [show f' y=1 from hy]
    · simp [MulAut.conj_apply,mul_assoc]
  have he := congrArg (Subgroup.comap f') hN
  rw [comap_map_eq_self (hkTv.trans le_sup_right),comap_top] at he
  exact he

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
