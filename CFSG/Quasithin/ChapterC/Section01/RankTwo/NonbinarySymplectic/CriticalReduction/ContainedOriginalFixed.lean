module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedRankOneProjection
public import Theory.SpecificGroups.SymplecticFour.FixedPlaneDisplacement

/-!
# Original-vertex fixedness at the contained rank-one selector

The selected plane meets the original plane in exactly the new point:
otherwise the full rank-one image would preserve a line. This point differs
from the original edge point. The original mover has the same full fixed
layer as its plane core, so its selected conjugate fixes only ambient-fixed
elements on the whole original edge Z. Equality of the natural fixed indices
lifts the calculation without removing the central kernel. Every shear in
the original plane core preserves this equality.

This supplies the ORIGINAL vertex mover in MS93 (5.5)(b), printed pp.915--917,
for the same marked rank-one selector used by the individual/paired generation
argument. ContainedIndividualGeneration and ContainedPairedPaths apply it to
those actual choices. The terminal normalizer comparisons, distance exclusions
and minimum-replacement witness remain separate obligations.
-/

public noncomputable section
open Subgroup Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.ContainedOriginalFixed
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem plane_fixed :
    TwoLocalCover.fixedSpace (SymplecticConjugatePair.planeRadical (F := F)) = plane F := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  ext v
  have hh := congrArg (fun W : Submodule (ZMod 2) (Vector F) => v ∈ W)
    (SymplecticConjugatePair.planeRadical_natural_fixedSpace (F := F))
  constructor
  · intro hv
    apply (Iff.of_eq hh).mp
    exact fun g => hv g.val g.property
  · intro hv g hg
    exact (Iff.of_eq hh).mpr hv ⟨g,hg⟩

private theorem conjugate_plane_fixed (w : Sp F) :
    TwoLocalCover.fixedSpace ((SymplecticConjugatePair.planeRadical (F := F)).map
      (MulAut.conj w).toMonoidHom) = (plane F).map (toLinear w).toLinearMap := by
  ext v
  constructor
  · intro hv
    have hin : w⁻¹ • v ∈ TwoLocalCover.fixedSpace (SymplecticConjugatePair.planeRadical (F := F)) := by
      intro y hy
      have hh := congrArg (fun z => w⁻¹ • z) (hv _ (mem_map_of_mem (MulAut.conj w).toMonoidHom hy))
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_smul,inv_smul_smul] using hh
    rw [plane_fixed] at hin
    exact ⟨w⁻¹ • v,hin,smul_inv_smul w v⟩
  · rintro ⟨v,hv,rfl⟩ y ⟨k,hk,rfl⟩
    have hh : k • v=v := ((plane_fixed (F := F)).symm ▸ hv : v ∈ TwoLocalCover.fixedSpace
      (SymplecticConjugatePair.planeRadical (F := F))) k hk
    change (w*k*w⁻¹) • (w • v) = w • v
    simp only [mul_smul,inv_smul_smul,hh]

/-- The plane selected by the literal rank-one projection meets the original
plane in precisely the selected point. -/
private theorem rankOne_selected_plane_intersection
    (A E : Subgroup (Sp F)) (hAP : A ≤ SymplecticConjugatePair.planeRadical)
    (hEP : E ≤ planeParabolic) (w : Sp F)
    (hcore : (SymplecticConjugatePair.planeRadical.map (MulAut.conj w).toMonoidHom) ≤ pointLocal)
    (hgen : ((A ⊔ E.map (MulAut.conj w).toMonoidHom).subgroupOf pointLocal).map pointQuotient = ⊤) :
    plane F ⊓ (plane F).map (toLinear w).toLinearMap = point F := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let W := (plane F).map (toLinear w).toLinearMap
  have hpoint : point F ≤ W := by
    apply Submodule.span_le.mpr
    intro x hx
    have he : x=e (F := F) 0 := Set.mem_singleton_iff.mp hx
    rw [he]
    change e (F := F) 0 ∈ (plane F).map (toLinear w).toLinearMap
    rw [←conjugate_plane_fixed]
    intro y hy
    exact (mem_pointLocal_iff_fixed y).mp (hcore hy)
  have hdim : Module.finrank F W=2 := (toLinear w).finrank_map_eq (plane F) |>.trans finrank_plane
  have hne : W ≠ plane F := by
    intro he
    have hE : E.map (MulAut.conj w).toMonoidHom ≤ planeParabolic := by
      rintro y ⟨k,hk,rfl⟩
      rw [planeParabolic,mem_stabilizer_iff]
      intro v hv
      have hvW : v∈W := he.symm ▸ hv
      obtain ⟨v,hv₀,rfl⟩ := hvW
      rw [←he]
      refine ⟨k • v,(mem_stabilizer_iff _ _).mp (hEP hk) v hv₀,?_⟩
      change w • (k • v) = (w*k*w⁻¹) • (w • v)
      simp only [mul_smul,inv_smul_smul]
    have hA : A ≤ planeParabolic := hAP.trans
      (SymplecticConjugatePair.planeRadical_le_unipotent.trans (unipotent_le_borel.trans inf_le_right))
    have hle := sup_le hA hE
    let t := SpecialLinearGroup.transvection (ι := Fin 2) (F := F) (i := 1) (j := 0) one_ne_zero 1
    obtain ⟨y,hy,hyt⟩ := (show t ∈ ((A ⊔ E.map (MulAut.conj w).toMonoidHom).subgroupOf pointLocal).map
      pointQuotient by rw [hgen]; trivial)
    have hz := (mem_planeParabolic_iff y.val).mp (hle hy) 1 1
    have ht : (pointQuotient y).val 1 0=0 := hz
    rw [hyt] at ht
    simp [t,SpecialLinearGroup.transvection_coe,Matrix.single] at ht
  have hpin : point F ≤ plane F ⊓ W := le_inf point_le_plane hpoint
  apply (Submodule.eq_of_le_of_finrank_le hpin ?_).symm
  rw [finrank_point]
  have hd : Module.finrank F ↥(plane F ⊓ W) ≤ 2 := by
    simpa only [finrank_plane] using Submodule.finrank_mono (show plane F ⊓ W ≤ plane F from inf_le_left)
  by_contra hn
  have hi : plane F ⊓ W = plane F := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [finrank_plane]; omega)
  have hpW : plane F ≤ W := hi ▸ (show plane F ⊓ W ≤ W from inf_le_right)
  exact hne (Submodule.eq_of_le_of_finrank_eq hpW (by rw [finrank_plane,hdim])).symm

/-- The same selected plane moves the original edge point. -/
private theorem rankOne_selected_plane_moves_original_point
    (A E : Subgroup (Sp F)) (hAP : A ≤ SymplecticConjugatePair.planeRadical)
    (hEP : E ≤ planeParabolic) (u w : Sp F)
    (hu : u∈planeLocal) (hun : u∉pointParabolic)
    (hcore : (SymplecticConjugatePair.planeRadical.map (MulAut.conj w).toMonoidHom) ≤ pointLocal)
    (hgen : ((A ⊔ E.map (MulAut.conj w).toMonoidHom).subgroupOf pointLocal).map pointQuotient = ⊤) :
    e (F := F) 0 ∉ TwoLocalCover.fixedSpace (SymplecticConjugatePair.planeRadical.map
      (MulAut.conj (u⁻¹*w)).toMonoidHom) := by
  intro he
  rw [conjugate_plane_fixed] at he
  obtain ⟨v,hv,he⟩ := he
  have hmem : u • e (F := F) 0 ∈ plane F ⊓ (plane F).map (toLinear w).toLinearMap := by
    refine ⟨(mem_stabilizer_iff _ _).mp (planeLocal_le hu) _ (e_mem_plane 0),v,hv,?_⟩
    change (u⁻¹*w) • v = e (F := F) 0 at he
    change w • v = u • e (F := F) 0
    have hh := congrArg (fun z => u • z) he
    simpa only [mul_smul,smul_inv_smul] using hh
  rw [rankOne_selected_plane_intersection A E hAP hEP w hcore hgen] at hmem
  apply hun
  rw [mem_pointParabolic_iff]
  simpa [mem_point_iff,Theory.SpecificGroups.SymplecticFour.smul_eq_mulVec,Theory.SpecificGroups.SymplecticFour.e,Matrix.mulVec_single] using hmem


private theorem full_fixed_of_image_fixed
    {G D : Type*} [Group G] [Group D]
    (U S : Subgroup G) (hUS : U ≤ S) [Finite U]
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) D V) (f : S →* D)
    (hindex : ∀ A : Subgroup S, (centralizer (A : Set S)).relIndex (U.subgroupOf S) =
      2 ^ fixedCodim σ (A.map f))
    (E : Subgroup G) (hES : E ≤ S)
    (hfix : fixedSpace σ ((E.subgroupOf S).map f) = fixedSpace σ ((⊤ : Subgroup S).map f)) :
    U ⊓ centralizer (E : Set G) = U ⊓ centralizer (S : Set G) := by
  have he := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    (U.subgroupOf S) (E.subgroupOf S)
  have hs := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    (U.subgroupOf S) ⊤
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hindex] at he
  rw [map_subgroupOf_eq_of_le hUS,←MonoidHom.range_eq_map,range_subtype,hindex] at hs
  have hi : (centralizer (E : Set G)).relIndex U = (centralizer (S : Set G)).relIndex U := by
    rw [he,hs,fixedCodim,fixedCodim,hfix]
  let CE := (centralizer (E : Set G)).subgroupOf U
  let CS := (centralizer (S : Set G)).subgroupOf U
  have hCE : CE=CS := by
    apply (eq_of_le_of_card_ge (comap_mono (centralizer_le hES)) ?_).symm
    have hE := CE.card_mul_index
    have hS := CS.card_mul_index
    change CE.index=CS.index at hi
    rw [hi] at hE
    exact (Nat.eq_of_mul_eq_mul_right (index_ne_zero_of_finite (H := CS)).bot_lt
      (hE.trans hS.symm)).le
  apply le_antisymm
  · intro u hu
    exact ⟨hu.1,show (⟨u,hu.1⟩ : U) ∈ CS from hCE ▸ hu.2⟩
  · exact inf_le_inf_left _ (centralizer_le hES)

private theorem conjugate_full_fixed {G : Type*} [Group G]
    (Z J D : Subgroup G) (he : Z ⊓ centralizer (J : Set G) = Z ⊓ centralizer (D : Set G))
    (g : G) (hg : g ∈ normalizer (Z : Set G)) :
    Z ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set G) =
      Z ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hz := mem_normalizer_iff_map_conj_eq.mp hg
  change Z.map (MulAut.conj g).toMonoidHom = Z at hz
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_inf _ _ _ (MulAut.conj g).injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,hz] at hh
  exact hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.ContainedOriginalFixed

open Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers ContainedOriginalFixed
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- On the actual marked contained selector, the original vertex mover fixes
only ambient-fixed elements of the entire original edge layer. -/
theorem Input.replacement_contained_marked_original_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2))
    (B : BinaryField) (hB : B.degree=n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f)
    (A : Subgroup (Sp B.Carrier))
    (u v : stabilizer d.radical a) (hu : f u∈planeLocal) (hun : f u∉pointParabolic)
    (hAP : A ≤ (CentralRootGeometry.wing true).map unipotent.subtype)
    (hcore : (planeParabolic.map (MulAut.conj (f u*f v)).toMonoidHom).pCoreIn 2 ≤ pointLocal)
    (hgen : ((A ⊔ (((Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a)).map f).map
        (MulAut.conj (f u*f v)).toMonoidHom).subgroupOf pointLocal).map pointQuotient=⊤) :
    Z d.radical t ⊓ centralizer ((Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map (MulAut.conj v.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let S := stabilizer d.radical a
  let T := Q d.radical t
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) T (Nat.card F^2)
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) T (Nat.card F^2)
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  let Dv := D.map (MulAut.conj v.val).toMonoidHom
  let E₀ := E.subgroupOf S
  let E₁ := (E₀.map f).subgroupOf unipotent
  let σ := SymplecticConjugatePair.binaryNatural (F := B.Carrier)
  have hTS : T ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hET : E ≤ T := Subgroup.SmallMover.join_le _ _ _ _
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ _)
  have hES : E ≤ S := hET.trans hTS
  have hEf : E₀.map f ≤ unipotent := (map_mono (comap_mono hET)).trans hTf
  have hE₁ : E₁.map unipotent.subtype=E₀.map f := map_subgroupOf_eq_of_le hEf
  have hmove : movingIndex E₁ =
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) E₁ = _
    rw [fixedCodim,fixedSpace_comp_map,hE₁]
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) E₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hES,hindex] at hh
    exact hh.symm
  have hbig : Nat.card B.Carrier^2 < movingIndex E₁ := by
    rw [hmove,show Nat.card B.Carrier=Nat.card F by rw [B.card_eq,hB,h.field_card]]
    exact (h.replacement_unequal_individual_indices d geometry hb ha hat hct hne).2
  have hEfix := (fixed_eq_point_and_movingIndex_of_square_lt E₁ hbig).1
  have hP : P=SymplecticConjugatePair.planeRadical := SymplecticConjugatePair.planeRadical_eq_wing.symm
  have hcore' : P.map (MulAut.conj (f u*f v)).toMonoidHom ≤ pointLocal := by
    rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (f u*f v)).injective,pCoreIn,
      planeParabolic_core_map_eq_radical B.card_eq (by rw [hB]; exact h.nonbinary)] at hcore
    rw [hP]
    exact hcore
  have hmoves : e (F := B.Carrier) 0 ∉ TwoLocalCover.fixedSpace (P.map (MulAut.conj (f v)).toMonoidHom) := by
    have hh := rankOne_selected_plane_moves_original_point A (E₀.map f)
      (hAP.trans_eq hP) (hEf.trans (unipotent_le_borel.trans inf_le_right)) (f u) (f u*f v) hu hun
      (by rwa [←hP]) hgen
    simpa only [inv_mul_cancel_left,←hP] using hh
  have hDS : D ≤ S := map_subtype_le _
  have hDvS : Dv ≤ S := by
    rintro y ⟨x,hx,rfl⟩
    exact S.mul_mem (S.mul_mem v.property (hDS hx)) (S.inv_mem v.property)
  have hDvf : (Dv.subgroupOf S).map f = P.map (MulAut.conj (f v)).toMonoidHom := by
    have hdv : Dv.subgroupOf S=D₀.map (MulAut.conj v).toMonoidHom := by
      apply Subgroup.map_injective S.subtype_injective
      rw [map_subgroupOf_eq_of_le hDvS,Subgroup.image_conjugate]
      rfl
    rw [hdv,Subgroup.image_conjugate,map_comap_eq_self_of_surjective hf]
  let C := T ⊔ Dv
  have hCS : C ≤ S := sup_le hTS hDvS
  have hzero : fixedSpace σ ((C.subgroupOf S).map f) = ⊥ := by
    apply le_antisymm _ bot_le
    intro z hz
    have hEz : z∈fixed E₁ := by
      rw [CentralRootGeometry.SmallMovers.fixed,mem_invariants]
      intro k
      have hk : k.val.val∈E₀.map f := by
        rw [←hE₁]
        exact mem_map_of_mem unipotent.subtype k.property
      exact hz ⟨k.val.val,(map_mono (comap_mono (hET.trans le_sup_left))) hk⟩
    rw [hEfix] at hEz
    obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hEz
    by_cases hr : r=0
    · simp only [hr,zero_smul,Submodule.zero_mem]
    have hzD : r • e (F := B.Carrier) 0 ∈ TwoLocalCover.fixedSpace (P.map (MulAut.conj (f v)).toMonoidHom) := by
      intro y hy
      rw [←hDvf] at hy
      exact hz ⟨y,(map_mono (comap_mono (show Dv ≤ C from le_sup_right))) hy⟩
    exact False.elim (hmoves ((Submodule.smul_mem_iff _ hr).mp hzD))
  have htop : fixedSpace σ ((⊤ : Subgroup S).map f)=⊥ := by
    apply le_antisymm _ bot_le
    rw [←hzero]
    exact fixedSpace_antitone σ (map_mono le_top)
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hU := full_fixed_of_image_fixed (U d.radical a) S hUS σ f hindex C hCS (hzero.trans htop.symm)
  have hZ := h.replacement_edge_fixed_mono_of_U d geometry hb ha hat C S hCS le_rfl hU.le
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb ha hat B hB f hf hfQ hindex hJplane
  have hev := conjugate_full_fixed (Z d.radical a) J D he v.val (Z_normalized _ _ v.property)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans hTS
  have hJvS : J.map (MulAut.conj v.val).toMonoidHom ≤ S := by
    rintro y ⟨x,hx,rfl⟩
    exact S.mul_mem (S.mul_mem v.property (hJS hx)) (S.inv_mem v.property)
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le hJvS))
  intro z hz
  have hzD : z∈centralizer (Dv : Set (FreeAmalgam d.radical)) :=
    (hev ▸ (show z∈Z d.radical a ⊓ centralizer (J.map (MulAut.conj v.val).toMonoidHom : Set _) from
      ⟨adjacent_Z_le _ ha hat hz.1,hz.2⟩)).2
  apply hZ
  refine ⟨hz.1,?_⟩
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne _ hat
    rw [ha] at hh
    exact Ne.symm hh
  have hzT : z∈centralizer (T : Set (FreeAmalgam d.radical)) := by
    have hz' := hz.1
    rw [Z,if_neg ht] at hz'
    exact (mem_omegaCenter_iff.mp hz').2.2
  have hTC : T ≤ centralizer ({z} : Set (FreeAmalgam d.radical)) :=
    fun y hy => mem_centralizer_singleton_iff.mpr (hzT y hy)
  have hDC : Dv ≤ centralizer ({z} : Set (FreeAmalgam d.radical)) :=
    fun y hy => mem_centralizer_singleton_iff.mpr (hzD y hy)
  intro y hy
  exact mem_centralizer_singleton_iff.mp ((sup_le hTC hDC) hy)


/-- Every shear in the same original plane core preserves the original-edge
fixed equality. This applies to the actual shear chosen for paired generation. -/
theorem Input.replacement_plane_shear_edge_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree=n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f)
    (E : Subgroup (FreeAmalgam d.radical))
    (hfixed : Z d.radical t ⊓ centralizer (E : Set (FreeAmalgam d.radical)) =
      Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (x : stabilizer d.radical a) (hx : f x∈(planeParabolic (F := B.Carrier)).pCoreIn 2) :
    Z d.radical t ⊓ centralizer (E.map (MulAut.conj x.val).toMonoidHom : Set (FreeAmalgam d.radical)) =
      Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2)
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb ha hat B hB f hf hfQ hindex hJplane
  have hxD : x.val∈D := by
    apply mem_map_of_mem S.subtype
    change f x∈(CentralRootGeometry.wing true).map unipotent.subtype
    rw [←SymplecticConjugatePair.planeRadical_eq_wing]
    rw [pCoreIn,planeParabolic_core_map_eq_radical B.card_eq (by rw [hB]; exact h.nonbinary)] at hx
    exact hx
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Ne.symm hh
  have hxC : x.val∈centralizer (Z d.radical t : Set (FreeAmalgam d.radical)) := by
    intro z hz
    have hzJ : z∈centralizer (J : Set (FreeAmalgam d.radical)) := by
      have hz' := hz
      rw [Z,if_neg ht] at hz'
      intro y hy
      exact (mem_omegaCenter_iff.mp hz').2.2 y ((Subgroup.SmallMover.join_le _ _ _ _) hy)
    have hzD : z∈centralizer (D : Set (FreeAmalgam d.radical)) :=
      (he ▸ (show z∈Z d.radical a ⊓ centralizer (J : Set _) from ⟨adjacent_Z_le _ ha hat hz,hzJ⟩)).2
    exact (hzD x.val hxD).symm
  have hh := conjugate_full_fixed (Z d.radical t) E S hfixed x.val
    (Subgroup.centralizer_le_normalizer _ hxC)
  have hs : S.map (MulAut.conj x.val).toMonoidHom=S :=
    mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer x.property)
  rwa [hs] at hh

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
