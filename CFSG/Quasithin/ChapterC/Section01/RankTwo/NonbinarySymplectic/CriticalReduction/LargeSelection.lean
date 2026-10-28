module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.CubicSelection
public import Theory.SpecificGroups.SymplecticFour.SelectedLargePlaneGeneration

/-!
# Full-plane selectors for every critical-image size

For an image larger than q, the actual critical endpoint is quadratic in
its literal natural quotient. The large quadratic model selector gives
one-conjugate generation and a generating pair of plane radicals. Both
conjugators lift to the original residual through the entire Q-kernel.
The pair therefore fixes exactly the ambient-fixed subgroup of the full
Z-layer, with all central attachments retained.

Combining this with the field-sized selector covers every critical-image
size for a small-mover join of relative order q cubed. The chosen-plane
application identifies that join with the literal parabolic core and
retains the parabolic-positioning conclusion in the field-sized branch.
The proper-join large-image case and unequal neighboring movers remain
open, as do the selected-path exclusions and the distance-two witness.

Source: MS93 (5.6)(b--d), printed pp.917--918. No field-degree reduction,
central complement, or original-radical characteristic control is used.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A cubic mover generates with every large critical endpoint using one
residual conjugate; the same pair generates with both plane radicals. -/
theorem Input.replacement_cubic_mover_large_selection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hlarge : Nat.card F < (Q d.radical a).relIndex (Z d.radical z))
    (E : Subgroup (FreeAmalgam d.radical)) (hES : E ≤ stabilizer d.radical a)
    (hQE : Q d.radical a ≤ E) (hpE : IsPGroup 2 E)
    (hEc : (Q d.radical a).relIndex E = Nat.card F^3)
    (hEm : (centralizer (E : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      E.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      (E.map (MulAut.conj g).toMonoidHom ⊔
        (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a) := by
  obtain ⟨B,hB,f,hf,hfQ,π,hπ,hπker,hact⟩ :=
    h.replacement_inner_natural_action d geometry hb path.start_color
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  let S := stabilizer d.radical a
  let E₀ := E.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkE : f.ker ≤ E₀ := by rw [hQeq]; exact comap_mono hQE
  have hEcard : Nat.card (E₀.map f) = Nat.card B.Carrier^3 := by
    rw [←relIndex_ker,hQeq]
    have he := relIndex_map_map_of_injective ((Q d.radical a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at he
    rw [←he,hEc,hBF]
  have hEn : E ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) := hES.trans (U_normalized a)
  let δE := f.comp (inclusion hES)
  have hδE : δE.range = E₀.map f := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hy => ⟨⟨y.val,hy⟩,rfl⟩⟩
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hEmodel : Nat.card (Vector B.Carrier ⧸ fixedSpace
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2)) (E₀.map f)) ≤ Nat.card B.Carrier^2 := by
    have hh := Representation.fixed_quotient_card_le_centralizer_index (U d.radical a) E hEn π hπ
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := B.Carrier) 2)) δE
      (fun x u => hact (inclusion hES x) u)
    rw [hδE] at hh
    rw [hBF]
    exact hh.trans hEm
  obtain ⟨k,hk⟩ := SelectedPlaneGeneration.conjugate_plane_of_cubic_order B.card_eq
    (by rw [hB]; exact Nat.zero_lt_one.trans h.nonbinary) (E₀.map f) (hpE.comap_subtype.map f) hEcard hEmodel
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact (show 0 < geometry.b d.radical by omega))
        z path.end_color path.critical }
  let δ := f.comp (inclusion hzS)
  have hδ : δ.range = A₀.map f := by
    rw [MonoidHom.range_comp]
    congr 1
    ext y
    exact ⟨fun ⟨x,hx⟩ => hx ▸ x.property,fun hy => ⟨⟨y.val,hy⟩,rfl⟩⟩
  have hδcard : Nat.card δ.range = (Q d.radical a).relIndex (Z d.radical z) :=
    Sp4Four.SourceComparison.quotient_image_card _ _ _ hzS f hfQ
  have hc : Nat.card B.Carrier < Nat.card (A₀.map f) := by
    rw [←hδ,hδcard,hBF]
    exact hlarge
  have hq := critical_quotient_actor_quadratic rev (by omega) π hπ δ
    (fun x u => hact (inclusion hzS x) u)
  rw [hδ] at hq
  obtain ⟨g₀,x₀,hgen₀,hpair₀⟩ := SelectedLargePlaneGeneration.exists_plane_large_quadratic_selection
    (E₀.map f) (A₀.map f) ⟨k,hk⟩ hq hc
  have hL : L₀.map f=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two (by
      rw [hBF,h.field_card]
      exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L₀.map f by rw [hL]; trivial)
  obtain ⟨x,hx,hfx⟩ := (show x₀ ∈ L₀.map f by rw [hL]; trivial)
  have hkg : f.ker ≤ E₀.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hkE
    simpa only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq] using hh
  have hgen : E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀ = ⊤ := by
    have hm : (E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀).map f = ⊤ := by
      rwa [Subgroup.map_sup,Subgroup.image_conjugate,hfg]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkg.trans le_sup_left),comap_top] at hh
  have hpair : E₀.map (MulAut.conj g).toMonoidHom ⊔
      (E₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
    have hm : (E₀.map (MulAut.conj g).toMonoidHom ⊔
        (E₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom).map f = ⊤ := by
      rwa [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
        Subgroup.image_conjugate,hfg,map_inv,hfx]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkg.trans le_sup_left),comap_top] at hh
  refine ⟨g.val,hg,x.val,hx,?_,?_⟩
  · have hm := congrArg (Subgroup.map S.subtype) hgen
    rw [Subgroup.map_sup,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le hES,map_subgroupOf_eq_of_le hzS,
      ←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm
  · have hm := congrArg (Subgroup.map S.subtype) hpair
    rw [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,Subgroup.image_conjugate,
      map_subgroupOf_eq_of_le hES,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hm

/-- The actual cubic-order small-mover join now has the source selector
for every critical image size. Field-sized images retain parabolic positioning;
larger images use one conjugate for generation. The whole Z-layer is retained. -/
theorem Input.replacement_cubic_small_mover_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 →
        Z d.radical z ≤ J → x ∈ normalizer (J : Set (FreeAmalgam d.radical))) := by
  dsimp only
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hTS : Q d.radical t ≤ stabilizer d.radical a := by
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hpT : IsPGroup 2 (Q d.radical t) := hjR ▸ (h.replacement_two_group d).map j
  have hpJ : IsPGroup 2 J := hpT.of_injective (inclusion hJT) (inclusion_injective _)
  by_cases hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · obtain ⟨g,hg,x,hx,hgen,hfixed,hpos⟩ :=
      h.replacement_cubic_small_mover_root_selection d path hb hat hsmall hJc hJm
    exact ⟨g,hg,x,hx,hgen,hfixed,fun _ => hpos⟩
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hlarge : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) :=
    lt_of_lt_of_le (by nlinarith : Nat.card F < Nat.card F^2) (le_of_not_gt hsmall)
  obtain ⟨g,hg,x,hx,hgen,hpair⟩ := h.replacement_cubic_mover_large_selection d
    path hb hlarge J (hJT.trans hTS) hQJ hpJ hJc hJm
  refine ⟨g,hg,x,hx,?_,?_,fun hs => (hsmall hs).elim⟩
  · apply le_antisymm
    · apply sup_le hgen.le
      rintro y ⟨w,hw,rfl⟩
      have hxS := Ltilde_le_stabilizer a hx
      have hwS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical) hw
      exact (stabilizer d.radical a).mul_mem
        ((stabilizer d.radical a).mul_mem hxS hwS) ((stabilizer d.radical a).inv_mem hxS)
    · exact hgen.ge.trans le_sup_left
  · have hfixed : centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
      apply le_antisymm
      · intro w hw s hs
        have h₁ : J.map (MulAut.conj g).toMonoidHom ≤ centralizer ({w} : Set (FreeAmalgam d.radical)) :=
          fun y hy => mem_centralizer_singleton_iff.mpr (hw.1 y hy)
        have h₂ : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
            centralizer ({w} : Set (FreeAmalgam d.radical)) :=
          fun y hy => mem_centralizer_singleton_iff.mpr (hw.2 y hy)
        exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hpair.symm ▸ hs))
      · exact le_inf (centralizer_le (show J.map (MulAut.conj g).toMonoidHom ≤ stabilizer d.radical a from
          le_sup_left.trans_eq hpair))
          (centralizer_le (show (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤
            stabilizer d.radical a from le_sup_right.trans_eq hpair))
    rw [inf_assoc,hfixed]


/-- For the actual chosen plane, the cubic-order join supplies all critical-image
branches of generation and whole-Z fixed equality, with source positioning
when the critical image is field-sized. -/
theorem Input.replacement_cubic_mover_chosen_plane_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (hfirst : path.walk.getVert 1 = t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJc : (Q d.radical a).relIndex (Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2)) = Nat.card F^3)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    J.subgroupOf (stabilizer d.radical a) =
      ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 →
        x ∈ normalizer (J : Set (FreeAmalgam d.radical)) ∧
        x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype) := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hJS : J ≤ S := by
    apply (Subgroup.SmallMover.join_le _ _ _ _).trans
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQJ : Q d.radical a ≤ J := by
    have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
      (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
      (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
      (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
        (h.replacement_two_group d) (h.replacement_core_le d)))
    rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh
  have hk : f.ker ≤ J₀ := by
    intro x hx
    exact hQJ (hfQ ▸ mem_map_of_mem S.subtype hx)
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hc : Nat.card (J₀.map f) = Nat.card B.Carrier^3 := by
    rw [←relIndex_ker]
    have he := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at he
    rw [←he,hJc,hcard]
  have hm : J₀.map f=P := by
    apply eq_of_le_of_card_ge ((map_le_iff_le_comap).mpr hJplane)
    rw [hc,card_map_of_injective unipotent.subtype_injective,CentralRootGeometry.card_wing]
  have heq : J₀=P.comap f := by rw [←hm,comap_map_eq_self hk]
  have hJm : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2 := by
    have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
    have he := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) J₀
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,hindex,hm] at he
    have hp : P=SymplecticConjugatePair.planeRadical :=
      SymplecticConjugatePair.planeRadical_eq_wing.symm
    rw [hp] at he
    change (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      2 ^ fixedCodim (SymplecticConjugatePair.binaryNatural (F := B.Carrier))
        SymplecticConjugatePair.planeRadical at he
    rw [SymplecticConjugatePair.planeRadical_natural_fixedCodim B.card_eq] at he
    rw [he,h.field_card,hB,show 2*n=n*2 by omega,pow_mul]
  by_cases hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · obtain ⟨heq,g,hg,x,hx,hgen,hfixed,hn,hp⟩ :=
      h.replacement_cubic_small_mover_plane_selection d path hb hat hfirst hsmall
        B hB f hfQ hTf hindex hJc hJplane
    exact ⟨heq,g,hg,x,hx,hgen,hfixed,fun _ => ⟨hn,hp⟩⟩
  · obtain ⟨g,hg,x,hx,hgen,hfixed,_⟩ :=
      h.replacement_cubic_small_mover_selection d path hb hat hJc hJm
    exact ⟨heq,g,hg,x,hx,hgen,hfixed,fun hs => (hsmall hs).elim⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
