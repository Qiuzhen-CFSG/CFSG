module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointLargeSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerSelection
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry
/-!
# Smaller-mover selection when the critical image escapes the plane

The full critical endpoint has fixed index at most q squared on the actual
U-layer. In any exact marking, an endpoint outside the chosen plane radical
is therefore a full point-plane subgroup of order q squared. Its central
long root lies in both the endpoint image and J: the latter follows from
the already proved literal intersection J = T intersect Q₁.

Apply the smaller-plane root calculation to this root, then enlarge to the
original critical endpoint. The same residual pair gives generation using
J itself, a generating pair of full parabolic cores, fixed-subgroup equality
on the entire Z-layer, and position in the original parabolic. Every lift
retains the full Q-kernel and the original nonbinary field degree.

NonplanePaths applies this selector to the actual equal-mover neighboring
pair and constructs its overlapping backward critical path. The case where
the large endpoint lies inside the chosen plane, the individual unequal
movers, the trapped-root and terminal exclusions still require their source
arguments. No original-radical characteristic control follows here.
Source: MS93 (5.6)--(5.8), printed pp.917--920.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
private theorem full_of_full_image {S T : Type*} [Group S] [Group T]
    (f : S →* T) (D : Subgroup S) (hk : f.ker ≤ D) (hm : D.map f = ⊤) : D=⊤ := by
  apply top_unique
  intro y _
  obtain ⟨z,hz,he⟩ := (show f y ∈ D.map f by rw [hm]; trivial)
  have hzy : z⁻¹*y ∈ f.ker := by
    change f (z⁻¹*y)=1
    simp [he]
  have hh := D.mul_mem hz (hk hzy)
  simpa using hh

private theorem kernel_le_conjugate {S T : Type*} [Group S] [Group T]
    (f : S →* T) (D : Subgroup S) (hk : f.ker ≤ D) (g : S) :
    f.ker ≤ D.map (MulAut.conj g).toMonoidHom := by
  intro y hy
  refine ⟨g⁻¹*y*g,hk ?_,?_⟩
  · change f (g⁻¹*y*g)=1
    simp [show f y=1 from hy]
  · simp [MulAut.conj_apply,mul_assoc]

private theorem conjugate_fixed_eq {G : Type*} [Group G]
    (Z J D : Subgroup G) (he : Z ⊓ centralizer (J : Set G) = Z ⊓ centralizer (D : Set G))
    (g : G) (hg : g ∈ normalizer (Z : Set G)) :
    Z ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set G) =
      Z ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hz := mem_normalizer_iff_map_conj_eq.mp hg
  change Z.map (MulAut.conj g).toMonoidHom = Z at hz
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_inf _ _ _ (MulAut.conj g).injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,
    hz] at hh
  exact hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual critical endpoint moves at most q squared cosets of the whole U-layer. -/
theorem Input.replacement_critical_U_index_le_square
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2 := by
  obtain ⟨B,hB,f,hf,hfQ,hindex,hquad⟩ := h.replacement_critical_natural_indices d path hb
  have hi := quadratic_natural_fixed_index_le_square
    (((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f) hquad
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hi
  have hh := Subgroup.SmallMover.centralizer_index_map
    (stabilizer d.radical a).subtype (stabilizer d.radical a).subtype_injective
    ((U d.radical a).subgroupOf (stabilizer d.radical a))
    ((Z d.radical z).subgroupOf (stabilizer d.radical a))
  rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
    map_subgroupOf_eq_of_le (path.endpoint_Z_le_start_stabilizer (by omega)),hindex] at hh
  rw [hh]
  simpa only [fixedCodim,B.card_eq,hB,h.field_card] using hi

/-- An endpoint outside the chosen plane is exactly a full point-plane image.
The relative order is measured through the original full Q-kernel. -/
theorem Input.replacement_nonplane_critical_coordinates
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
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
    (hout : ¬ ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype) :
    (Q d.radical a).relIndex (Z d.radical z) = Nat.card F^2 ∧
      ∃ l : B.Carrier,
        ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f =
          (finitePlane l).map unipotent.subtype := by
  let S := stabilizer d.radical a
  let A₀ := (Z d.radical z).subgroupOf S
  let A := (A₀.map f).subgroupOf unipotent
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hAU : A₀.map f ≤ unipotent := (map_mono (comap_mono hzT)).trans hTf
  have hAm : A.map unipotent.subtype = A₀.map f := map_subgroupOf_eq_of_le hAU
  have hc : Nat.card A = (Q d.radical a).relIndex (Z d.radical z) := by
    rw [←card_map_of_injective unipotent.subtype_injective,hAm,←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hzS] at hh
    exact hh.symm
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hi : movingIndex A ≤ Nat.card B.Carrier^2 := by
    have hh := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      ((U d.radical a).subgroupOf S) A₀
    rw [map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer d.radical a)),
      map_subgroupOf_eq_of_le hzS,hindex] at hh
    have hi := h.replacement_critical_U_index_le_square d path hb
    rw [hh] at hi
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype) A ≤ _
    rw [fixedCodim,fixedSpace_comp_map,hAm,hBF]
    exact hi
  have hn : ¬ A ≤ CentralRootGeometry.wing true := by
    intro he
    apply hout
    rw [←hAm]
    exact map_mono he
  have hlarge : Nat.card B.Carrier^2 ≤ Nat.card A := by
    rw [hc,hBF]
    by_contra hbad
    have hs : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by omega
    have hp := h.replacement_endpoint_le_parabolic_core d path hb hfirst hs B hB f hTf hindex
    apply hout
    apply (map_le_iff_le_comap).mpr
    intro y hy
    obtain ⟨v,hv,hv'⟩ := hp hy
    have he : v=y := Subtype.ext hv'
    exact he ▸ hv
  obtain ⟨l,hl⟩ := Degree.eq_finitePlane_of_small_not_le_wing A (hi.trans hlarge) hi hn
  refine ⟨?_,l,?_⟩
  · rw [←hc,hl,card_finitePlane,hBF]
  · rw [←hAm,hl]

/-- In the proper-J branch, an endpoint outside the chosen plane supplies
an actual full long root in J. The same two residual selectors give generation
by J, full-Z fixed equality, and the original parabolic position. -/
theorem Input.replacement_nonplane_smaller_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hout : ¬ ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype)
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a ∧
      (D.map (MulAut.conj g).toMonoidHom ⊔
        (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a) ∧
      ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
        centralizer ((J.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype := by
  dsimp only
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let J₀ := J.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hsat := h.replacement_small_mover_parabolic_intersection d geometry hb path.start_color hat
    B hB f hf hindex hJplane
  change Q d.radical t ⊓ D = J at hsat
  have hJD : J ≤ D := by rw [←hsat]; exact inf_le_right
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hJS : J ≤ S := hJD.trans hDS
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hzT : Z d.radical z ≤ Q d.radical t := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.dist_end,geometry.distance_constant z path.end_color]
    change path.walk.length - 1 < geometry.b d.radical
    rw [path.length_eq_b]
    omega
  have hmapD : D₀.map f=P := map_comap_eq_self_of_surjective hf _
  have hkD : f.ker ≤ D₀ := by
    intro y hy
    change f y ∈ P
    rw [MonoidHom.mem_ker.mp hy]
    exact P.one_mem
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkJ : f.ker ≤ J₀ := by
    intro y hy
    have hyQ : y.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hy
    change y.val ∈ J
    rw [←hsat]
    exact ⟨hQT hyQ,mem_map_of_mem S.subtype (hkD hy)⟩
  have hcard : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hcJ : Nat.card B.Carrier^2 ≤ Nat.card (J₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at hh
    rw [←hh,hcard]
    exact h.replacement_small_mover_join_index d geometry hb path.start_color hat
  obtain ⟨_,l,hl⟩ := h.replacement_nonplane_critical_coordinates d path hb hfirst
    B hB f hfQ hTf hindex hout
  have hrootA : RootSubgroup.group 0 ≤ A₀.map f := by
    rw [hl]
    intro y hy
    obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff 0 y).mp hy
    refine ⟨CentralRootGeometry.element 0 s 0 0,
      (element_mem_finitePlane l _ _ _ _).mpr (by simp),?_⟩
    simp [CentralRootGeometry.element,RootSubgroup.element_zero]
  have hrootP : RootSubgroup.group (F := B.Carrier) 0 ≤ P := by
    intro y hy
    obtain ⟨s,rfl⟩ := (RootSubgroup.mem_group_iff 0 y).mp hy
    refine ⟨CentralRootGeometry.element 0 s 0 0,
      (CentralRootGeometry.element_mem_wing true _ _ _ _).mpr rfl,?_⟩
    simp [CentralRootGeometry.element,RootSubgroup.element_zero]
  have hrootJ : RootSubgroup.group 0 ≤ J₀.map f := by
    intro y hy
    obtain ⟨v,hv,hfv⟩ := hrootA hy
    refine ⟨v,?_,hfv⟩
    change v.val ∈ J
    rw [←hsat]
    refine ⟨hzT hv,mem_map_of_mem S.subtype ?_⟩
    change f v ∈ P
    rw [hfv]
    exact hrootP hy
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨g₀,x₀,hrootgen,hpair₀,hpos₀⟩ := SmallPlaneGeneration.exists_subplane_root_generators hq
    P (J₀.map f) (RootSubgroup.group 0) ⟨1,by
      rw [show (MulAut.conj (1 : Sp B.Carrier)).toMonoidHom = MonoidHom.id _ by ext y; simp,
        Subgroup.map_id]⟩ ((map_le_iff_le_comap).mpr hJplane)
    hrootJ (by nlinarith) (RootSubgroup.card 0) (by
      rw [PointRadicalAction.root_displacement,finrank_point])
  have hgen₀ : ((J₀.map f).map (MulAut.conj g₀).toMonoidHom ⊔ A₀.map f) ⊔
      (A₀.map f).map (MulAut.conj x₀).toMonoidHom = ⊤ :=
    top_unique (hrootgen.ge.trans (sup_le_sup (sup_le_sup_left hrootA _) (map_mono hrootA)))
  have hL : L₀.map f=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two hq
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L₀.map f by rw [hL]; trivial)
  obtain ⟨x,hx,hfx⟩ := (show x₀ ∈ L₀.map f by rw [hL]; trivial)
  have hgen : (J₀.map (MulAut.conj g).toMonoidHom ⊔ A₀) ⊔
      A₀.map (MulAut.conj x).toMonoidHom = ⊤ := by
    apply full_of_full_image f _ ((kernel_le_conjugate f J₀ hkJ g).trans
      (le_sup_left.trans le_sup_left))
    rwa [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,hfg,hfx]
  have hpair : D₀.map (MulAut.conj g).toMonoidHom ⊔
      (D₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤ := by
    apply full_of_full_image f _ ((kernel_le_conjugate f D₀ hkD g).trans le_sup_left)
    rwa [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,Subgroup.image_conjugate,
      hmapD,hfg,map_inv,hfx]
  have hgen' := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,
    map_subgroupOf_eq_of_le hJS,map_subgroupOf_eq_of_le hzS,
    ←MonoidHom.range_eq_map,range_subtype] at hgen'
  have hpair' := congrArg (Subgroup.map S.subtype) hpair
  rw [Subgroup.map_sup,Subgroup.image_conjugate,Subgroup.image_conjugate,Subgroup.image_conjugate,
    ←MonoidHom.range_eq_map,range_subtype] at hpair'
  have hxN : x ∈ normalizer (D₀ : Set S) := by
    apply P.le_normalizer_comap f
    change f x ∈ normalizer (P : Set (Sp B.Carrier))
    rw [hfx]
    exact hpos₀
  have hxD : x.val ∈ normalizer (D : Set (FreeAmalgam d.radical)) :=
    D₀.le_normalizer_map S.subtype (mem_map_of_mem S.subtype hxN)
  have hxP := D₀.le_normalizer_map f (mem_map_of_mem f hxN)
  rw [hmapD,show P=planeRadicalAmbient from SymplecticConjugatePair.planeRadical_eq_wing.symm,
    planeRadicalAmbient_normalizer B.card_eq (by rw [hB]; exact h.nonbinary)] at hxP
  refine ⟨g.val,hg,x.val,hx,hgen',hpair',?_,hxD,⟨x,hxP,rfl⟩⟩
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb path.start_color hat
    B hB f hf hfQ hindex hJplane
  have he₁ := conjugate_fixed_eq (Z d.radical a) J D he g.val
    (Z_normalized d.radical a g.property)
  have he₂ := conjugate_fixed_eq (Z d.radical a) _ _ he₁ x.val⁻¹
    (Z_normalized d.radical a (S.inv_mem x.property))
  apply le_antisymm
  · intro w hw
    have hw₁ := he₁ ▸ hw.1
    have hw₂ := he₂ ▸ (show w ∈ Z d.radical a ⊓ centralizer
      ((J.map (MulAut.conj g.val).toMonoidHom).map (MulAut.conj x.val⁻¹).toMonoidHom :
        Set (FreeAmalgam d.radical)) from ⟨hw.1.1,hw.2⟩)
    refine ⟨hw.1.1,?_⟩
    have h₁ : D.map (MulAut.conj g.val).toMonoidHom ≤ centralizer ({w} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw₁.2 y hy)
    have h₂ : (D.map (MulAut.conj g.val).toMonoidHom).map (MulAut.conj x.val⁻¹).toMonoidHom ≤
        centralizer ({w} : Set (FreeAmalgam d.radical)) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hw₂.2 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hpair'.symm ▸ hy))
  · intro w hw
    have hJg : J.map (MulAut.conj g.val).toMonoidHom ≤ S := le_sup_left.trans le_sup_left |>.trans_eq hgen'
    have hJgx : (J.map (MulAut.conj g.val).toMonoidHom).map (MulAut.conj x.val⁻¹).toMonoidHom ≤ S := by
      rintro y ⟨v,hv,rfl⟩
      exact S.mul_mem (S.mul_mem (S.inv_mem x.property) (hJg hv)) (S.inv_mem (S.inv_mem x.property))
    exact ⟨⟨hw.1,centralizer_le hJg hw.2⟩,centralizer_le hJgx hw.2⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
