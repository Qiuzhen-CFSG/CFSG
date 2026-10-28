module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedSelection

/-!
# The original plane and the same nonplane selector generate

The nonplane critical image contains its marked full central root. Retain
that root's generating triple before enlarging it to the endpoint image.
Both copies of the root lie in the original full plane, so that plane and
the selected plane generate the whole vertex stabilizer. All residual
lifts use the original full neighborhood kernel. This strengthens the
source selector for the triple-seed propagation in MS93 (5.11).
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

/-- In the proper-J branch, an endpoint outside the chosen plane supplies
an actual full long root in J. The same two residual selectors give generation
by J, full-Z fixed equality, and the original parabolic position. -/
theorem Input.replacement_nonplane_original_plane_selection
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
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      D ⊔ D.map (MulAut.conj g).toMonoidHom = stabilizer d.radical a := by
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
  have hrootx : (RootSubgroup.group (F := B.Carrier) 0).map
      (MulAut.conj x₀).toMonoidHom ≤ P :=
    (map_mono hrootP).trans_eq (mem_normalizer_iff_map_conj_eq.mp hpos₀)
  have hop₀ : P ⊔ P.map (MulAut.conj g₀).toMonoidHom = ⊤ := by
    apply top_unique
    rw [←hrootgen]
    exact sup_le (sup_le
      ((map_mono ((map_le_iff_le_comap).mpr hJplane)).trans le_sup_right)
      (hrootP.trans le_sup_left)) (hrootx.trans le_sup_left)
  have hop : D₀ ⊔ D₀.map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply full_of_full_image f _ (hkD.trans le_sup_left)
    rwa [Subgroup.map_sup,Subgroup.image_conjugate,hmapD,hfg]
  have hop' := congrArg (Subgroup.map S.subtype) hop
  rw [Subgroup.map_sup,Subgroup.image_conjugate,←MonoidHom.range_eq_map,range_subtype] at hop'
  refine ⟨g.val,hg,x.val,hx,hgen',hpair',?_,hxD,⟨x,hxP,rfl⟩,hop'⟩
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
