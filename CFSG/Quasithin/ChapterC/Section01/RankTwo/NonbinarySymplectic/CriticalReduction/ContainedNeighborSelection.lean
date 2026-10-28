module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NeighborEdgeFixed
public import Theory.SpecificGroups.SymplecticFour.ContainedPlaneGeneration

/-!
# Contained-image selectors with every individual edge fixed clause

Choose the first residual element to lift the opposition element in the
literal marked symplectic quotient. The established additive-plane selector
then supplies the same second element, smaller-mover generation and paired
whole-Z fixed equality. This choice also makes the first full plane radical
opposite the original one, and the second selected plane remains opposite.

The original edge Z centralizes the original smaller mover, hence the
whole original plane core. Opposition now gives the individual edge-Z
fixed equality at both selected edges. NeighborEdgeFixed transfers both
equalities to every neighboring mover at those same choices, without
assuming equality of movers or deleting a central attachment.

ContainedNeighborPaths carries these choices into an actual backward critical
path. Generation here still uses the original smaller mover on U_a;
individual residual generation by an unequal neighbor is a further clause.
Source: MS93 (5.5)(b), (5.6), printed pp.915--918, contained large-image branch.
-/

public noncomputable section
open scoped Pointwise
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
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

private theorem contained_opposite_generators
    {F : Type*} [Field F] [CharP F 2] [Finite F]
    {n : ℕ} (hF : Nat.card F=2^n) (hn : 1<n)
    (J A : Subgroup (Sp F))
    (hJP : J≤((CentralRootGeometry.wing true).map (unipotent (F := F)).subtype))
    (hJc : Nat.card F<Nat.card J)
    (hAP : A≤((CentralRootGeometry.wing true).map (unipotent (F := F)).subtype))
    (hAc : Nat.card F^2≤Nat.card A) :
    let P := (CentralRootGeometry.wing true).map (unipotent (F := F)).subtype
    ∃ g x : Sp F,
      (J.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔ A.map (MulAut.conj x).toMonoidHom=⊤ ∧
      (P.map (MulAut.conj g).toMonoidHom ⊔
        (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom=⊤) ∧
      (P.map (MulAut.conj g).toMonoidHom ⊔ P=⊤) ∧
      x∈normalizer (P : Set (Sp F)) := by
  dsimp only
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨x,hA,hpair,hpos⟩ := ContainedPlane.exists_contained_plane_selector hF hn A hAP hAc
  let o := TwoConjugate.opposition (F := F)
  have hmaps (D : Subgroup (Sp F)) :
      (D.map (MulAut.conj o).toMonoidHom).map (MulAut.conj o).toMonoidHom=D := by
    rw [Subgroup.map_map]
    have he : (MulAut.conj o).toMonoidHom.comp (MulAut.conj o).toMonoidHom=MonoidHom.id _ := by
      apply MonoidHom.ext
      intro y
      have hoo : o*o=1 := by
        dsimp only [o]
        nth_rw 1 [←TwoConjugate.opposition_inv]
        exact inv_mul_cancel _
      change o*(o*y*o⁻¹)*o⁻¹=y
      calc
        _ = (o*o)*y*(o*o)⁻¹ := by group
        _ = y := by rw [hoo]; simp
    rw [he,Subgroup.map_id]
  have hopposite : ((CentralRootGeometry.wing true).map (unipotent (F := F)).subtype).map
      (MulAut.conj o).toMonoidHom ⊔ (CentralRootGeometry.wing true).map unipotent.subtype=⊤ := by
    rw [←SymplecticConjugatePair.planeRadical_eq_wing]
    apply LargePlaneGeneration.opposite_plane_large_subactor_generate _ le_rfl
    rw [SymplecticConjugatePair.card_planeRadical]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  refine ⟨o,x,?_,hpair,hopposite,hpos⟩
  rw [sup_assoc,hA]
  have hh := LargePlaneGeneration.opposite_plane_large_subactor_generate J
    (by rwa [SymplecticConjugatePair.planeRadical_eq_wing]) hJc
  have hh' := congrArg (Subgroup.map (MulAut.conj o).toMonoidHom) hh
  rw [Subgroup.map_sup,hmaps,map_top_of_surjective _ (MulAut.conj o).surjective,
    SymplecticConjugatePair.planeRadical_eq_wing,sup_comm] at hh'
  exact hh'

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The contained-image selector can use an opposite original plane as its
first choice, while retaining smaller-mover generation, the paired full-Z
fixed equality and the same second residual element. -/
theorem Input.replacement_contained_large_opposite_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
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
      (D.map (MulAut.conj g).toMonoidHom ⊔ D = stabilizer d.radical a) ∧
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
  have hcA : Nat.card B.Carrier^2 ≤ Nat.card (A₀.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hzS] at hh
    rw [←hh,hcard]
    exact hlarge
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  obtain ⟨g₀,x₀,hgen₀,hpair₀,hopposite₀,hpos₀⟩ := contained_opposite_generators
    B.card_eq (by rw [hB]; exact h.nonbinary) (J₀.map f) (A₀.map f)
    ((map_le_iff_le_comap).mpr hJplane) (by nlinarith) hcontained hcA
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
  have hopposite : D₀.map (MulAut.conj g).toMonoidHom ⊔ D₀ = ⊤ := by
    apply full_of_full_image f _ (hkD.trans le_sup_right)
    rwa [Subgroup.map_sup,Subgroup.image_conjugate,hmapD,hfg]
  have hopposite' := congrArg (Subgroup.map S.subtype) hopposite
  rw [Subgroup.map_sup,Subgroup.image_conjugate,
    ←MonoidHom.range_eq_map,range_subtype] at hopposite'
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
  refine ⟨g.val,hg,x.val,hx,hgen',hpair',?_,hopposite',hxD,⟨x,hxP,rfl⟩⟩
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


/-- A contained large critical image has a simultaneous smaller-mover selector
whose two selected individual neighboring movers fix exactly the ambient-fixed
subgroup of the whole original edge Z, for every original neighbor. The original
mover, rather than an assumed equal neighbor, supplies both generation identities. -/
theorem Input.replacement_contained_large_neighbor_fixed_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
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
      (D.map (MulAut.conj g).toMonoidHom ⊔ D = stabilizer d.radical a) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ∀ c : Vertex d.radical, Adjacent d.radical c t →
        let t₁ := act d.radical g⁻¹ t
        let c₁ := act d.radical g⁻¹ c
        let t₂ := act d.radical x t₁
        let c₂ := act d.radical x c₁
        (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₁)
          (Q d.radical c₁) (Q d.radical t₁) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
            Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
        (Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical c₂)
          (Q d.radical c₂) (Q d.radical t₂) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
            Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  dsimp only
  obtain ⟨g,hg,x,hx,hgen,hpair,hfixed,hopposite,hxn,hxp⟩ :=
    h.replacement_contained_large_opposite_selection d path hb hat B hB f hf hfQ hindex
      hlarge hcontained hJplane
  let S := stabilizer d.radical a
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D := (P.comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a = a := S.inv_mem hgS
  have hxa : act d.radical x a = a := hxS
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb path.start_color hat
    B hB f hf hfQ hindex hJplane
  have he₁ := conjugate_fixed_eq (Z d.radical a) J D he g
    (Z_normalized d.radical a hgS)
  have he₂ := conjugate_fixed_eq (Z d.radical a) _ _ he₁ x⁻¹
    (Z_normalized d.radical a (S.inv_mem hxS))
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    exact Ne.symm hh
  have htZ := adjacent_Z_le d.radical path.start_color hat
  have htJ : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y ((Subgroup.SmallMover.join_le _ _ _ _) hy)
  have htD : Z d.radical t ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    fun v hv => (he ▸ (show v ∈ Z d.radical a ⊓ centralizer
      (J : Set (FreeAmalgam d.radical)) from ⟨htZ hv,htJ hv⟩)).2
  have hopposite₂ : (D.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom ⊔ D = S := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hopposite
    have hD : D.map (MulAut.conj x⁻¹).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (D : Set (FreeAmalgam d.radical))).inv_mem hxn)
    have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hxS))
    rw [Subgroup.map_sup,hD,hS] at hh
    exact hh
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hy => hy.2 a (adjacent_symm d.radical hat))
  have hJgS : J.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro y ⟨v,hv,rfl⟩
    exact S.mul_mem (S.mul_mem hgS (hJS hv)) (S.inv_mem hgS)
  have hJgxS : (J.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom ≤ S := by
    rintro y ⟨v,hv,rfl⟩
    exact S.mul_mem (S.mul_mem (S.inv_mem hxS) (hJgS hv)) (S.inv_mem (S.inv_mem hxS))
  have fixed_of_opposite (A D' : Subgroup (FreeAmalgam d.radical))
      (hAS : A ≤ S)
      (heA : Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ centralizer (D' : Set (FreeAmalgam d.radical)))
      (hgenA : D' ⊔ D = S) :
      Z d.radical t ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (S : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · intro y hy
      have hyD' := (heA ▸ (show y ∈ Z d.radical a ⊓ centralizer
        (A : Set (FreeAmalgam d.radical)) from ⟨htZ hy.1,hy.2⟩)).2
      refine ⟨hy.1,?_⟩
      have h₁ : D' ≤ centralizer ({y} : Set (FreeAmalgam d.radical)) :=
        fun v hv => mem_centralizer_singleton_iff.mpr (hyD' v hv)
      have h₂ : D ≤ centralizer ({y} : Set (FreeAmalgam d.radical)) :=
        fun v hv => mem_centralizer_singleton_iff.mpr (htD hy.1 v hv)
      intro v hv
      exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hgenA.symm ▸ hv))
    · exact inf_le_inf_left _ (centralizer_le hAS)
  have hfix₁ := fixed_of_opposite _ _ hJgS he₁ hopposite
  have hfix₂ := fixed_of_opposite _ _ hJgxS he₂ hopposite₂
  refine ⟨g,hg,x,hx,hgen,hpair,hfixed,hopposite,hxn,hxp,?_⟩
  intro c hct
  let t₁ := act d.radical g⁻¹ t
  let c₁ := act d.radical g⁻¹ c
  have ha₁ : Adjacent d.radical a t₁ := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hc₁ : Adjacent d.radical c₁ t₁ := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  have ha₂ : Adjacent d.radical a (act d.radical x t₁) := by
    rw [←hxa]
    exact (adjacent_act_iff d.radical x _ _).mpr ha₁
  have hc₂ : Adjacent d.radical (act d.radical x c₁) (act d.radical x t₁) :=
    (adjacent_act_iff d.radical x _ _).mpr hc₁
  have hJa₁ : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t₁) (Nat.card F^2) = J.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.SmallMover.join_map _ (MulAut.conj g).injective]
    have hU := U_act d.radical g⁻¹ a
    have hQ := Q_act d.radical g⁻¹ a
    rw [hga,inv_inv] at hU hQ
    rw [←hU,←hQ]
    simp only [t₁,Q_act,inv_inv]
  have hJa₂ : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (act d.radical x t₁)) (Nat.card F^2) =
      (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [←hJa₁,Subgroup.SmallMover.join_map _ (MulAut.conj x⁻¹).injective]
    have hU := U_act d.radical x a
    have hQ := Q_act d.radical x a
    rw [hxa] at hU hQ
    rw [←hU,←hQ,Q_act]
  refine ⟨h.replacement_neighbor_edge_fixed_of_original d geometry hb path.start_color hat
    ha₁ hc₁ (by rw [hJa₁]; exact hfix₁),
    h.replacement_neighbor_edge_fixed_of_original d geometry hb path.start_color hat
      ha₂ hc₂ (by rw [hJa₂]; exact hfix₂)⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
