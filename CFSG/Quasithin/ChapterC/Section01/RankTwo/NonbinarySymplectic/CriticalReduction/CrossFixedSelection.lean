module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalBranches
public import Theory.SpecificGroups.SymplecticFour.CrossMoverFixedGeneration

/-!
# Individual fixedness for the unequal-mover root selector

The original mover is the unique small maximum in the unequal-neighbor
case. Use the same full-Sylow normalization and critical-root marking as
cross-join generation, but align the root within the original plane.
The selected plane and the original plane then generate through the full
Q-kernel. The established whole-Z equality for J and its plane lifts this
to ambient fixedness for J alone on the original edge Z.

CrossFixedPaths applies this same selector to the literal neighboring
vertices and backward critical path. All original field degrees and central
attachments are retained. Source: MS93 (5.5)(a,b), printed pp.915--917,
field-sized critical-image branch. This does not prove individual generation
or discard the nonsplitting exception in (c).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
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
/-- The same residual root selector gives cross-join generation and the
ambient fixed subgroup on the whole original edge Z for the original
individual mover. No complement to the fixed layer is assumed. -/
theorem Input.replacement_unequal_root_individual_fixed_selector
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a,
      (J ⊔ Jc).map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let E := J ⊔ Jc
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hJT : J ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hET : E ≤ Q d.radical t := sup_le hJT (Subgroup.SmallMover.join_le _ _ _ _)
  have hJS : J ≤ S := hJT.trans hTS
  have hES : E ≤ S := hET.trans hTS
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hJm : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2 :=
    (h.replacement_unequal_original_quadratic d geometry hb path.start_color hat hct hne).1.le
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex⟩ :=
    h.replacement_normalized_natural_indices d geometry hb path.start_color hat
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J₀ := J.subgroupOf S
  let E₀ := E.subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let L₀ := (Ltilde d.radical a).subgroupOf S
  let J₁ := (J₀.map f).subgroupOf unipotent
  let E₁ := (E₀.map f).subgroupOf unipotent
  let := finite_stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hJf : J₀.map f ≤ unipotent := (map_mono (comap_mono hJT)).trans hTf
  have hEf : E₀.map f ≤ unipotent := (map_mono (comap_mono hET)).trans hTf
  have hJ₁ : J₁.map unipotent.subtype = J₀.map f := map_subgroupOf_eq_of_le hJf
  have hE₁ : E₁.map unipotent.subtype = E₀.map f := map_subgroupOf_eq_of_le hEf
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hjoin : Subgroup.SmallMover.join U₀ f.ker T (Nat.card F^2) = J₀ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,
      map_subgroupOf_eq_of_le hJS]
  let : U₀.Normal := (normal_subgroupOf_iff_le_normalizer hUS).mpr (U_normalized a)
  have hJn : unipotent ≤ normalizer (J₀.map f : Set (Sp B.Carrier)) := by
    rw [←hjoin]
    exact hTn.trans (Subgroup.SmallMover.normalizer_image_le_normalizer_join_image
      U₀ T f hf hkT (Nat.card F^2))
  let : J₁.Normal := (normal_subgroupOf_iff_le_normalizer hJf).mpr hJn
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hJcard : Nat.card B.Carrier^2 ≤ Nat.card J₁ := by
    rw [←card_map_of_injective unipotent.subtype_injective,hJ₁,←relIndex_ker]
    have he := relIndex_map_map_of_injective f.ker J₀ S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hJS] at he
    rw [←he,hBF]
    exact h.replacement_small_mover_join_index d geometry hb path.start_color hat
  have index (D : Subgroup (FreeAmalgam d.radical)) (hDT : D ≤ Q d.radical t) :
      movingIndex (((D.subgroupOf S).map f).subgroupOf unipotent) =
        (centralizer (D : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [←binary_movingIndex]
    change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype)
        (((D.subgroupOf S).map f).subgroupOf unipotent) = _
    have hm : (((D.subgroupOf S).map f).subgroupOf unipotent).map unipotent.subtype =
        (D.subgroupOf S).map f := map_subgroupOf_eq_of_le ((map_mono (comap_mono hDT)).trans hTf)
    rw [fixedCodim,fixedSpace_comp_map,hm]
    have he := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
      U₀ (D.subgroupOf S)
    rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le (hDT.trans hTS),hindex] at he
    exact he.symm
  have hJmove : movingIndex J₁ ≤ Nat.card B.Carrier^2 := by
    rw [index J hJT,hBF]
    exact hJm
  have hout : ¬ E₁ ≤ CentralRootGeometry.wing true := by
    intro he
    have hm := movingIndex_le_field_sq_of_le_wing E₁ he
    rw [index E hET,hBF] at hm
    exact (h.replacement_unequal_mover_fixed_index d geometry hb path.start_color hat hct hne).not_ge hm
  obtain ⟨hcA,hdA⟩ := h.replacement_small_critical_image_dimensions d path hb hsmall B hB f hfQ hindex
  let P := (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
  let D₀ := P.comap f
  let D := D₀.map S.subtype
  have hJplane : J₀ ≤ D₀ := by
    apply (map_le_iff_le_comap).mp
    rw [←hJ₁]
    exact map_mono (CrossMoverGeneration.normal_small_le_plane J₁ hJmove)
  have hAP : A₀.map f ≤ P := by
    apply (map_le_iff_le_comap).mpr
    have hzD := h.replacement_endpoint_le_parabolic_core d path hb hfirst hsmall B hB f hTf hindex
    intro y hy
    obtain ⟨v,hv,hvy⟩ := hzD hy
    have he : v=y := Subtype.ext hvy
    exact he ▸ hv
  obtain ⟨g₀,hgen₀,hpair₀⟩ := CrossMoverGeneration.exists_cross_mover_plane_root_selector hq
    J₁ E₁ hJcard hJmove (comap_mono (map_mono (comap_mono le_sup_left))) hout
    (A₀.map f) hAP hcA hdA
  rw [hE₁] at hgen₀
  have hL : L₀.map f=⊤ := by
    have he : L₀=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two hq
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show g₀ ∈ L₀.map f by rw [hL]; trivial)
  have hkJ : f.ker ≤ J₀ := by
    rw [←hjoin]
    apply Subgroup.SmallMover.kernel_le_join U₀ f.ker T (Nat.card F^2)
      (Nat.one_le_pow _ _ Nat.card_pos) hkT
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color))
      (U_le_Z a hu) k.val hkQ
  have hkE : f.ker ≤ E₀ := hkJ.trans (comap_mono le_sup_left)
  have hkg : f.ker ≤ E₀.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hkE
    simpa only [MulEquiv.toMonoidHom_eq_coe,Subgroup.Normal.map_conj_eq] using hh
  have hgen : E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀ = ⊤ := by
    have hm : (E₀.map (MulAut.conj g).toMonoidHom ⊔ A₀).map f = ⊤ := by
      rwa [Subgroup.map_sup,Subgroup.image_conjugate,hfg]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkg.trans le_sup_left),comap_top] at hh
  have hwhole := congrArg (Subgroup.map S.subtype) hgen
  rw [Subgroup.map_sup,Subgroup.image_conjugate,map_subgroupOf_eq_of_le hES,
    map_subgroupOf_eq_of_le hzS,←MonoidHom.range_eq_map,range_subtype] at hwhole
  have hkD : f.ker ≤ D₀ := by
    intro y hy
    change f y ∈ P
    rw [MonoidHom.mem_ker.mp hy]
    exact P.one_mem
  have hpair : D₀.map (MulAut.conj g).toMonoidHom ⊔ D₀ = ⊤ := by
    have hm : (D₀.map (MulAut.conj g).toMonoidHom ⊔ D₀).map f = ⊤ := by
      rwa [Subgroup.map_sup,Subgroup.image_conjugate,map_comap_eq_self_of_surjective hf,
        hfg]
    have hh := congrArg (Subgroup.comap f) hm
    rwa [comap_map_eq_self (hkD.trans le_sup_right),comap_top] at hh
  have hpair' := congrArg (Subgroup.map S.subtype) hpair
  rw [Subgroup.map_sup,Subgroup.image_conjugate,←MonoidHom.range_eq_map,range_subtype] at hpair'
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb path.start_color hat
    B hB f hf hfQ hindex hJplane
  have heg := conjugate_fixed_eq (Z d.radical a) J D he g.val
    (Z_normalized d.radical a g.property)
  have ht : color d.radical t ≠ false := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    exact Ne.symm hh
  have htZ := adjacent_Z_le d.radical path.start_color hat
  have htJ : Z d.radical t ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    rw [Z,if_neg ht] at hv
    exact (mem_omegaCenter_iff.mp hv).2.2 y (hJT hy)
  have hJgS : J.map (MulAut.conj g.val).toMonoidHom ≤ S := by
    rintro y ⟨v,hv,rfl⟩
    exact S.mul_mem (S.mul_mem g.property (hJS hv)) (S.inv_mem g.property)
  refine ⟨g.val,hg,hwhole,le_antisymm ?_ (inf_le_inf_left _ (centralizer_le hJgS))⟩
  intro y hy
  have hyD : y ∈ centralizer (D : Set (FreeAmalgam d.radical)) :=
    (show y ∈ Z d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical)) from
      he ▸ ⟨htZ hy.1,htJ hy.1⟩).2
  have hyDg : y ∈ centralizer (D.map (MulAut.conj g.val).toMonoidHom : Set (FreeAmalgam d.radical)) :=
    (show y ∈ Z d.radical a ⊓ centralizer (D.map (MulAut.conj g.val).toMonoidHom : Set (FreeAmalgam d.radical)) from
      heg ▸ ⟨htZ hy.1,hy.2⟩).2
  refine ⟨hy.1,?_⟩
  have h₁ : D.map (MulAut.conj g.val).toMonoidHom ≤ centralizer ({y} : Set (FreeAmalgam d.radical)) :=
    fun v hv => mem_centralizer_singleton_iff.mpr (hyDg v hv)
  have h₂ : D ≤ centralizer ({y} : Set (FreeAmalgam d.radical)) :=
    fun v hv => mem_centralizer_singleton_iff.mpr (hyD v hv)
  intro v hv
  exact mem_centralizer_singleton_iff.mp ((sup_le h₁ h₂) (hpair'.symm ▸ hv))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
