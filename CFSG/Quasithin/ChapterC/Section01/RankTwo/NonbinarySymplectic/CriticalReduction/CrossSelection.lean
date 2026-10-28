module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NormalizedCoordinates
public import Theory.SpecificGroups.SymplecticFour.CrossMoverGeneration
/-!
# Root generation by the join of unequal neighboring movers

Keep one natural-index marking in which the full Sylow normalizes the
replacement edge. Its normalizer also preserves the original small-mover
join. When that join has small fixed index, its image is a normal plane
subgroup of order at least q squared. Unequal neighboring movers together
move more than q squared cosets, so their join escapes that plane. The
arbitrary-degree cross-mover calculation supplies a single root generator.
The large-fixed-index branch uses the already proved point-radical selector.

The conjugator lifts inside the original residual. The join contains the
whole Q-kernel, so generation lifts to the entire vertex stabilizer. The
neighboring mover alone is not asserted to contain this kernel or generate.
CrossSelectedPaths applies this result to the literal graph and full edge Z.

Source: MS93 (5.5)(a), printed pp.915--917, field-sized critical-image
branch. The separate individual-mover fixed-layer and generation clauses
(b,c), the proper-J large-image branch and the distance exclusions remain.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
private theorem quadratic_of_displacement_line {F : Type*} [Field F]
    (A : Subgroup (Sp F)) (hd : Module.finrank F (displacementSpace A) = 1) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v := by
  have hn : displacementSpace A ≠ ⊥ := by
    intro hh
    rw [hh,finrank_bot] at hd
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  have hperp : displacementSpace A ≤ (form F).orthogonal (displacementSpace A) := by
    intro x hx y hy
    rw [hs] at hx hy
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨e,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [TwoLocalCover.form_alternating.self_eq_zero]
  rw [orthogonal_displacementSpace] at hperp
  intro x hx y hy w
  exact hperp (Coinvariants.sub_mem_ker
    (ρ := (symplecticNatural 2).comp A.subtype) ⟨y,hy⟩ w) x hx

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
/-- Coordinates preserving normalization by the whole standard Sylow. -/
theorem Input.replacement_normalized_natural_indices
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ E : BinaryField, E.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp E.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        unipotent ≤ normalizer
          (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp E.Carrier)) ∧
        ∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := E.Carrier) 2)) (A.map f) := by
  obtain ⟨E,hE,f,hf,hfQ,hidx⟩ := h.replacement_inner_natural_indices d geometry hb ha
  let := finite_stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf (stabilizer d.radical a)
  obtain ⟨P,hTP,hPn⟩ := h.replacement_edge_normalizing_sylow d ha hat
  let S := P.mapSurjective (f := f) hf
  have hS : T.map f ≤ (S : Subgroup _) := map_mono hTP
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow (by rw [E.card_eq]) (by rw [hE]; exact h.nonbinary.le))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj g).toMonoidHom = unipotent :=
    congrArg (fun S : Sylow 2 (Sp E.Carrier) => (S : Subgroup (Sp E.Carrier))) hg
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hTf : T.map f' ≤ unipotent := by
    rw [←Subgroup.map_map]
    exact (map_mono hS).trans_eq hSm
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x) = 1 ↔ f x = 1
    exact (MulAut.conj g).map_eq_one_iff
  refine ⟨E,hE,f',(MulAut.conj g).surjective.comp hf,by rw [hker]; exact hfQ,hTf,?_,?_⟩
  · have hh := (map_mono (f := f) hPn).trans (le_normalizer_map f)
    have hh' := (map_mono (f := (MulAut.conj g).toMonoidHom) hh).trans
      (le_normalizer_map (MulAut.conj g).toMonoidHom)
    change ((S : Subgroup _).map (MulAut.conj g).toMonoidHom) ≤ _ at hh'
    rw [hSm,Subgroup.map_map] at hh'
    exact hh'
  · intro A
    rw [←Subgroup.map_map, fixedCodim_map_conj]
    exact hidx A

/-- In the unequal-neighbor root case, the join of the two original
movers has a residual conjugate generating with the critical endpoint.
This does not identify either mover alone as a generating subgroup. -/
theorem Input.replacement_unequal_join_root_generator
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    let Jc := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a,
      (J ⊔ Jc).map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a := by
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
  by_cases hJm : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2
  swap
  · obtain ⟨g,hg,hall⟩ := h.replacement_large_movement_root_generator d path hb hat hsmall
      (lt_of_not_ge hJm)
    have hgen := hall c hct
    refine ⟨g,hg,le_antisymm ?_ ?_⟩
    · refine sup_le ?_ hzS
      rintro y ⟨v,hv,rfl⟩
      have hgS := Ltilde_le_stabilizer a hg
      exact S.mul_mem (S.mul_mem hgS (hES hv)) (S.inv_mem hgS)
    · exact hgen.ge.trans (sup_le_sup_right (map_mono (show Jc ≤ E from le_sup_right)) _)
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
  obtain ⟨r,hr⟩ := FourLongRoots.exists_conjugate_root_of_displacement_one (A₀.map f) hcA hdA
    (quadratic_of_displacement_line (A₀.map f) hdA)
  obtain ⟨g₀,hgen₀⟩ := CrossMoverGeneration.exists_cross_mover_root_generator hq
    J₁ E₁ hJcard hJmove (comap_mono (map_mono (comap_mono le_sup_left))) hout (A₀.map f) ⟨r,hr⟩
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
  exact ⟨g.val,hg,hwhole⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
