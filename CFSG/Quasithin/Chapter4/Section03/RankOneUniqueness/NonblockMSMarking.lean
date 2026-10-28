module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs.FieldTransport
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Simultaneous original parabolic and Sylow markings

A marking of the original L-image as the line parabolic residual determines
its Sylow image up to conjugation inside that same residual. The original
S∩L is Sylow in L: restrict the given ambient Sylow to N_G(L) and then to
its normal subgroup L. Map this Sylow through the literal full SL₃ quotient,
and conjugate it inside the line residual to the upper unipotent subgroup.

Apply that one inner conjugation to the quotient marking and transport both
the natural section U and the doubled dual section Q/U by their respective
representation operators. This preserves the original field, all subgroups,
quotient maps and MS-pair hypotheses. In particular, changing the quotient
marking alone would not suffice; both intertwining equations are proved.

NonblockMSMarkingApplications uses the simultaneous marking to select the
original secondary component and place the orbit of U in its two-core.
Construction of MSData and its line marking, strict secondary-core enlargement,
and the final nonblock contradiction remain with the same source assembly
owner. The independent whole-core nonbinary classification retains
qt-c134-nonbinary-linear-three-source and its final discharge.
Source: Aschbacher--Smith, C.1.34(3), pp.136--137, and the choices after
original 4.3.10, p.617; Sylow conjugacy inside the parabolic residual.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

omit [Finite G] in
private theorem section_conjugate {B A F : Type*} [Group B] [AddCommGroup A]
    [Field F] [Module F A] {J P C : Subgroup G} {a : J →* B}
    {rho : Representation F B A} (hm : HasSectionModel J P C a rho) (g : B) :
    HasSectionModel J P C ((MulAut.conj g).toMonoidHom.comp a) rho := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (rho.asGroupHom g)
  apply hm.transport e.toAddEquiv
  intro x v
  change rho g (rho (a x) v) = rho (g * a x * g⁻¹) (rho g v)
  simp only [← Module.End.mul_apply,← map_mul]
  simp

/-- Change the full quotient marking and both module coordinates together. -/
@[expose] noncomputable def MSData.conjugateModel (d : MSData c n)
    (g : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) : MSData c n :=
  { d with
    model := d.model.trans (MulAut.conj g)
    natural := by exact section_conjugate d.natural g
    doubleDual := by exact section_conjugate d.doubleDual g }

private theorem original_sylow (D : Chapter12.Section02.ChosenModule T L V) :
    ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S c ⊓ L := by
  let N := normalizer (L : Set G)
  let A := L.subgroupOf N
  let e : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype D.sylow_normalizes_component).exists_sylow_map_eq_inf_of_normal A
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((P : Subgroup A).map e.toMonoidHom).map L.subtype = _
  have hf : L.subtype.comp e.toMonoidHom = N.subtype.comp A.subtype := rfl
  rw [map_map,hf,←map_map,hP]
  rw [Subgroup.map_inf _ _ _ N.subtype_injective,map_subgroupOf_eq_of_le L.le_normalizer]
  change ((T : Subgroup G).subgroupOf N).map N.subtype ⊓ L = _
  rw [map_subgroupOf_eq_of_le D.sylow_normalizes_component]
  change (T : Subgroup G) ⊓ L = ((T : Subgroup G) ⊓ c.H) ⊓ L
  rw [inf_assoc,inf_eq_right.mpr (c.le_component.trans (map_subtype_le _))]

private theorem unipotent_le_line (F : Type*) [Field F] :
    unipotentSL F ≤ lineLocalSL F := inf_le_right

private theorem line_image_sylow (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    ∃ P : Sylow 2 (lineLocalSL d.field.Carrier),
      (P : Subgroup (lineLocalSL d.field.Carrier)).map (lineLocalSL d.field.Carrier).subtype =
        ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) := by
  let f := (linearThreeActor d.model).comp (inclusion c.le_component)
  have hfr : f.range = lineLocalSL d.field.Carrier := by
    rw [MonoidHom.range_comp]
    have hi : (inclusion c.le_component).range = L.subgroupOf (K c) := by
      ext x
      constructor
      · rintro ⟨y,rfl⟩; exact y.property
      · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
    rw [hi,hL]
  let f' : L →* lineLocalSL d.field.Carrier := f.codRestrict _ (fun x => hfr.le ⟨x,rfl⟩)
  have hs : Function.Surjective f' := by
    intro y
    obtain ⟨x,hx⟩ := hfr.ge y.property
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨P,hP⟩ := original_sylow (c := c) D
  refine ⟨P.mapSurjective (f := f') hs,?_⟩
  change ((P : Subgroup L).map f').map (lineLocalSL d.field.Carrier).subtype = _
  rw [map_map]
  change (P : Subgroup L).map f = _
  rw [←map_map]
  congr 1
  apply map_injective (K c).subtype_injective
  rw [map_map,map_subgroupOf_eq_of_le (inf_le_right.trans c.le_component)]
  exact hP

/-- Align the original Sylow and line images by one inner change of marking. -/
theorem MSData.exists_simultaneous_marking (d : MSData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier) :
    ∃ g : lineLocalSL d.field.Carrier,
      let d' := d.conjugateModel g.val
      (L.subgroupOf (K c)).map (linearThreeActor d'.model) = lineLocalSL d'.field.Carrier ∧
      ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d'.model) = unipotentSL d'.field.Carrier := by
  obtain ⟨P,hP⟩ := line_image_sylow d D hL
  let P₀ := (Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow d.field.Carrier
    (show 0 < d.field.degree by rw [d.degree_eq]; have := d.pair.positive; omega)
    d.field.card_eq).subtype (unipotent_le_line d.field.Carrier)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (lineLocalSL d.field.Carrier) P P₀
  have hh := congrArg (fun Q : Sylow 2 (lineLocalSL d.field.Carrier) =>
    (Q : Subgroup (lineLocalSL d.field.Carrier)).map (lineLocalSL d.field.Carrier).subtype) hg
  have he : (((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model)).map
      (MulAut.conj g.val).toMonoidHom = unipotentSL d.field.Carrier := by
    change ((P : Subgroup (lineLocalSL d.field.Carrier)).map
      (MulAut.conj g).toMonoidHom).map (lineLocalSL d.field.Carrier).subtype = _ at hh
    have hf : (lineLocalSL d.field.Carrier).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g.val).toMonoidHom.comp (lineLocalSL d.field.Carrier).subtype := rfl
    rw [map_map,hf,←map_map,hP] at hh
    change _ = ((unipotentSL d.field.Carrier).subgroupOf (lineLocalSL d.field.Carrier)).map
      (lineLocalSL d.field.Carrier).subtype at hh
    rwa [map_subgroupOf_eq_of_le (unipotent_le_line d.field.Carrier)] at hh
  refine ⟨g,?_,?_⟩
  · change (L.subgroupOf (K c)).map
      ((MulAut.conj g.val).toMonoidHom.comp (linearThreeActor d.model)) = _
    rw [←map_map,hL]
    exact mem_normalizer_iff_map_conj_eq.mp ((lineLocalSL d.field.Carrier).le_normalizer g.property)
  · change ((S c ⊓ L).subgroupOf (K c)).map
      ((MulAut.conj g.val).toMonoidHom.comp (linearThreeActor d.model)) = _
    rwa [←map_map]

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
