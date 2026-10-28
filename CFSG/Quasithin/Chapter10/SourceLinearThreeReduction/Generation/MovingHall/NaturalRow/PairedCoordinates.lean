module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.PairedSource
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.ModuleKernel
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.PairedCoordinates

/-!
# Original paired coordinates and the central-alpha seed decomposition

The selected original linear pair constructs a surjective coordinate map
on the original local module, with precisely its orbit-fixed kernel.
The prescribed Sylow exchanger acts by a linear equivalence between the
two coordinates. The actor maps have a two-group joint kernel, proved
from the actual module centralizer. E.2.3 supplies the seed bound including
its central-alpha supplement, before either fixed center has vanished.

The final application discharges all these inputs from the original
non-A₅ context and its actual even-field component quotient. This adapts
the general calculations in `SourceSections/PairedCoordinates` and
`SourceSections/PairedSource` without a field-four hypothesis.
Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217,746.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

@[expose] def OriginalPairedCoordinates : Prop :=
    ∃ F : BinaryField,
      letI : Algebra (ZMod 2) F.Carrier := ZMod.algebra _ 2
      ∃ (q₁ q₂ : localOrbit T L →* SL(2,F.Carrier))
        (c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
          (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
          (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
        (_htwo : IsPGroup 2 (q₁.ker ⊓ q₂.ker : Subgroup (localOrbit T L)))
        (t : T) (f : (Fin 2 → F.Carrier) ≃ₗ[ZMod 2] (Fin 2 → F.Carrier)),
          ∀ a : D.moduleSubgroup,
            ((c.coordinates ⟨(t:G)*a*(t:G)⁻¹,
              (mem_normalizer_iff.mp (D.sylow_normalizes_module t.property) a).mp a.property⟩).toAdd).1 =
                f (c.coordinates a).toAdd.2

set_option backward.isDefEq.respectTransparency false in
theorem source_original_paired_coordinates_of_natural_source
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤)
    (hC : IsPGroup 2 (centralizer
      (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L))))
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hpair : SourceOriginalPairedLinear D) :
    OriginalPairedCoordinates D := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set X) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨d,F,⟨c⟩,hexchange⟩ := hpair
  rcases F with @⟨K, iField, iFinite, iChar, iAlgebra, degree, hpos, hcard⟩
  have hAlg : iAlgebra = ZMod.algebra K 2 := Subsingleton.elim _ _
  subst iAlgebra
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let F : BinaryField := @BinaryField.mk K iField iFinite iChar (ZMod.algebra K 2) degree hpos hcard
  let V := Fin 2 → F.Carrier
  have hcore : pCore 2 (X ⧸ C) = ⊥ := hU.quotient_pCore_eq_bot
  have hne : q.ker ≠ ⊤ := by
    intro he
    apply hJ
    rw [←hk,he]
    exact le_top
  have hp := (minimalParabolic_reduced_image S hP q hq hcore hne).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hf,_,_,_⟩ := lemma_B_2_7 U q hq hk S
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top S).trans hf.1)).elim
    · exact hf
  have hc : c.quotientMap.ker = fixedSpace α ((pResidual 2 X).map q) := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact source_offender_pair_linear_kernel α (S.mapSurjective hq) hp hff hcore F c
  have hJY : (elementaryAbelianMaxJ (S : Subgroup X)).map q ≤ Y :=
    RankOneBaumann.thompson_image_le_offender_layer S U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S)) Y le_rfl
  have hRY := RankOneBaumann.residual_image_le_normal_thompson_layer S hP U hU hJ q hq hk Y hJY
  let R := localOrbit T L
  have hRX : R ≤ X := le_sup_left
  have hUX : D.moduleSubgroup ≤ X := D.module_le_core.trans (pCoreIn_le 2 X)
  have hrx : pResidual 2 X = R.subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [source_join_residual D,map_subgroupOf_eq_of_le hRX]
  let k : R →* Y := (q.comp (inclusion hRX)).codRestrict Y (by
    intro a
    apply hRY
    apply mem_map_of_mem
    rw [hrx]
    exact a.property)
  let q₁ : R →* SL(2,F.Carrier) := (MonoidHom.fst _ _).comp (c.action.groupEquiv.toMonoidHom.comp k)
  let q₂ : R →* SL(2,F.Carrier) := (MonoidHom.snd _ _).comp (c.action.groupEquiv.toMonoidHom.comp k)
  let ue : U ≃* D.moduleSubgroup := subgroupOfEquivOfLe hUX
  let m : D.moduleSubgroup →* Multiplicative (V × V) := {
    toFun a := Multiplicative.ofAdd (c.quotientMap (Additive.ofMul (ue.symm a)))
    map_one' := by rw [map_one]; exact c.quotientMap.map_zero
    map_mul' := by
      intro a b
      rw [map_mul]
      exact c.quotientMap.map_add _ _ }
  have honto : Function.Surjective m := by
    intro v
    obtain ⟨a,ha⟩ := c.quotientMap_surjective v.toAdd
    refine ⟨ue a.toMul,?_⟩
    change Multiplicative.ofAdd (c.quotientMap (Additive.ofMul (ue.symm (ue a.toMul)))) = v
    rw [ue.symm_apply_apply]
    exact ha
  have hconj (g : X) (a : D.moduleSubgroup) :
      α (q g) (Additive.ofMul (ue.symm a)) =
        Additive.ofMul (ue.symm ⟨(g:G)*a*(g:G)⁻¹,
          (mem_normalizer_iff.mp (D.join_normalizes_module g.property) a).mp a.property⟩) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply U q hq hk g (ue.symm a)
  let n : BinaryConjugationSection R D.moduleSubgroup
      (D.moduleSubgroup ⊓ centralizer (R : Set G))
      (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)) := {
    section_le := D.module_le_orbit
    kernel_le := inf_le_left
    normalized := D.orbit_normalizes_module
    coordinates := m
    onto := honto
    kernel_eq := by
      ext a
      change c.quotientMap (Additive.ofMul (ue.symm a)) = 0 ↔
        (a:G) ∈ D.moduleSubgroup ⊓ centralizer (R : Set G)
      change (Additive.ofMul (ue.symm a)) ∈ c.quotientMap.ker ↔ _
      rw [hc,NormalElementaryQuotient.mem_fixedSpace_image]
      constructor
      · intro hz
        refine ⟨a.property,?_⟩
        intro z hzR
        have hzR' : z ∈ (pResidual 2 X).map X.subtype := by
          rw [source_join_residual D]
          exact hzR
        obtain ⟨b,hb,rfl⟩ := hzR'
        exact congrArg X.subtype (hz b hb)
      · rintro ⟨_,hz⟩ b hb
        apply Subtype.ext
        apply hz b
        change (b:G) ∈ localOrbit T L
        rw [←source_join_residual D]
        exact mem_map_of_mem X.subtype hb
    equivariant := by
      intro r a
      have hh := c.quotientMap_action (k r) (Additive.ofMul (ue.symm a))
      change c.quotientMap (α (q (inclusion hRX r)) _) = _ at hh
      rw [hconj] at hh
      exact hh }
  obtain ⟨ρ,hρ,hnat,he,_,_⟩ := source_images_and_fixedSpace S hP U hU hJ q hq hk d F c hexchange
  obtain ⟨t,ht₁,ht₂⟩ := hexchange
  obtain ⟨g,hg,hgt⟩ := t.property
  obtain ⟨f,hf⟩ := SL2NaturalOffenders.exchanged_pair_coordinate_equiv Y c.action.groupEquiv ρ
    (fun a v => hnat a v) (t:X ⧸ C)
    (by rw [c.first_eq,c.second_eq]; exact ht₁)
    (by rw [c.second_eq,c.first_eq]; exact ht₂)
  have htwo : IsPGroup 2 (q₁.ker ⊓ q₂.ker : Subgroup R) := by
    apply (hC.comap_of_injective (inclusion hRX) (inclusion_injective hRX)).to_le
    intro r hr
    have hh : c.action.groupEquiv (k r) = 1 := Prod.ext hr.1 hr.2
    have hk1 : k r = 1 := c.action.groupEquiv.map_eq_one_iff.mp hh
    have hq1 : q (inclusion hRX r) = 1 := congrArg Subtype.val hk1
    exact (QuotientGroup.eq_one_iff (N := C) (inclusion hRX r)).mp hq1
  refine ⟨F,q₁,q₂,n,htwo,⟨(g:G),hg⟩,f,?_⟩
  intro a
  have hh := he (q g) (Additive.ofMul (ue.symm a))
  rw [hconj,hgt] at hh
  exact (congrArg Prod.fst hh).trans (hf _)

set_option backward.isDefEq.respectTransparency false in
theorem source_original_seed_split_of_natural_source
    (hP : IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)) ⊤) :
    let X := localJoin T L
    let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
    let U := D.moduleSubgroup.subgroupOf X
    letI := (source_parabolic_module_reduced D).normal
    letI := (source_parabolic_module_reduced D).elementary
    let C := centralizer (U : Set X)
    let q := QuotientGroup.mk' C
    let hq := QuotientGroup.mk'_surjective C
    let hk := QuotientGroup.ker_mk' C
    let α := NormalElementaryQuotient.representation U q hq hk
    let Y := offenderSubgroup α
    letI := offenderSubgroup_normal α
    ∀ (_hJ : ¬ elementaryAbelianMaxJ (S : Subgroup X) ≤ centralizer (U : Set X))
      (d : SourceTwoFactorCase (α.comp Y.subtype)) (F : BinaryField)
      (_c : d.MarkedProduct (linearNatural F 2))
      (_hexchange : ∃ t : S.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:X ⧸ C)).toMonoidHom = d.first),
      omegaOneCenterAmbient (T : Subgroup G) ≤
        ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
          (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU : IsPReduced 2 U := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = C := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  let := offenderSubgroup_normal α
  dsimp only
  intro hJ d F c hexchange
  have hspan := paired_orbit_span_of_source_model S hP
    U hU hJ q hq hk d F c hexchange
  have hplace : omegaOneCenterAmbient (S : Subgroup X) ≤
      ⁅U,pResidual 2 X⁆ ⊔ (thompsonAlpha (S : Subgroup X) ⊓ centralizer (pResidual 2 X : Set X)) :=
    (omegaCenter_le_omegaCenter_maxJ (S : Subgroup X)).trans
      ((le_conjugateSpanBy _ _).trans_eq hspan)
  have hS : (S : Subgroup X).map X.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hZ : (omegaOneCenterAmbient (S : Subgroup X)).map X.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,hS]
  have hα : (thompsonAlpha (S : Subgroup X)).map X.subtype = thompsonAlpha (T : Subgroup G) := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,hS]
  have hm := map_mono (f := X.subtype) hplace
  rw [hZ,Subgroup.map_sup,map_commutator,
    map_subgroupOf_eq_of_le (D.module_le_core.trans (pCoreIn_le 2 X)),source_join_residual D] at hm
  apply hm.trans
  apply sup_le le_sup_left
  apply le_trans ?_ le_sup_right
  rintro z ⟨w,hw,rfl⟩
  refine ⟨hα ▸ mem_map_of_mem X.subtype hw.1,?_⟩
  intro l hl
  obtain ⟨a,ha,rfl⟩ := (source_join_residual D).symm ▸ hl
  exact congrArg X.subtype (hw.2 a ha)

/-- Construct the literal paired module, exchanger and seed decomposition
from the original moving context and its even-field component quotient. -/
theorem Context.original_paired_coordinates_and_seed
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    OriginalPairedCoordinates D ∧
      omegaOneCenterAmbient (T : Subgroup G) ≤
        ⁅D.moduleSubgroup,localOrbit T L⁆ ⊔
          (thompsonAlpha (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)) := by
  have hP := source_natural_minimal_parabolic D e n hn hF ctx.nonnormal
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  have hC := source_natural_module_centralizer_isTwoGroup D n hn hF e ctx.nonnormal hJ
  have hpair := ctx.original_paired_linear D n hn hF e
  refine ⟨source_original_paired_coordinates_of_natural_source D hP hC hJ hpair,?_⟩
  obtain ⟨d,E,⟨c⟩,hexchange⟩ := hpair
  exact source_original_seed_split_of_natural_source D hP hJ d E c hexchange

/-- The paired natural source makes the literal original Baumann subgroup
Sylow in its join with L₀, as required by 10.2.2(3). -/
theorem Context.original_baumann_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (localOrbit T L ⊔ baumann (T : Subgroup G)) := by
  let X := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf X
  have hU := source_parabolic_module_reduced D
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set X)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  have hP := source_natural_minimal_parabolic D e n hn hF ctx.nonnormal
  have hJ := source_hstar_local_thompson_moves_of_omega_commutator D ctx.hstar ctx.moving
  obtain ⟨d,E,⟨c⟩,hexchange⟩ := ctx.original_paired_linear D n hn hF e
  have hs := (source_global_baumann_and_alpha S hP U hU hJ q hq hk d E c hexchange).1
  have hbmap : (baumann (S : Subgroup X)).map X.subtype = baumann (T : Subgroup G) := by
    have he := baumann_map_injective X.subtype X.subtype_injective (S : Subgroup X)
    change (baumann (S : Subgroup X)).map X.subtype = baumann ((S : Subgroup X).map X.subtype) at he
    exact he.trans (congrArg baumann (map_subgroupOf_eq_of_le le_sup_right))
  have hm := (Chapter1.IsSylowIn.map_iff X.subtype X.subtype_injective).mpr hs
  rw [Subgroup.map_sup,hbmap,source_join_residual D] at hm
  exact hm

/-- The original general-field moving branch satisfies the actual 10.2.1
Baumann-normalizer containment, with no block or normalizer callback. -/
theorem Context.original_baumann_normalizer_le
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hP := source_natural_minimal_parabolic D e n hn hF ctx.nonnormal
  have hu := hasUniqueMaximalOver_map_subtype
    ((isMinimalParabolicOver_iff _ ⊤).mp hP).1
  have he : (((T : Subgroup G).subgroupOf (localJoin T L)).map (localJoin T L).subtype) =
      (T : Subgroup G) := map_subgroupOf_eq_of_le le_sup_right
  have hu' : Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L) := he ▸ hu
  exact source_baumann_normalizer_le_of_orbit_sylow D hu'
    (ctx.original_baumann_sylow D n hn hF e)

end CFSG.Quasithin.Chapter10.MovingHall
