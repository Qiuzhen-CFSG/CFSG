module
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.OriginalConsequences
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.SourceGeometry
public import Theory.Representation.SL2NaturalOffenders.CoordinateSwap
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SourceSections.FixedCenterSplit
/-!
# Paired coordinates on the original local module

The selected paired marker gives the actual coordinate map on the original
module and its exact orbit-centralizer kernel. Its two actor maps use the
original centralizer quotient. Descending the whole action and retaining
the prescribed Sylow exchanger gives the coordinate equivalence required
by the cubic fixed-center argument. The final consumer retains the central
alpha summand in the seed bound, so no vanishing fixed-center premise is used.

Source: Aschbacher–Smith E.2.3 and 10.2.3(4), pp.216–217 and 746.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
@[expose] def SourceOriginalPairedCoordinates : Prop :=
    ∃ F : BinaryField,
      letI : Algebra (ZMod 2) F.Carrier := ZMod.algebra _ 2
      ∃ (q₁ q₂ : localOrbit T L →* SL(2,F.Carrier))
        (c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
          (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
          (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂)))
        (t : T) (f : (Fin 2 → F.Carrier) ≃ₗ[ZMod 2] (Fin 2 → F.Carrier)),
          ∀ a : D.moduleSubgroup,
            ((c.coordinates ⟨(t:G)*a*(t:G)⁻¹,
              (mem_normalizer_iff.mp (D.sylow_normalizes_module t.property) a).mp a.property⟩).toAdd).1 =
                f (c.coordinates a).toAdd.2

set_option backward.isDefEq.respectTransparency false in
theorem source_original_paired_coordinates_of_selected_source
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from
      le_sup_right)) : Subgroup (localJoin T L)) ≤
      centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)))
    (hpair : SourceOriginalPairedLinear D) :
    SourceOriginalPairedCoordinates D := by
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
  have hP := source_a5_minimal_parabolic D e hn
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
  refine ⟨F,q₁,q₂,n,⟨(g:G),hg⟩,f,?_⟩
  intro a
  have hh := he (q g) (Additive.ofMul (ue.symm a))
  rw [hconj,hgt] at hh
  exact (congrArg Prod.fst hh).trans (hf _)

variable {H : Subgroup G} {K : Type*} [Field K] [CharP K 2]
local instance pairedCoordinatesInputFieldAlgebra : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G),H⁆ ≠ ⊥)
    (hK : Nat.card K = 4)
    (fK : alternatingGroup (Fin 5) ≃* SL(2,K))
    (nK : BinaryConjugationSection L ⁅D.fullModule,L⁆ (sourceMovedFixed D)
      (SL2.BinarySmall.natural.comp
        (fK.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))))
include e hn hH hZH hK fK nK

/-- The actual original selected source supplies the paired section and its
coordinate exchanger from the original full natural marking. -/
theorem source_original_paired_coordinates_of_hstar_natural_four :
    SourceOriginalPairedCoordinates D :=
  source_original_paired_coordinates_of_selected_source D e hn
    (source_hstar_local_thompson_moves_of_omega_commutator D hH hZH)
    (source_original_paired_linear_of_hstar_natural_four D e hn hH hZH hK fK nK)

/-- The same coordinates give the original cubic fixed-center equality;
the retained central-alpha seed summand is discharged by E.2.3. -/
theorem source_original_paired_cubic_fixed_of_hstar_natural_four :
    ∃ F : BinaryField,
      letI : Algebra (ZMod 2) F.Carrier := ZMod.algebra _ 2
      ∃ (q₁ q₂ : localOrbit T L →* SL(2,F.Carrier))
        (_c : BinaryConjugationSection (localOrbit T L) D.moduleSubgroup
          (D.moduleSubgroup ⊓ centralizer (localOrbit T L : Set G))
          (Representation.prod (SL2.BinarySmall.natural.comp q₁) (SL2.BinarySmall.natural.comp q₂))),
        ∀ b : localOrbit T L, orderOf (q₁ b) = 3 ∨ orderOf (q₂ b) = 3 →
          omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer ({(b:G)} : Set G) =
            omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) := by
  obtain ⟨F,q₁,q₂,c,t,f,hswap⟩ :=
    source_original_paired_coordinates_of_hstar_natural_four D e hn hH hZH hK fK nK
  refine ⟨F,q₁,q₂,c,?_⟩
  intro b hb
  exact source_original_paired_natural_cubic_fixed_eq_of_seed_split D q₁ q₂ c
    (source_original_seed_le_moved_sup_central_alpha_of_hstar_natural_four D e hn hH hZH hK fK nK)
    t.property f hswap b hb
end CFSG.Quasithin.Chapter10
