module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.PointImages
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.RadicalImage
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.NormalClosureCentralizerCore
/-!
# The original automizer images and fixed three-space

Restrict the original module and point radical to the module normalizer.
Its literal action has exactly the internal module centralizer as kernel.
The unique-offender theorem then gives the original induced-automizer
images of J(R) and Baum(R), and puts V inside Baum(R). The same marking
identifies both fixed spaces with the original three-space.

Source: Aschbacher–Smith C.1.37 and 13.3.10(2), pp.141–143,887–888.
The contrary-case application is OriginalUnitaryNoncentrality.OffenderImages.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The point-radical calculation applies to the original induced automizer,
with no replacement of the action kernel or the embedded Baumann subgroup. -/
theorem unitary_point_images_on_automizer
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (R : Subgroup G) (hRN : R ≤ normalizer (V : Set G)) (hVR : V ≤ R)
    (hR : (inducedAutomizer V R).map rho ≤ Atlas.G2.LieParabolicSetup.radical₂)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (V : Set G)) :
    V ≤ ChapterB.baumann R ∧
      (inducedAutomizer V (elementaryAbelianMaxJ R)).map rho = Atlas.G2.BinaryCore.elementary ∧
      (inducedAutomizer V (ChapterB.baumann R)).map rho = Atlas.G2.BinaryCore.elementary := by
  let N := normalizer (V : Set G)
  let U := V.subgroupOf N
  let S := R.subgroupOf N
  have hVN : V ≤ N := V.le_normalizer
  let : U.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVN (p := 2)
  let aU : Additive U ≃+ Additive V := (subgroupOfEquivOfLe hVN).toAdditive
  let EU : Additive U ≃ₗ[F] Additive V := { aU with map_smul' := ZMod.map_smul aU }
  let E' := EU.trans E
  let q : N →* Atlas.G2.Model F := rho.comp V.normalizerMonoidHom.rangeRestrict
  have he' (n : N) (v : U) :
      E' (Additive.ofMul (MulAut.conjNormal n v)) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (q n) (E' (Additive.ofMul v)) :=
    he (V.normalizerMonoidHom.rangeRestrict n) (EU (Additive.ofMul v))
  have hk := unitary_coordinate_kernel U q E' he'
  have hUS : U ≤ S := fun _ hx => hVR hx
  have hmapS : S.map q = (inducedAutomizer V R).map rho := by
    rw [inducedAutomizer,Subgroup.map_map]
  have hmove : ¬ elementaryAbelianMaxJ S ≤ q.ker := by
    intro hc
    apply hJ
    have hm := map_mono (f := N.subtype) (hc.trans_eq hk)
    rw [←elementaryAbelianMaxJ_map_injective _ N.subtype_injective,
      map_subgroupOf_eq_of_le hRN,map_centralizer_subtype,
      map_subgroupOf_eq_of_le hVN] at hm
    exact hm.trans inf_le_right
  have hno := (unitary_no_strong_and_le_baumann U q E' hk he' S hUS).2
  have him := unitary_point_thompson_baumann_images U q E' hk he' S hUS
    (hmapS ▸ hR) hmove
  have hBS : (ChapterB.baumann S).map N.subtype = ChapterB.baumann R := by
    have hb : (ChapterB.baumann S).map N.subtype = ChapterB.baumann (S.map N.subtype) :=
      Stellmacher.baumann_map_injective N.subtype N.subtype_injective S
    exact hb.trans (congrArg ChapterB.baumann (map_subgroupOf_eq_of_le hRN))
  have hJS : (elementaryAbelianMaxJ S).map N.subtype = elementaryAbelianMaxJ R := by
    rw [←elementaryAbelianMaxJ_map_injective _ N.subtype_injective,
      map_subgroupOf_eq_of_le hRN]
  have hBA : ChapterB.baumann S = (ChapterB.baumann R).subgroupOf N := by
    apply map_injective N.subtype_injective
    exact hBS.trans (map_subgroupOf_eq_of_le (show ChapterB.baumann R ≤ N from
      inf_le_left.trans hRN)).symm
  have hJA : elementaryAbelianMaxJ S = (elementaryAbelianMaxJ R).subgroupOf N := by
    apply map_injective N.subtype_injective
    have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
    exact hJS.trans (map_subgroupOf_eq_of_le (hJR.trans hRN)).symm
  have hv := map_mono (f := N.subtype) hno
  rw [map_subgroupOf_eq_of_le hVN,hBS] at hv
  refine ⟨hv,?_,?_⟩
  · rw [inducedAutomizer,Subgroup.map_map]
    change ((elementaryAbelianMaxJ R).subgroupOf N).map q = _
    rw [←hJA]
    exact him.1
  · rw [inducedAutomizer,Subgroup.map_map]
    change ((ChapterB.baumann R).subgroupOf N).map q = _
    rw [←hBA]
    exact him.2

omit [Finite G] in
/-- The original centralizer of an actor with the root-eight image is
exactly the original marked three-space. -/
theorem unitary_centralizer_eq_marked_seed
    (rho : Automizer V →* Atlas.G2.Model F) (E : Additive V ≃ₗ[F] W)
    (he : ∀ a v, E (automizerRepresentation V a v) =
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (R U : Subgroup G) (hRN : R ≤ normalizer (V : Set G)) (hUV : U ≤ V)
    (hU : pointCoordinateSubspace E U = seed)
    (hR : (inducedAutomizer V R).map rho = Atlas.G2.BinaryCore.elementary) :
    V ⊓ centralizer (R : Set G) = U := by
  apply le_antisymm
  · intro v hv
    let w : Additive V := Additive.ofMul ⟨v,hv.1⟩
    have hr : Atlas.G2.rootC (1 : F) ∈ (inducedAutomizer V R).map rho := by
      rw [hR,Atlas.G2.Natural.BinaryModelOffenders.elementary_eq]
      exact Atlas.G2.NaturalOffenders.rootC_mem_elementary 1
    obtain ⟨_,⟨n,hn,rfl⟩,hr⟩ := hr
    have hc : automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict n) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hv.2 n.val hn)
    have hf := he (V.normalizerMonoidHom.rangeRestrict n) w
    rw [hc,hr] at hf
    have hw := (Atlas.G2.NaturalOffenders.fixed_rootC_iff (1 : F) one_ne_zero (E w)).mp hf.symm
    apply (mem_pointCoordinateSubspace E U w).mp
    rw [hU,mem_seed]
    exact hw
  · intro u hu
    let w : Additive V := Additive.ofMul ⟨u,hUV hu⟩
    have hw : E w ∈ seed := hU ▸ (mem_pointCoordinateSubspace E U w).mpr hu
    refine ⟨hUV hu,?_⟩
    intro r hr
    let n : normalizer (V : Set G) := ⟨r,hRN hr⟩
    have hm : rho (V.normalizerMonoidHom.rangeRestrict n) ∈ Atlas.G2.BinaryCore.elementary := by
      rw [←hR]
      exact mem_map_of_mem rho (mem_map_of_mem V.normalizerMonoidHom.rangeRestrict hr)
    have hf := (Atlas.G2.Natural.BinaryPointOffenders.fixes_seed_iff _).mpr hm (E w) hw
    have hh := E.injective ((he (V.normalizerMonoidHom.rangeRestrict n) w).trans hf)
    have heq : r * u * r⁻¹ = u := congrArg (fun z : Additive V => (z.toMul : G)) hh
    exact mul_inv_eq_iff_eq_mul.mp heq
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
