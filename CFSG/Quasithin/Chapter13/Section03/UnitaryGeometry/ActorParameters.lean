module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.PairHyperplanes


/-!
# Actual actor coordinates for the unitary conjugate pair

The literal induced automizer image constructs a surjective map from the
original elementary actor U to the three ABC parameters. Faithfulness of the
natural chart identifies its kernel with C_U(V). The actual commutator then
has the native bilinear pairing as coordinates. Both intrinsic singular loci
can therefore be tested on original group elements; in particular the vector
hyperplane is exactly the fifth-coordinate kernel.

Source: Aschbacher–Smith 13.3.12(4), printed p.890.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] {V U : Subgroup G}
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]

omit [IsElementaryAbelian 2 V] in
theorem exists_actor_parameters
    (f : Automizer V→*Atlas.G2.Model K) (hUN : U≤normalizer (V:Set G))
    (himage : (inducedAutomizer V U).map f=Atlas.G2.EvenTwoRank.elementary K) :
    ∃q : Additive U→ₗ[K]Three,Function.Surjective q ∧
      ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
        Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))) := by
  let α : U→*Atlas.G2.Model K :=
    f.comp (V.normalizerMonoidHom.rangeRestrict.comp (Subgroup.inclusion hUN))
  have hα (u : U) : α u∈Atlas.G2.EvenTwoRank.elementary K := by
    rw [←himage]
    exact ⟨_,⟨⟨u.val,hUN u.property⟩,u.property,rfl⟩,rfl⟩
  let β := α.codRestrict (Atlas.G2.EvenTwoRank.elementary K) hα
  let c := (Atlas.G2.EvenTwoRank.elementaryEquiv K).symm.toMonoidHom.comp β
  let q := c.toAdditiveLeft.toZModLinearMap 2
  have hq (u : U) : α u=Atlas.G2.EvenTwoRank.elementaryEmbedding K
      (Multiplicative.ofAdd (q (Additive.ofMul u))) := by
    have hh := (Atlas.G2.EvenTwoRank.elementaryEquiv K).apply_symm_apply (β u)
    exact (congrArg Subtype.val hh).symm
  refine ⟨q,?_,hq⟩
  intro v
  have hv : Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd v)∈
      (inducedAutomizer V U).map f := by rw [himage];exact ⟨_,rfl⟩
  obtain ⟨a,⟨n,hn,rfl⟩,ha⟩ := hv
  refine ⟨Additive.ofMul ⟨n.val,hn⟩,?_⟩
  have hh := (hq ⟨n.val,hn⟩).symm.trans ha
  exact congrArg Multiplicative.toAdd (Atlas.G2.EvenTwoRank.elementaryEmbedding_injective K hh)

theorem actor_parameter_kernel
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (u : U) : q (Additive.ofMul u)=0 ↔ u.val∈centralizer (V:Set G) := by
  let a := V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [he,he,hab]
  have hp : q (Additive.ofMul u)=0 ↔ f a=1 := by
    rw [hq]
    constructor
    · intro hh
      simp [hh]
    · intro hh
      exact congrArg Multiplicative.toAdd
        (Atlas.G2.EvenTwoRank.elementaryEmbedding_injective K (hh.trans (map_one _).symm))
  rw [hp]
  have hfa : f a=1 ↔ a=1 := by rw [←map_one f];exact hf.eq_iff
  rw [hfa]
  have ha : a=1 ↔ V.normalizerMonoidHom ⟨u.val,hUN u.property⟩=1 :=
    Subtype.val_inj.symm
  rw [ha]
  change ⟨u.val,hUN u.property⟩∈V.normalizerMonoidHom.ker ↔ _
  rw [Subgroup.normalizerMonoidHom_ker]
  rfl

theorem actor_parameter_displacement
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (u : U) (v : Additive V) :
    E (automizerRepresentation V (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩) v-v)=
      targetEmbed false (pairCommutator (q (Additive.ofMul u)) (tailCoordinate (E v))) := by
  rw [map_sub,he,hq,elementary_displacement]

theorem commute_iff_pairCommutator_eq_zero
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (u : U) (v : Additive V) : Commute u.val v.toMul.val ↔
      pairCommutator (q (Additive.ofMul u)) (tailCoordinate (E v))=0 := by
  let a := V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩
  have hfix : automizerRepresentation V a v=v ↔ Commute u.val v.toMul.val := by
    constructor
    · intro hh
      have hv := congrArg (fun v : Additive V=>v.toMul.val) hh
      change u.val*v.toMul.val*u.val⁻¹=v.toMul.val at hv
      exact mul_inv_eq_iff_eq_mul.mp hv
    · intro hh
      apply Additive.toMul.injective
      apply Subtype.ext
      change u.val*v.toMul.val*u.val⁻¹=v.toMul.val
      rw [hh.eq,mul_inv_cancel_right]
  rw [←hfix,←sub_eq_zero,←E.map_eq_zero_iff]
  rw [actor_parameter_displacement E f he hUN q hq]
  constructor
  · intro hh
    apply (targetEquiv false).injective
    apply Subtype.ext
    change targetEmbed false _=targetEmbed false 0
    simpa only [map_zero] using hh
  · intro hh
    rw [hh,map_zero]

theorem vector_hyperplane_criterion
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hUN : U≤normalizer (V:Set G)) (q : Additive U→ₗ[K]Three) (hqs : Function.Surjective q)
    (hq : ∀u : U,f (V.normalizerMonoidHom.rangeRestrict ⟨u.val,hUN u.property⟩)=
      Atlas.G2.EvenTwoRank.elementaryEmbedding K (Multiplicative.ofAdd (q (Additive.ofMul u))))
    (R : Subgroup G) (hker : ∀u : U,q (Additive.ofMul u)=0 ↔ u.val∈R)
    (v : Additive V) :
    (∃u∈U,u∉R ∧ Commute u v.toMul.val) ↔ (E v) 5=0 := by
  change _ ↔ tailCoordinate (E v) 2=0
  rw [←pairCommutator_vector_kernel]
  constructor
  · rintro ⟨u,hu,hr,hc⟩
    refine ⟨q (Additive.ofMul ⟨u,hu⟩),fun hh=>hr ((hker _).mp hh),?_⟩
    exact (commute_iff_pairCommutator_eq_zero E f he hUN q hq _ v).mp hc
  · rintro ⟨w,hw,hβ⟩
    obtain ⟨u,rfl⟩ := hqs w
    refine ⟨u.toMul.val,u.toMul.property,fun hh=>hw ((hker _).mpr hh),?_⟩
    exact (commute_iff_pairCommutator_eq_zero E f he hUN q hq u.toMul v).mpr hβ
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
