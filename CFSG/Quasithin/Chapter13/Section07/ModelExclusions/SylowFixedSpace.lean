module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.ThetaAlternatives
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoverSeed
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.CoverProjection
public import Theory.Representation.CentralCoverCubicFixed
public import Theory.GroupTheory.CubicClosureTwoKernel
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# The original seed-normalizer obstruction from model Sylow fixed points

The original point residual and full component Sylow generate a solvable
model subgroup. If that subgroup normalizes its Sylow, the original seed
orbit maps into its fixed space. Cubic elements fixing this image fix every
lift through the central cover, and consequently normalize the original seed.
The source theta-solvability theorem then contradicts nonsolvable cubic
generation in the model fixed-space fixer.

All source quotient maps are retained. The two explicit model geometry
inputs are intended for the natural SL₃(4) and Sp₄(4) consumers.
Source: Aschbacher–Smith13.7.5(6) and13.7.6(5), printed pp.938–939.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Module
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

include d

/-- Fixing the literal quotient seed normalizes the original group seed. -/
theorem normalizes_seed_of_fixed_section
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (k : H)
    (hf : ∀ u ∈ sectionImage H V₃ V₁ V₃,
      ρ (QuotientGroup.mk' (pCore 2 H) k) u = u) :
    (k : G) ∈ normalizer (V₃ : Set G) := by
  apply mem_normalizer_fintype
  intro v hv
  change (k : G) * v * (k : G)⁻¹ ∈ V₃
  let u : Section08.Source.UH H V₃ := ⟨v,le_conjugateSpanBy V₃ H hv⟩
  have hh := vector_commutator ρ hρ u k
  have hfu : ρ (QuotientGroup.mk' (pCore 2 H) k) (vector H V₃ V₁ u) = vector H V₃ V₁ u :=
    hf (vector H V₃ V₁ u) ⟨u,hv,rfl⟩
  rw [hfu,sub_self] at hh
  have hc : ⁅v,(k : G)⁆ ∈ V₁ :=
    (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Section08.Source.UH H V₃)) _).mp hh
  have hi : ⁅v,(k : G)⁆⁻¹ * v ∈ V₃ :=
    V₃.mul_mem (V₃.inv_mem (d.plane_le_seed (d.line_le_plane hc))) hv
  simpa only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc,
    inv_mul_cancel, mul_one] using hi

/-- The cubic closure of a model subgroup fixing the marked seed is solvable. -/
theorem cubic_seed_fixer_solvable
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (p : Representation.IntertwiningMap (ρ.comp (modelActor hKH hK eK)) σ)
    (hp : Representation.OneCohomology.IsCover p)
    (D : Subgroup A)
    (hD : ∀ a ∈ D, ∀ u ∈ sectionImage H V₃ V₁ V₃, σ a (p u) = p u) :
    Group.IsSolvable (closure {a : D | orderOf a = 3}) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkq : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let P := D.comap q
  let f : P →* D := (q.comp P.subtype).codRestrict D (fun x => x.property)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,hx⟩ := hq a
    exact ⟨⟨x,by change q x ∈ D; rw [hx]; exact a.property⟩,Subtype.ext hx⟩
  let j : f.ker →* q.ker := (P.subtype.comp f.ker.subtype).codRestrict q.ker (by
    intro x
    exact congrArg Subtype.val x.property)
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : q.ker => z.val) he
  have hkf : IsPGroup 2 f.ker := hkq.of_injective j hj
  let C := closure {x : P | orderOf x = 3}
  let Y := closure {x : G | x ∈ K ⊓ normalizer (V₃ : Set G) ∧ orderOf x = 3}
  let b : P →* G := K.subtype.comp P.subtype
  have hb : Function.Injective b := K.subtype_injective.comp P.subtype_injective
  have hCY : C ≤ Y.comap b := by
    apply (closure_le _).mpr
    intro x hx
    apply Subgroup.subset_closure
    refine ⟨⟨x.val.property,?_⟩,(orderOf_injective b hb x).trans hx⟩
    apply normalizes_seed_of_fixed_section d ρ hρ (inclusion hKH x.val)
    intro u hu
    have hcube : q x.val ^ 3 = 1 := by
      have hh : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
      exact (map_pow (q.comp P.subtype) x 3).symm.trans (by rw [hh,map_one])
    have hh := Representation.OneCohomology.cubic_fixed_of_central_cover
      (ρ.comp (modelActor hKH hK eK)) σ p hp.2.1 (q x.val) hcube u
      (hD _ x.property u hu)
    simpa only [MonoidHom.comp_apply, q, MulEquiv.coe_toMonoidHom,
      modelActor_mk] using hh
  let i : C →* Y := (b.comp C.subtype).codRestrict Y (fun x => hCY x.property)
  let : Group.IsSolvable Y := seed_normalizer_theta_solvable d h1221 hH hcentral hKH
  have hc : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (f := i)
    (fun x y h => Subtype.ext (hb (congrArg (fun z : Y => z.val) h)))
  exact solvable_cubic_closure_of_two_kernel f hf hkf hc

/-- A model whose Sylow fixed-point fixer has nonsolvable cubic closure is excluded. -/
theorem source_model_sylow_fixer_false
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH σ eK)
    (hBorel : ∀ (S : Sylow 2 A) (J : Subgroup A), Group.IsSolvable J →
      (S : Subgroup A) ≤ J → J ≤ normalizer (S : Set A))
    (hfixer : ∀ S : Sylow 2 A, ¬ Group.IsSolvable
      (closure {a : subspaceKernel σ (fixedSpace σ (S : Subgroup A)) ⊤ | orderOf a = 3})) :
    False := by
  let : Finite A := Finite.of_equiv (K ⧸ pCore 2 K) eK.toEquiv
  obtain ⟨hKn,hgen⟩ := component_normal_and_span_of_one_le d hH hF9 hKH hK hL₁K
  obtain ⟨p,hp⟩ := exists_cover_of_section hKH hK ρ hρ hgen.symm σ eK hs
  let KN := K.subgroupOf H
  let : KN.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
  have hTH : (T : Subgroup G) ≤ H := hF9.T_le_H
  obtain ⟨Q,hQ⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal KN
  let e0 : KN ≃* K := subgroupOfEquivOfLe hKH
  let q := eK.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp e0.toMonoidHom)
  have hq : Function.Surjective q := eK.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e0.surjective)
  let S := Q.mapSurjective hq
  let B₀ : Subgroup KN := (sourceOne L T V₁).comap (H.subtype.comp KN.subtype)
  let B := B₀.map q
  have hQB : (Q : Subgroup KN) ≤ normalizer (B₀ : Set KN) := by
    apply le_normalizer_iff.mpr
    intro x hx y hy
    have ht : x ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H).subgroupOf KN := hQ ▸ hx
    exact (le_normalizer_iff.mp (T_normalizes_one L (T : Subgroup G) V₁ d.line_stable))
      x.val.val ht y.val.val hy
  have hSB : (S : Subgroup A) ≤ normalizer (B : Set A) :=
    (map_mono hQB).trans (B₀.le_normalizer_map q)
  let : Group.IsSolvable (sourceOne L T V₁) := point_residual_solvable d
  let b : B₀ →* sourceOne L T V₁ :=
    ((H.subtype.comp KN.subtype).comp B₀.subtype).codRestrict _ (fun x => x.property)
  have hb : Function.Injective b := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : sourceOne L T V₁ => z.val) he
  let : Group.IsSolvable B₀ := Group.isSolvable_of_isSolvable_injective (f := b) hb
  let : Group.IsSolvable B := Group.isSolvable_of_surjective (q.subgroupMap_surjective B₀)
  let : Group.IsNilpotent (S : Subgroup A) := S.isPGroup'.isNilpotent
  have hbn : B ≤ normalizer (S : Set A) :=
    le_sup_left.trans (hBorel S (B ⊔ (S : Subgroup A))
      (Group.isSolvable_sup_of_normalizes B (S : Subgroup A) hSB) le_sup_right)
  have hstable := fixedSpace_stable_of_normalizes σ hbn
  have hP₂ : sectionImage H V₃ V₁ V₂ ≠ ⊥ := by
    intro hz
    have hh := plane_section_finrank d (H := H)
    rw [hz,finrank_bot] at hh
    omega
  obtain ⟨u,hu,hu0⟩ := (Submodule.ne_bot_iff _).mp hP₂
  have huP : u ∈ sectionImage H V₃ V₁ V₃ := by
    obtain ⟨v,hv,rfl⟩ := hu
    exact ⟨v,d.plane_le_seed hv,rfl⟩
  have hpu : p u ∈ fixedSpace σ (S : Subgroup A) := by
    intro a
    change σ a.val (p u) = p u
    obtain ⟨k,hk,hka⟩ := a.property
    rw [←hka]
    have he : p (ρ (modelActor hKH hK eK (q k)) u) = σ (q k) (p u) :=
      LinearMap.congr_fun (p.isIntertwining' (q k)) u
    rw [←he]
    change p (ρ (modelActor hKH hK eK (eK (QuotientGroup.mk' (pCore 2 K) (e0 k)))) u) = p u
    rw [modelActor_mk]
    congr 1
    apply plane_vector_fixed d ρ hρ _ _ u hu hu0
    have ht : k ∈ ((T.subtype hTH : Sylow 2 H) : Subgroup H).subgroupOf KN := hQ ▸ hk
    exact ht
  have hL₁H := hL₁K.trans hKH
  have hseed : ∀ w ∈ sectionImage H V₃ V₁ V₃, p w ∈ fixedSpace σ (S : Subgroup A) := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0,map_zero]
      exact Submodule.zero_mem _
    obtain ⟨l,hl⟩ := seed_section_nonzero_orbit d hL₁H ρ hρ u huP hu0 w hw hw0
    let k : KN := ⟨⟨l,hL₁H l.property⟩,hL₁K l.property⟩
    have hk : k ∈ B₀ := l.property
    have ha : q k ∈ B := mem_map_of_mem q hk
    have hm : modelActor hKH hK eK (q k) =
        QuotientGroup.mk' (pCore 2 H) (inclusion hL₁H l) := by
      exact modelActor_mk hKH hK eK (e0 k)
    have he : p (ρ (modelActor hKH hK eK (q k)) u) = σ (q k) (p u) :=
      LinearMap.congr_fun (p.isIntertwining' (q k)) u
    rw [hm,hl] at he
    rw [he]
    exact (hstable ha (p u)).2 hpu
  apply hfixer S
  apply cubic_seed_fixer_solvable d h1221 hH hcentral hKH hK ρ hρ σ eK p hp
  intro a ha w hw
  exact ha.2 (p w) (hseed w hw)
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
