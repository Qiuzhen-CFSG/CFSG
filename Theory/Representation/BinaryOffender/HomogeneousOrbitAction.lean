module
public import Theory.Representation.BinaryOffender.HomogeneousOrbitKernel
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The full action on a homogeneous component orbit

The centralizer of a centerless quasisimple component in its join with a
normalizing two-group fixes the full homogeneous orbit, including its
central covering kernels. Its kernel on that full module is therefore the
same centralizer already obtained on the central quotient.

If a subgroup induces only inner component automorphisms, its action on
the entire orbit is the action of the corresponding component elements.
The resulting homomorphism is the identity on the original component.
Consequently a quadratic-ratio bound on the faithful join image transfers
to the actual component action on the full orbit. The terminal Chapter14
application uses this before the paired-cover obstruction.

Source: Aschbacher--Smith A.1.41--42, D.3.4 and14.6.22,
printed pp.31--32,194,1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The component centralizer fixes the entire orbit, retaining all central kernels. -/
theorem orbitSpan_le_fixedSpace_componentCentralizer
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    orbitSpan ρ P I ≤ fixedSpace ρ ((K ⊔ P) ⊓ centralizer (K : Set G)) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer
    (show K ≤ J from le_sup_left)).mpr (sup_le K.le_normalizer hI.normalizes)
  let eK : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  have hz₀ : center K₀ = ⊥ := by
    apply bot_unique
    intro k hk
    have he := (centerCongr eK ⟨k,hk⟩).property
    change eK k ∈ center K at he
    rw [hz,mem_bot] at he
    exact eK.injective (he.trans eK.map_one.symm)
  have hgen : K₀ ⊔ P.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
      (show P ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (J ⧸ K₀) :=
    quotient_isPGroup_of_sup_eq_top (P.subgroupOf J) K₀ hP.comap_subtype
      ((sup_comm _ _).trans hgen)
  let C := J ⊓ centralizer (K : Set G)
  have hmap : (centralizer (K₀ : Set J)).map J.subtype = C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨y.property,mem_centralizer_iff.mpr ?_⟩
      intro k hk
      exact congrArg Subtype.val (mem_centralizer_iff.mp hy
        ⟨k,show k ∈ J from (show K ≤ J from le_sup_left) hk⟩ hk)
    · rintro ⟨hx,hc⟩
      refine ⟨⟨x,hx⟩,mem_centralizer_iff.mpr ?_,rfl⟩
      intro k hk
      exact Subtype.ext (mem_centralizer_iff.mp hc k hk)
  have hC : IsPGroup 2 C := hmap ▸
    (centralizer_isPGroup_of_centerless_quotient K₀ hz₀ hquot).map J.subtype
  have hfix : orbitSpan ρ P I ≤ fixedSpace ρ C := by
    apply orbitSpan_le_fixedSpace_of_normalizes ρ
      (show P ≤ normalizer (C : Set G) from ?_)
      (Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes ρ hI.isIrrPlus hC
        inf_le_right (hI.centralizer_stabilizes ρ))
    intro p hp x
    exact and_congr (J.le_normalizer ((show P ≤ J from le_sup_right) hp) x)
      (normalizer_le_normalizer_centralizer K (hI.normalizes hp) x)
  exact hfix

/-- An inner component automorphism acts on every orbit vector as its implementer. -/
theorem orbit_action_eq_of_inner
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) (p : (K ⊔ P : Subgroup G)) (k : K)
    (he : K.normalizerMonoidHom ⟨p,(sup_le K.le_normalizer hI.normalizes) p.property⟩ = MulAut.conj k) :
    ∀ v ∈ orbitSpan ρ P I, ρ p.val v = ρ k.val v := by
  have hc : k.val⁻¹ * p.val ∈ centralizer (K : Set G) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    have hh := congrArg (fun f : MulAut K => (f ⟨x,hx⟩ : G)) he
    change p.val*x*p.val⁻¹ = k.val*x*k.val⁻¹ at hh
    have hx' : p.val*x = k.val*x*k.val⁻¹*p.val := by
      rw [←hh,mul_assoc,inv_mul_cancel, mul_one]
    calc
      x * (k.val⁻¹ * p.val) = k.val⁻¹ * (k.val * x * k.val⁻¹ * p.val) := by group
      _ = k.val⁻¹ * (p.val*x) := congrArg (k.val⁻¹ * ·) hx'.symm
      _ = k.val⁻¹*p.val*x := (mul_assoc _ _ _).symm
  have hm : k.val⁻¹*p.val ∈ K ⊔ P :=
    (K ⊔ P).mul_mem ((le_sup_left : K ≤ K ⊔ P) (K.inv_mem k.property)) p.property
  intro v hv
  have hf := orbitSpan_le_fixedSpace_componentCentralizer ρ hz hP hI hv ⟨_,hm,hc⟩
  change ρ (k.val⁻¹*p.val) v = v at hf
  have hh := congrArg (ρ k.val) hf
  simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel_left] using hh


/-- The full orbit action has exactly the component centralizer as kernel. -/
theorem orbitRepresentation_kernel_eq_centralizer
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    (invariantSubspace ρ (K ⊔ P) (orbitSpan ρ P I)
      (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)).toRepresentation.ker =
      centralizer (K.subgroupOf (K ⊔ P) : Set (K ⊔ P : Subgroup G)) := by
  apply le_antisymm
  · intro x hx
    rw [← orbitSection_kernel_eq_centralizer ρ hz hP hI]
    apply (centralSectionRepresentation_ker_iff _ _ _ _ _ _ x).mpr
    intro v hv
    have hh := congrArg (fun f => ((f ⟨v,hv⟩ : orbitSpan ρ P I) : V)) hx
    change ρ x.val v = v at hh
    rw [hh,sub_self]
    exact Submodule.zero_mem _
  · intro x hx
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply orbitSpan_le_fixedSpace_componentCentralizer ρ hz hP hI v.property
      (⟨x.val,x.property,?_⟩ : ((K ⊔ P) ⊓ centralizer (K : Set G) : Subgroup G))
    apply mem_centralizer_iff.mpr
    intro k hk
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx
      ⟨k,(le_sup_left : K ≤ K ⊔ P) hk⟩ hk)

/-- The original centerless component is faithful on the full orbit module. -/
theorem orbit_component_faithful
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    Function.Injective (invariantSubspace ρ K (orbitSpan ρ P I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation := by
  apply (injective_iff_map_eq_one _).mpr
  intro k hk
  have hx : (inclusion (le_sup_left : K ≤ K ⊔ P) k) ∈
      (invariantSubspace ρ (K ⊔ P) (orbitSpan ρ P I)
        (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)).toRepresentation.ker := hk
  rw [orbitRepresentation_kernel_eq_centralizer ρ hz hP hI] at hx
  have hc : k ∈ center K := mem_center_iff.mpr (fun x => Subtype.ext
    (congrArg (fun z : (K ⊔ P : Subgroup G) => (z : G)) (mem_centralizer_iff.mp hx
      ⟨x.val,(le_sup_left : K ≤ K ⊔ P) x.property⟩ x.property)))
  simpa only [hz,mem_bot] using hc

/-- Inner actors admit a component-valued action map which is the identity on K. -/
theorem orbit_inner_actor_map
    {K P C : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) (hCP : C ≤ P)
    (hi : ∀ c : C, ∃ k : K,
      K.normalizerMonoidHom ⟨c,hI.normalizes (hCP c.property)⟩ = MulAut.conj k) :
    ∃ f : (K ⊔ C : Subgroup G) →* K,
      (∀ k : K, f (inclusion le_sup_left k) = k) ∧
      ∀ g v, v ∈ orbitSpan ρ P I → ρ g.val v = ρ (f g).val v := by
  let J := K ⊔ C
  let α : J →* MulAut K := K.normalizerMonoidHom.comp
    (inclusion (sup_le K.le_normalizer (hCP.trans hI.normalizes)))
  let j : K ≃* (MulAut.conj : K →* MulAut K).range :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hz)
  have ht : (⊤ : Subgroup J) ≤ (MulAut.conj : K →* MulAut K).range.comap α := by
    have hgen : K.subgroupOf J ⊔ C.subgroupOf J = ⊤ := by
      rw [←subgroupOf_sup (le_sup_left : K ≤ J) (le_sup_right : C ≤ J)]
      exact subgroupOf_self J
    rw [←hgen]
    apply sup_le
    · intro k hk
      refine ⟨⟨k.val,hk⟩,?_⟩
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rfl
    · intro c hc
      obtain ⟨k,hk⟩ := hi ⟨c.val,hc⟩
      exact ⟨k,hk.symm⟩
  let f : J →* K := j.symm.toMonoidHom.comp
    (α.codRestrict _ (fun g => ht (mem_top g)))
  have hf (g : J) : MulAut.conj (f g) = α g :=
    congrArg Subtype.val (j.apply_symm_apply ⟨α g,ht (mem_top g)⟩)
  refine ⟨f,?_,?_⟩
  · intro k
    apply MulAut.conj_injective_of_center_eq_bot hz
    exact (hf (inclusion le_sup_left k)).trans (by
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rfl)
  · intro g v hv
    exact orbit_action_eq_of_inner ρ hz hP hI
      ⟨g.val,(sup_le_sup_left hCP K) g.property⟩ (f g) (hf g).symm v hv

/-- The full component action inherits the bound on the faithful inner-actor image. -/
theorem orbit_component_quadraticRatio_le
    {K P C : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) (hCP : C ≤ P)
    (hi : ∀ c : C, ∃ k : K,
      K.normalizerMonoidHom ⟨c,hI.normalizes (hCP c.property)⟩ = MulAut.conj k)
    (hD : K ⊔ C ≤ subspaceStabilizer ρ (orbitSpan ρ P I)) :
    quadraticRatio (invariantSubspace ρ K (orbitSpan ρ P I)
      (orbitSpan_component_invariant ρ hI.normalizes hI.isIrrPlus)).toRepresentation ≤
    quadraticRatio (imageRepresentation
      (invariantSubspace ρ (K ⊔ C) (orbitSpan ρ P I) hD).toRepresentation) := by
  obtain ⟨f,_,hf⟩ := orbit_inner_actor_map ρ hz hP hI hCP hi
  apply quadraticRatio_le_image_of_equivariant _ _ f
    (orbit_component_faithful ρ hz hP hI) (LinearEquiv.refl _ _)
  intro g v
  exact Subtype.ext (hf g v v.property)

end Representation.BinaryOffender
