module
public import Theory.Representation.BinaryOffender.PerfectOrbitSection
public import Theory.Representation.BinaryOffender.Homogeneous.AutomorphismTwist
public import Theory.Representation.BinaryOffender.Homogeneous.Core
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.Representation.BinaryOffender.KernelQuotient
public import Theory.Representation.BinaryOffender.QuadraticImageBound

/-!
# The kernel and generalized Fitting subgroup of a homogeneous orbit section

For a centerless quasisimple actor and a normalizing two-group, homogeneity
makes their join's component centralizer stabilize the chosen Irr⁺ seed.
Its two-group action on the seed is trivial by the odd-order linear
centralizer theorem. Normalization extends this to the entire orbit span.
Consequently the literal central quotient has kernel exactly the two-core
of the join, and its faithful image has the original component as F*.
The component isomorphism is induced by the original quotient projection.
No irreducibility of the orbit span is assumed.

Source: Aschbacher--Smith A.1.40--42, D.3.4, and the section step in
5.1.23, printed pp.31--32,194,645--646, `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem Homogeneous.IsIrrPlusWith.join
    {K P : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) : IsIrrPlusWith ρ K (K ⊔ P) I := by
  refine ⟨sup_le K.le_normalizer hI.normalizes,hI.invariant,hI.isIrrPlus,?_⟩
  have he : orbitSpan ρ (K ⊔ P) I = orbitSpan ρ P I := by
    apply le_antisymm
    · exact orbitSpan_le ρ (le_orbitSpan ρ P I)
        (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    · exact orbitSpan_le ρ (le_orbitSpan ρ (K ⊔ P) I)
        (le_sup_right.trans (orbitSpan_invariant ρ (K ⊔ P) I))
  rw [he]
  exact hI.homogeneous

theorem Homogeneous.IsIrrPlusWith.centralizer_stabilizes
    {K P : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    (K ⊔ P) ⊓ centralizer (K : Set G) ≤ subspaceStabilizer ρ I := by
  apply le_subspaceStabilizer
  intro g hg v hv
  have he := (hI.join ρ).map_eq_of_central_twist ρ ⟨g,hg.1⟩
    (LinearEquiv.refl _ _) (by
      intro k w
      have hk : K.normalizerMonoidHom
          ⟨g⁻¹, (hI.join ρ).normalizes ((K ⊔ P).inv_mem hg.1)⟩ k = k := by
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_apply_coe]
        simp only [inv_inv]
        have hc := mem_centralizer_iff.mp hg.2 k k.property
        calc
          g⁻¹ * k * g = g⁻¹ * (k * g) := mul_assoc _ _ _
          _ = g⁻¹ * (g * k) := congrArg (g⁻¹ * ·) hc
          _ = k := inv_mul_cancel_left _ _
      simp only [LinearEquiv.refl_apply,hk])
  rw [← he]
  exact ⟨v,hv,rfl⟩

theorem Homogeneous.orbitSpan_le_fixedSpace_of_normalizes
    {N P : Subgroup G} (hPN : P ≤ normalizer (N : Set G))
    {I : Submodule (ZMod 2) V} (hI : I ≤ fixedSpace ρ N) :
    orbitSpan ρ P I ≤ fixedSpace ρ N := by
  apply iSup_le
  rintro p _ ⟨v,hv,rfl⟩ n
  have hn : (p : G)⁻¹ * n * p ∈ N := by
    simpa only [inv_inv, SetLike.mem_coe] using
      ((hPN (P.inv_mem p.property)) (n : G)).mp n.property
  have hh := hI hv ⟨(p : G)⁻¹ * n * p,hn⟩
  calc
    ρ n (ρ p v) = ρ p (ρ ((p : G)⁻¹ * n * p) v) := by
      simp only [← Module.End.mul_apply, ← map_mul, ← mul_assoc,
        mul_inv_cancel, one_mul]
    _ = ρ p v := congrArg (ρ p) hh

end Representation.BinaryOffender


namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

abbrev orbitSectionRepresentation
    {K P : Subgroup G} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :=
  centralSectionRepresentation ρ K (K ⊔ P) (orbitSpan ρ P I)
    (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
    (sup_le K.le_normalizer hI.normalizes)

theorem orbitSection_kernel_eq_centralizer
    [FiniteDimensional (ZMod 2) V]
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    (orbitSectionRepresentation ρ hI).ker =
      centralizer (K.subgroupOf (K ⊔ P) : Set (K ⊔ P : Subgroup G)) := by
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
  apply le_antisymm
  · have hn : ¬ orbitSpan ρ P I ≤ fixedSpace ρ K :=
      fun hh => hI.isIrrPlus.not_le_fixedSpace ρ ((le_orbitSpan ρ P I).trans hh)
    have hk := centralSection_kernel_le_centralizer_of_not_fixed ρ K J le_sup_left
      (orbitSpan ρ P I) hn (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
      (sup_le K.le_normalizer hI.normalizes)
    intro x hx
    have hc := (hk (mem_map_of_mem J.subtype hx)).2
    exact mem_centralizer_iff.mpr (fun k hk =>
      Subtype.ext (mem_centralizer_iff.mp hc k hk))
  · intro x hx
    apply (centralSectionRepresentation_ker_iff _ _ _ _ _ _ x).mpr
    intro v hv
    have hxC : (x : G) ∈ C := hmap ▸ mem_map_of_mem J.subtype hx
    have he := hfix hv ⟨x,hxC⟩
    change ρ (x : G) v = v at he
    change ρ (x : G) v - v ∈ fixedSpace ρ K
    rw [he,sub_self]
    exact Submodule.zero_mem _

end Representation.BinaryOffender


namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem orbitSection_kernel_eq_twoCore
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    (orbitSectionRepresentation ρ hI).ker = pCore 2 (K ⊔ P : Subgroup G) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer
    (show K ≤ J from le_sup_left)).mpr (sup_le K.le_normalizer hI.normalizes)
  let eK : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv eK.symm
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
  exact (orbitSection_kernel_eq_centralizer ρ hz hP hI).trans
    (centralizer_eq_twoCore_of_centerless_quasisimple_quotient K₀ hz₀
      (quotient_isPGroup_of_sup_eq_top (P.subgroupOf J) K₀ hP.comap_subtype
        ((sup_comm _ _).trans hgen)))

theorem orbitSection_faithful_twoCore_eq_bot
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    pCore 2 (KernelQuotient.Actor (orbitSectionRepresentation ρ hI)) = ⊥ := by
  let σ := orbitSectionRepresentation ρ hI
  have hk : (actionHom σ).ker = pCore 2 (K ⊔ P : Subgroup G) :=
    (actionHom_ker_eq σ).trans (orbitSection_kernel_eq_twoCore ρ hz hP hI)
  let e := QuotientGroup.quotientMulEquivOfEq hk.symm
  have he := pCore_map_iso 2 e
  rw [pCore_quotient_pCore_eq_bot,Subgroup.map_bot] at he
  exact he.symm

/-- The component is identified by the original quotient map. -/
def orbitSectionComponentEquiv
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I) :
    K ≃* (K.subgroupOf (K ⊔ P)).map
      (KernelQuotient.projection (orbitSectionRepresentation ρ hI)) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let eK : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  have hf : Function.Injective (q.subgroupMap K₀) := by
    intro a b hab
    apply eK.injective
    apply orbitSection_faithful_on_component ρ hz hI.normalizes hI.isIrrPlus
    exact congrArg (KernelQuotient.action σ) (congrArg Subtype.val hab)
  exact eK.symm.trans (MulEquiv.ofBijective (q.subgroupMap K₀)
    ⟨hf,q.subgroupMap_surjective K₀⟩)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The component equivalence is induced by the same quotient projection. -/
theorem orbitSectionComponentEquiv_apply
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K P I) (k : K) :
    (orbitSectionComponentEquiv ρ hz hI k :
      KernelQuotient.Actor (orbitSectionRepresentation ρ hI)) =
      KernelQuotient.projection (orbitSectionRepresentation ρ hI)
        (inclusion (show K ≤ K ⊔ P from le_sup_left) k) := by rfl


theorem orbitSection_faithful_generalizedFitting
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hP : IsPGroup 2 P) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlusWith ρ K P I) :
    let σ := orbitSectionRepresentation ρ hI
    generalizedFitting (KernelQuotient.Actor σ) =
      (K.subgroupOf (K ⊔ P)).map (KernelQuotient.projection σ) := by
  let J := K ⊔ P
  let K₀ := K.subgroupOf J
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer
    (show K ≤ J from le_sup_left)).mpr (sup_le K.le_normalizer hI.normalizes)
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm
  let σ := orbitSectionRepresentation ρ hI
  let q := KernelQuotient.projection σ
  let M := K₀.map q
  have hq : Function.Surjective q := KernelQuotient.projection_surjective σ
  let : M.Normal := (inferInstance : K₀.Normal).map q hq
  let : IsQuasisimple M := IsQuasisimple.of_mulEquiv
    (orbitSectionComponentEquiv ρ hz hI)
  have hgen : K₀ ⊔ P.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
      (show P ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (J ⧸ K₀) :=
    quotient_isPGroup_of_sup_eq_top (P.subgroupOf J) K₀ hP.comap_subtype
      ((sup_comm _ _).trans hgen)
  have hquot' : IsPGroup 2 (KernelQuotient.Actor σ ⧸ M) :=
    hquot.of_surjective (QuotientGroup.map K₀ M q (le_comap_map q K₀))
      (QuotientGroup.map_surjective_of_surjective K₀ M q
        ((QuotientGroup.mk'_surjective M).comp hq) (le_comap_map q K₀))
  exact generalizedFitting_eq_of_quasisimple_two_quotient M hquot'
    (orbitSection_faithful_twoCore_eq_bot ρ hz hP hI)


end Representation.BinaryOffender
