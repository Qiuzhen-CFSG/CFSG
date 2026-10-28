module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.Elementary
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# The component action quotient in 15.3.43

After proving that `L` is normal in `I`, form the actual quotient
`I⁺ = I/C_I(L)`. Normality of the denominator is proved inside `I`.
Normalizer control and `Y₊ ≤ L` put the kernel in `M_I`; the identity
`Y₊ = θ(M_I)` then recovers the normalizer of its image. A Sylow subgroup
is transported by the actual quotient map.

The conditions below specify the remaining outputs of (e), rather than
assuming them as standing source hypotheses. The reduction owner must
construct them before the model exclusions can be applied.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(e), printed pp.1139--1140.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.RankOne

open Subgroup

variable {G : Type*} [Group G]

/-- The containment and relative normality needed for the action quotient. -/
structure ComponentAction (I L : Subgroup G) : Prop where
  component_le : L ≤ I
  normalizes : I ≤ normalizer (L : Set G)

namespace ComponentAction

variable {I L : Subgroup G}

/-- The actual action kernel `C_I(L)`, a subgroup of `I`. -/
def kernel (_d : ComponentAction I L) : Subgroup I :=
  (centralizer (L : Set G)).subgroupOf I

instance kernel_normal (d : ComponentAction I L) : d.kernel.Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact d.normalizes.trans (normalizer_le_normalizer_centralizer _)

abbrev Quotient (d : ComponentAction I L) := I ⧸ d.kernel

def quotientMap (d : ComponentAction I L) : I →* d.Quotient :=
  QuotientGroup.mk' d.kernel

/-- The image of `X ∩ I` in `I⁺`. -/
def image (d : ComponentAction I L) (X : Subgroup G) : Subgroup d.Quotient :=
  (X.subgroupOf I).map d.quotientMap

theorem quotientMap_surjective (d : ComponentAction I L) :
    Function.Surjective d.quotientMap := QuotientGroup.mk'_surjective _

/-- The restriction of the quotient map to the component, with its image
as codomain. -/
def componentMap (d : ComponentAction I L) : L →* d.image L :=
  (d.quotientMap.subgroupMap (L.subgroupOf I)).comp
    (subgroupOfEquivOfLe d.component_le).symm.toMonoidHom

theorem componentMap_surjective (d : ComponentAction I L) :
    Function.Surjective d.componentMap :=
  (d.quotientMap.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe d.component_le).symm.surjective

theorem componentMap_ker (d : ComponentAction I L) : d.componentMap.ker = center L := by
  ext x
  rw [MonoidHom.mem_ker, Subtype.ext_iff]
  change d.quotientMap ⟨x, d.component_le x.property⟩ = 1 ↔ x ∈ center L
  rw [show d.quotientMap = QuotientGroup.mk' d.kernel from rfl,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (hx y y.property)
  · intro hx y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx (⟨y, hy⟩ : L))

/-- The canonical comparison with the central quotient. This transports
actual component model equivalences into `I⁺`; group-order comparisons
are not used to identify the image. -/
noncomputable def centerQuotientEquiv (d : ComponentAction I L) :
    (L ⧸ center L) ≃* d.image L :=
  (QuotientGroup.quotientMulEquivOfEq d.componentMap_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.componentMap d.componentMap_surjective)

theorem image_simple (d : ComponentAction I L) [Theory.GroupTheory.IsQuasisimple L] :
    IsSimpleGroup (d.image L) := by
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  exact d.centerQuotientEquiv.symm.isSimpleGroup

instance image_component_normal (d : ComponentAction I L) : (d.image L).Normal := by
  let : (L.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer d.normalizes
  exact (inferInstance : (L.subgroupOf I).Normal).map d.quotientMap d.quotientMap_surjective

/-- Centralizing `L` implies normalizing `Y₊ ≤ L`; 15.3.11(4) then
places the quotient kernel in `M_I`. -/
theorem kernel_le_intersection (d : ComponentAction I L)
    {Yplus M : Subgroup G} (hYL : Yplus ≤ L)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I) :
    d.kernel ≤ M.subgroupOf I := by
  intro x hx
  have hn : (x : G) ∈ normalizer (Yplus : Set G) :=
    Subgroup.centralizer_le_normalizer _ (centralizer_le hYL hx)
  exact (hN.le ⟨x.property, hn⟩).1

/-- The common Sylow subgroup has precisely the expected Sylow image. -/
theorem image_sylow [Finite G] (d : ComponentAction I L) {S : Subgroup G}
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S) :
    ∃ Q : Sylow 2 d.Quotient, (Q : Subgroup d.Quotient) = d.image S := by
  have hSI : S ≤ I := hP ▸ map_subtype_le _
  have hSP : S.subgroupOf I = (P : Subgroup I) := by
    apply Subgroup.map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hSI, hP]
  refine ⟨P.mapSurjective d.quotientMap_surjective, ?_⟩
  change (P : Subgroup I).map d.quotientMap = (S.subgroupOf I).map d.quotientMap
  rw [hSP]

/-- The normalizer and properness part of (e), using the actual centralizer
kernel. In particular, no unrestricted quotient-normalizer rule is used. -/
theorem image_normalizer_and_proper (d : ComponentAction I L)
    {Yplus S M : Subgroup G} (hI : I ∈ outsideFamily Yplus S M)
    (hYL : Yplus ≤ L)
    (hN : I ⊓ normalizer (Yplus : Set G) = M ⊓ I)
    (hθ : theta (M ⊓ I) = Yplus) :
    normalizer (d.image Yplus : Set d.Quotient) = d.image M ∧ d.image M < ⊤ := by
  have hYI := hYL.trans d.component_le
  have hker : d.quotientMap.ker ≤ M.subgroupOf I := by
    rw [show d.quotientMap.ker = d.kernel from QuotientGroup.ker_mk' _]
    exact d.kernel_le_intersection hYL hN
  have hθI : theta (M.subgroupOf I) = Yplus.subgroupOf I := by
    apply Subgroup.map_injective I.subtype_injective
    rw [theta_map_of_injective I.subtype I.subtype_injective,
      subgroupOf_map_subtype, hθ, map_subgroupOf_eq_of_le hYI]
  have hYM : Yplus.subgroupOf I ≤ M.subgroupOf I := by
    rw [← hθI]
    exact theta_le _
  have hNI : normalizer (Yplus.subgroupOf I : Set I) = M.subgroupOf I := by
    rw [← subgroupOf_normalizer_eq hYI]
    ext x
    exact ⟨fun hx => (hN.le ⟨x.property, hx⟩).1,
      fun hx => (hN.ge ⟨hx, x.property⟩).2⟩
  refine ⟨image_normalizer_of_theta d.quotientMap d.quotientMap_surjective
    _ _ hYM hker hθI hNI, ?_⟩
  apply image_lt_top_of_kernel_le d.quotientMap d.quotientMap_surjective _ hker
  apply lt_top_iff_ne_top.mpr
  intro he
  exact hI.2 (subgroupOf_eq_top.mp he)

end ComponentAction

/-- The model-independent output of 15.3.43(e). The image of the original
radical is identified with the two-core, so the shadow uses the source's
denominator `R⁺`. Classification of `L⁺` is a separate, model-dependent input.
This record is an output contract, not a proof of (e). -/
structure QuotientConditions {I L : Subgroup G} (d : ComponentAction I L)
    (Yplus S M : Subgroup G) : Prop where
  fitting : Theory.GroupTheory.generalizedFitting d.Quotient = d.image L
  simple : IsSimpleGroup (d.image L)
  twoLocal : IsTwoLocal (d.image M)
  residual : d.image Yplus = threeResidualIn (d.image M)
  radical : d.image ((Yplus ⊔ S).pCoreIn 2) =
    (d.image Yplus ⊔ d.image S).pCoreIn 2
  shadow : SymmetricThreeShadow (d.image Yplus) (d.image S)
  maximal : Maximal (fun X : Subgroup d.Quotient =>
    Theory.GroupTheory.generalizedFitting X = pCore 2 X) (d.image M)

end CFSG.Quasithin.Chapter15.Section03.RankOne
