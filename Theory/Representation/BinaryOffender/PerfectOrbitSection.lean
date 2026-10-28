module
public import Theory.Representation.BinaryOffender.Homogeneous.Existence
public import Theory.Representation.BinaryOffender.QuasisimpleCentralSection

/-!
# Faithful component actions on homogeneous orbit sections

Choose a homogeneous Irr⁺ member for a normal quasisimple subgroup and
a normalizing two-group. Its orbit span is invariant under their join.
On the quotient by the component-fixed vectors, the kernel centralizes
the component: otherwise the normal-kernel dichotomy would kill the
noncentral seed. A centerless component therefore acts faithfully on
this literal orbit quotient. No irreducibility of the whole orbit span
or of the original representation is assumed.

Source: Aschbacher--Smith A.1.42 and the orbit-section step in 5.1.23,
printed pp.32 and 645--646 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Representation.BinaryOffender
open Homogeneous
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The kernel statement needs noncentrality, not irreducibility of the section. -/
theorem centralSection_kernel_le_centralizer_of_not_fixed
    (K J : Subgroup G) [IsQuasisimple K] (hKJ : K ≤ J)
    (W : Submodule (ZMod 2) V) (hnon : ¬ W ≤ fixedSpace ρ K)
    (hJW : J ≤ subspaceStabilizer ρ W) (hJK : J ≤ normalizer (K : Set G)) :
    (centralSectionRepresentation ρ K J W hJW hJK).ker.map J.subtype ≤
      J ⊓ centralizer (K : Set G) := by
  let K₀ := K.subgroupOf J
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer hKJ).mpr hJK
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKJ).symm
  let σ := centralSectionRepresentation ρ K J W hJW hJK
  have hnonker : ¬ K₀ ≤ σ.ker := by
    intro hk
    apply hnon
    apply le_fixedSpace_of_commutator_le_fixedSpace ρ K W (hKJ.trans hJW)
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk', v, hv, rfl⟩
    exact (centralSectionRepresentation_ker_iff ρ K J W hJW hJK ⟨k,hKJ hk'⟩).mp
      (hk hk') v hv
  have hcomp : IsComponent J K₀ :=
    ⟨(inferInstance : K₀.Normal).isSubnormal,inferInstance⟩
  have hc : σ.ker ≤ centralizer (K₀ : Set J) := by
    rcases hcomp.normal_dichotomy σ.ker with hn | hc
    · exact (hnonker hn).elim
    · exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hc)
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨x.property,mem_centralizer_iff.mpr ?_⟩
  intro k hk
  exact congrArg Subtype.val ((mem_centralizer_iff.mp (hc hx)) ⟨k,hKJ hk⟩ hk)

/-- The literal join of the component and the two-group preserves its orbit span. -/
theorem orbitSection_stable {K P : Subgroup G}
    (hPK : P ≤ normalizer (K : Set G)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) :
    K ⊔ P ≤ subspaceStabilizer ρ (orbitSpan ρ P I) :=
  sup_le (orbitSpan_component_invariant ρ hPK hI) (orbitSpan_invariant ρ P I)

/-- The central orbit quotient keeps the original component faithful. -/
theorem orbitSection_faithful_on_component
    {K P : Subgroup G} [IsQuasisimple K] (hz : center K = ⊥)
    (hPK : P ≤ normalizer (K : Set G)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) :
    Function.Injective ((centralSectionRepresentation ρ K (K ⊔ P)
      (orbitSpan ρ P I) (orbitSection_stable ρ hPK hI)
        (sup_le K.le_normalizer hPK)).comp (inclusion le_sup_left)) := by
  let σ := centralSectionRepresentation ρ K (K ⊔ P)
    (orbitSpan ρ P I) (orbitSection_stable ρ hPK hI)
      (sup_le K.le_normalizer hPK)
  have hnon : ¬ orbitSpan ρ P I ≤ fixedSpace ρ K :=
    fun hh => hI.not_le_fixedSpace ρ ((le_orbitSpan ρ P I).trans hh)
  have hk := centralSection_kernel_le_centralizer_of_not_fixed ρ K (K ⊔ P)
    le_sup_left (orbitSpan ρ P I) hnon (orbitSection_stable ρ hPK hI)
      (sup_le K.le_normalizer hPK)
  apply (injective_iff_map_eq_one _).mpr
  intro k hk'
  have hc : (k : G) ∈ centralizer (K : Set G) :=
    (hk (mem_map_of_mem (K ⊔ P).subtype
      (show inclusion le_sup_left k ∈ σ.ker from hk'))).2
  have hz' : k ∈ center K := mem_center_iff.mpr (fun x =>
    Subtype.ext ((mem_centralizer_iff.mp hc) x x.property))
  simpa only [hz,mem_bot] using hz'

/-- A constructed homogeneous seed, together with its fully moved, faithful
component action on the literal central orbit quotient. -/
@[expose] def HasFaithfulHomogeneousOrbitSection (K P : Subgroup G) : Prop :=
  ∃ I : Submodule (ZMod 2) V, ∃ hI : IsIrrPlusWith ρ K P I,
    subspaceCommutator ρ (orbitSpan ρ P I) K = orbitSpan ρ P I ∧
      Function.Injective ((centralSectionRepresentation ρ K (K ⊔ P)
        (orbitSpan ρ P I) (orbitSection_stable ρ hI.normalizes hI.isIrrPlus)
        (sup_le K.le_normalizer hI.normalizes)).comp
          (inclusion (show K ≤ K ⊔ P from le_sup_left)))

/-- Homogeneous selection constructs the entire section interface. -/
theorem hasFaithfulHomogeneousOrbitSection_of_faithful
    [FiniteDimensional (ZMod 2) V] (hf : Function.Injective ρ)
    (K P : Subgroup G) [IsQuasisimple K] (hne : K ≠ ⊥)
    (hz : center K = ⊥) (hPK : P ≤ normalizer (K : Set G)) (hP : IsPGroup 2 P) :
    HasFaithfulHomogeneousOrbitSection ρ K P := by
  obtain ⟨I,hI⟩ := exists_isIrrPlusWith_of_faithful ρ hf K P hne hPK hP
  exact ⟨I,hI,orbitSpan_full_commutator ρ hI.normalizes hI.isIrrPlus,
    orbitSection_faithful_on_component ρ hz hI.normalizes hI.isIrrPlus⟩

end Representation.BinaryOffender
