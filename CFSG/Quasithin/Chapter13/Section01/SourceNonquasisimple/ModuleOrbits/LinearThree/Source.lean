module

public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.SymmetricFive
public import Theory.Representation.SLThreeCentralExtension.Stabilizers
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Core
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.RadicalStabilizers.Models
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Preparation

/-!
# The rank-four L₃(2) branch on the original moved module

A surjective natural-head projection with fixed kernel and [U,L]=U gives
the nonsplit rank-four extension. Its fourteen-vector orbit has A₄
stabilizer. The marking retains the original normalizer quotient and
conjugation action on U; its kernel on L is proved to be O∞(L).
The actual A₄ stabilizer supplies a quaternion action on the odd Frattini
plane. The orbit index bounds [T:C_T(u)] only for the local Sylow choice.
Commutation of the original two-core and component actions then proves
C_{O₂(XT)}(u)=C_{O₂(XT)}(U). These results instantiate the literal
centralizer-analysis consumer's OrbitFacts.

Construction of the module marking belongs to the preceding 13.1.10
classification. No orbit, stabilizer, irreducibility or core-action
conclusion is assumed by the marking.

Source: Aschbacher--Smith, 13.1.10(4) and 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.OneCohomology.SLThreeCentralExtension
variable {G : Type*} [Group G] [Finite G]

/-- A genuine rank-four central natural extension marking on the original U.
The quotient on M restricts surjectively to L; every action equation refers
to the original normalizer action. No stabilizer or orbit data are fields. -/
structure RankFourMarking (L : Subgroup G) where
  quotient : normalizer (L : Set G) →* BinaryLinearThree.Group
  component_surjective : Function.Surjective (quotient.comp (inclusion L.le_normalizer))
  coordinates : normalizerMoved L ≃* Multiplicative (Fin 4 → ZMod 2)
  representation : Representation (ZMod 2) BinaryLinearThree.Group (Fin 4 → ZMod 2)
  projection : representation.IntertwiningMap BinaryLinearThree.W
  projection_surjective : Function.Surjective projection
  kernel_vector : Fin 4 → ZMod 2
  kernel_vector_ne_zero : kernel_vector ≠ 0
  kernel_eq : ∀ x, projection x = 0 ↔ x = 0 ∨ x = kernel_vector
  kernel_fixed : ∀ g, representation g kernel_vector = kernel_vector
  fully_moved : Coinvariants.ker representation = ⊤
  equivariant : ∀ m v, (coordinates (action L m v)).toAdd =
    representation (quotient m) (coordinates v).toAdd

namespace RankFourMarking
variable {L : Subgroup G} (d : RankFourMarking L)
include d

omit [Finite G] in
theorem indecomposable : ∀ A B : Submodule (ZMod 2) (Fin 4 → ZMod 2),
    (∀ g v, v ∈ A → d.representation g v ∈ A) →
    (∀ g v, v ∈ B → d.representation g v ∈ B) →
    IsCompl A B → A = ⊥ ∨ B = ⊥ := by
  have hp : Representation.OneCohomology.IsCover d.projection := by
    refine ⟨d.projection_surjective,?_,d.fully_moved⟩
    intro x hx g
    rcases (d.kernel_eq x).mp hx with rfl | rfl
    · exact map_zero _
    · exact d.kernel_fixed g
  apply Representation.OneCohomology.indecomposable_of_cover_of_simple d.projection hp
  intro A hA
  by_cases hb : A = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨x,hx,hx0⟩ := (Submodule.ne_bot_iff A).mp hb
    apply top_unique
    intro y _
    by_cases hy : y = 0
    · exact hy ▸ A.zero_mem
    obtain ⟨g,hg⟩ := BinaryLinearThree.natural_transitive_nonzero x y hx0 hy
    exact hg ▸ hA g x hx

omit [Finite G] in
theorem representation_injective : Function.Injective d.representation := by
  intro g k he
  apply Representation.specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := d.projection_surjective v
  rw [← d.projection.isIntertwining, ← d.projection.isIntertwining, he]

omit [Finite G] in
/-- The model quotient on L has precisely the kernel of the original action. -/
theorem component_kernel :
    (d.quotient.comp (inclusion L.le_normalizer)).ker = (componentAction L).ker := by
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have he (v : normalizerMoved L) :
      (d.coordinates (componentAction L l v)).toAdd =
        d.representation (d.quotient (inclusion L.le_normalizer l)) (d.coordinates v).toAdd :=
    d.equivariant (inclusion L.le_normalizer l) v
  constructor
  · intro hl
    apply MulEquiv.ext
    intro v
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [he]
    change d.representation ((d.quotient.comp (inclusion L.le_normalizer)) l)
      (d.coordinates v).toAdd = _
    rw [hl,map_one]
    rfl
  · intro hl
    apply d.representation_injective
    rw [map_one]
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd x)
    have hh := he v
    rw [hl,hv] at hh
    rw [MulAut.one_apply,hv] at hh
    change x = d.representation (d.quotient (inclusion L.le_normalizer l)) x at hh
    change d.representation (d.quotient (inclusion L.le_normalizer l)) x = x
    exact hh.symm

/-- Compatibility with the literal source quotient L/O∞(L). -/
theorem component_kernel_eq_radical {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (d.quotient.comp (inclusion L.le_normalizer)).ker = solvableRadical L := by
  rw [d.component_kernel, componentAction_ker_eq_radical h hmany hL hn]

omit [Finite G] in
theorem quotient_surjective : Function.Surjective d.quotient := by
  intro g
  obtain ⟨l,hl⟩ := d.component_surjective g
  exact ⟨inclusion L.le_normalizer l,hl⟩

omit [Finite G] in
theorem centralizer_subgroupOf_eq (u : normalizerMoved L) :
    (centralizer ({(u : G)} : Set G)).subgroupOf (normalizer (L : Set G)) =
      (vectorStabilizer d.representation (d.coordinates u).toAdd).comap d.quotient := by
  ext m
  change (m : G) ∈ centralizer ({(u : G)} : Set G) ↔
    d.representation (d.quotient m) (d.coordinates u).toAdd = (d.coordinates u).toAdd
  rw [mem_centralizer_singleton_iff, ← d.equivariant]
  constructor
  · intro hc
    have hh : action L m u = u := by
      apply Subtype.ext
      change (m : G)*(u : G)*(m : G)⁻¹ = (u : G)
      rw [hc,mul_inv_cancel_right]
    rw [hh]
  · intro he
    have hh := d.coordinates.injective (Multiplicative.toAdd.injective he)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)

omit [Finite G] in
theorem component_centralizer_image (u : normalizerMoved L) :
    ((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (d.quotient.comp (inclusion L.le_normalizer)) =
        vectorStabilizer d.representation (d.coordinates u).toAdd := by
  have he : (centralizer ({(u : G)} : Set G)).subgroupOf L =
      (vectorStabilizer d.representation (d.coordinates u).toAdd).comap
        (d.quotient.comp (inclusion L.le_normalizer)) := by
    ext l
    exact Iff.of_eq (congrArg (fun H : Subgroup (normalizer (L : Set G)) =>
      inclusion L.le_normalizer l ∈ H) (d.centralizer_subgroupOf_eq u))
  rw [he, map_comap_eq_self_of_surjective d.component_surjective]

private def centralizerImageEquivModel (u : normalizerMoved L) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
      (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        (d.quotient.comp (inclusion L.le_normalizer))) := by
  let C := (centralizer ({(u : G)} : Set G)).subgroupOf L
  let a := (componentAction L).domRestrict C
  let q := (d.quotient.comp (inclusion L.le_normalizer)).domRestrict C
  have hk : a.ker = q.ker := by
    dsimp only [a,q]
    rw [MonoidHom.ker_domRestrict,MonoidHom.ker_domRestrict,d.component_kernel]
  have ha : a.range = C.map (componentAction L) := by
    change ((componentAction L).comp C.subtype).range = _
    rw [MonoidHom.range_comp,range_subtype]
  have hq : q.range = C.map (d.quotient.comp (inclusion L.le_normalizer)) := by
    change (((d.quotient.comp (inclusion L.le_normalizer))).comp C.subtype).range = _
    rw [MonoidHom.range_comp,range_subtype]
  exact (MulEquiv.subgroupCongr ha.symm).trans
    ((QuotientGroup.quotientKerEquivRange a).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        ((QuotientGroup.quotientKerEquivRange q).trans (MulEquiv.subgroupCongr hq))))

/-- The original L-centralizer has the proved A₄ image over the marked quotient. -/
def centralizerImageEquivAlternating (u : normalizerMoved L)
    (hu : d.projection (d.coordinates u).toAdd ≠ 0) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (d.quotient.comp (inclusion L.le_normalizer))) ≃* alternatingGroup (Fin 4) :=
  (MulEquiv.subgroupCongr (d.component_centralizer_image u)).trans
    (nonfixedStabilizerEquivAlternating d.representation d.projection d.kernel_vector
      d.kernel_vector_ne_zero d.kernel_eq d.kernel_fixed (by simp)
      d.indecomposable (d.coordinates u).toAdd hu)

/-- The A₄ identification on the literal component-action image on U. -/
def movedCentralizerEquivAlternating (u : normalizerMoved L)
    (hu : d.projection (d.coordinates u).toAdd ≠ 0) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
      alternatingGroup (Fin 4) :=
  (d.centralizerImageEquivModel u).trans (d.centralizerImageEquivAlternating u hu)

omit [Finite G] in
/-- The actual component-centralizer image contains a four-group. -/
theorem centralizer_image_contains_four (u : normalizerMoved L)
    (hu : d.projection (d.coordinates u).toAdd ≠ 0) :
    ∃ E : Subgroup (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (d.quotient.comp (inclusion L.le_normalizer))), IsKleinFour E := by
  rw [d.component_centralizer_image]
  exact nonfixed_stabilizer_contains_four d.representation d.projection d.kernel_vector
    d.kernel_vector_ne_zero d.kernel_eq d.kernel_fixed (by simp)
    d.indecomposable (d.coordinates u).toAdd hu

omit [Finite G] in
/-- Noncommutativity on the marked quotient is detected on the original U. -/
theorem moved_centralizer_not_commutative (u : normalizerMoved L)
    (hu : d.projection (d.coordinates u).toAdd ≠ 0) :
    ¬ IsMulCommutative (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (componentAction L)) := by
  intro hc
  apply nonfixed_stabilizer_not_commutative d.representation d.projection d.kernel_vector
    d.kernel_vector_ne_zero d.kernel_eq d.kernel_fixed (by simp)
    d.indecomposable (d.coordinates u).toAdd hu
  rw [← d.component_centralizer_image u]
  apply isMulCommutative_iff.mpr
  intro a b
  obtain ⟨l,hl,hel⟩ := a.property
  obtain ⟨k,hk,hek⟩ := b.property
  let A := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)
  let lA : A := ⟨componentAction L l,⟨l,hl,rfl⟩⟩
  let kA : A := ⟨componentAction L k,⟨k,hk,rfl⟩⟩
  have hh := congrArg Subtype.val ((isMulCommutative_iff.mp hc) lA kA)
  change componentAction L l * componentAction L k = componentAction L k * componentAction L l at hh
  apply Subtype.ext
  change (a : BinaryLinearThree.Group)*(b : BinaryLinearThree.Group) =
    (b : BinaryLinearThree.Group)*(a : BinaryLinearThree.Group)
  rw [← hel,← hek]
  apply d.representation_injective
  rw [map_mul,map_mul]
  apply LinearMap.ext
  intro x
  obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd x)
  have he := congrArg (fun f : MulAut (normalizerMoved L) => (d.coordinates (f v)).toAdd) hh
  change (d.coordinates (componentAction L l (componentAction L k v))).toAdd =
    (d.coordinates (componentAction L k (componentAction L l v))).toAdd at he
  change (d.coordinates (action L (inclusion L.le_normalizer l)
      (action L (inclusion L.le_normalizer k) v))).toAdd =
    (d.coordinates (action L (inclusion L.le_normalizer k)
      (action L (inclusion L.le_normalizer l) v))).toAdd at he
  simp only [d.equivariant,hv] at he
  exact he

omit [Finite G] in
/-- The 14-vector orbit gives the literal centralizer index in M. -/
theorem nonfixed_centralizer_index (u : normalizerMoved L)
    (hu : d.projection (d.coordinates u).toAdd ≠ 0) :
    (centralizer ({(u : G)} : Set G)).relIndex (normalizer (L : Set G)) = 14 := by
  change ((centralizer ({(u : G)} : Set G)).subgroupOf _).index = _
  rw [d.centralizer_subgroupOf_eq, index_comap_of_surjective _ d.quotient_surjective]
  exact nonfixed_stabilizer_index d.representation d.projection d.kernel_vector
    d.kernel_vector_ne_zero d.kernel_eq d.kernel_fixed (by simp)
    d.indecomposable (d.coordinates u).toAdd hu

omit [Finite G] in
theorem fixed_centralizer (u : normalizerMoved L)
    (hu : d.projection (d.coordinates u).toAdd = 0) :
    normalizer (L : Set G) ≤ centralizer ({(u : G)} : Set G) := by
  intro m hm
  have hfix : d.representation (d.quotient ⟨m,hm⟩) (d.coordinates u).toAdd =
      (d.coordinates u).toAdd := by
    rcases (d.kernel_eq _).mp hu with he | he
    · rw [he,map_zero]
    · rw [he,d.kernel_fixed]
  exact (show (⟨m,hm⟩ : normalizer (L : Set G)) ∈
      (centralizer ({(u : G)} : Set G)).subgroupOf (normalizer (L : Set G)) from
    (d.centralizer_subgroupOf_eq u).symm ▸ hfix)

/-- The source bound retains exactly the local Sylow-centralizer choice. -/
theorem centralizer_index_le_two {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ normalizer (L : Set G))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 := by
  by_cases hu : d.projection (d.coordinates u).toAdd = 0
  · rw [relIndex_eq_one.mpr (hT.trans (d.fixed_centralizer u hu))]
    decide
  · apply SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_le_two
      (T : Subgroup G) (normalizer (L : Set G)) _
      (isSylowIn_iff.mpr ⟨T.isPGroup',hT,fun A hA hTA _ => T.is_maximal' hA hTA⟩) hlocal
    rw [d.nonfixed_centralizer_index u hu]
    decide

/-- The literal 13.1.12(1--2) consumer for the rank-four marking. The
four-group in A₄ lifts to Q₈ on the original odd Frattini plane. -/
theorem centralizer_index_and_radical_irreducible {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 ∧
      RadicalCentralizerIrreducible L p u := by
  have hT := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  refine ⟨d.centralizer_index_le_two hT u hlocal,?_⟩
  by_cases hu : d.projection (d.coordinates u).toAdd = 0
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd
      (hT.trans (d.fixed_centralizer u hu))
  · exact (radical_actions_of_component_alternating_four h hmany hL hn ho hd u hlocal
      ⟨d.movedCentralizerEquivAlternating u hu⟩).2.1

/-- Irreducibility on the original odd Frattini plane, for every vector.
The A₄ image lifts to order 24, which is prime to the source prime p>3. -/
theorem radical_irreducible {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) : RadicalCentralizerIrreducible L p u := by
  have hT := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  by_cases hu : d.projection (d.coordinates u).toAdd = 0
  · exact radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd
      (hT.trans (d.fixed_centralizer u hu))
  · apply radicalCentralizerIrreducible_of_coprime_component_image h hmany hL hn ho hd u
      (d.moved_centralizer_not_commutative u hu)
    rw [component_centralizer_frattini_card h hmany hL hn ho hd u,
      Nat.card_congr (d.movedCentralizerEquivAlternating u hu).toEquiv,
      nat_card_alternatingGroup,Nat.card_fin]
    have hp := (radical_frattini_plane h.simpleQTKE hL.1.1 hn ho hd).1
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hdiv
    have hh : p ∣ 3 * 2^3 := hdiv
    rcases (Fact.out : p.Prime).dvd_mul.mp hh with h3 | h8
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3
      omega
    · have h2 := (Fact.out : p.Prime).dvd_of_dvd_pow h8
      have := Nat.le_of_dvd (by decide : 0 < 2) h2
      omega

/-- The literal point centralizer in O₂(XT) fixes the whole moved module. -/
theorem core_centralizer_eq {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({(u : G)} : Set G) =
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (normalizerMoved L : Set G) := by
  have hT := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hu : d.projection (d.coordinates u).toAdd ≠ 0 :=
    fun he => hnt (hT.trans (d.fixed_centralizer u he))
  apply le_antisymm
  · intro r hr
    refine ⟨hr.1,?_⟩
    have hrM : r ∈ normalizer (L : Set G) :=
      (pCoreIn_le 2 (XiP p L ⊔ (T : Subgroup G))).trans
        (sup_le ((XiP_le p L).trans L.le_normalizer) hT) hr.1
    let rM : normalizer (L : Set G) := ⟨r,hrM⟩
    let e := d.coordinates.symm.trans ((action L rM).trans d.coordinates)
    let f := (AddEquiv.toMultiplicative.symm e).toAddMonoidHom
    have hf (v : normalizerMoved L) :
        f (d.coordinates v).toAdd = (d.coordinates (action L rM v)).toAdd := by
      change (d.coordinates (action L rM (d.coordinates.symm (d.coordinates v)))).toAdd = _
      rw [d.coordinates.symm_apply_apply]
    have hfcomm : ∀ g y, f (d.representation g y) = d.representation g (f y) := by
      intro g y
      obtain ⟨l,hl⟩ := d.component_surjective g
      obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd y)
      have hv' : (d.coordinates v).toAdd = y := congrArg Multiplicative.toAdd hv
      rw [← hv', ← hl]
      change f (d.representation (d.quotient (inclusion L.le_normalizer l))
        (d.coordinates v).toAdd) = d.representation (d.quotient (inclusion L.le_normalizer l))
        (f (d.coordinates v).toAdd)
      rw [← d.equivariant, hf, hf, ← d.equivariant]
      have he := radicalCore_commutes_component_action h hmany hL hn ho hd rM hr.1 l
      exact congrArg (fun a : MulAut (normalizerMoved L) =>
        (d.coordinates (a v)).toAdd) he
    have hru : action L rM u = u := by
      apply Subtype.ext
      change r * (u : G) * r⁻¹ = u
      rw [mem_centralizer_singleton_iff.mp hr.2,mul_inv_cancel_right]
    have hfu : f (d.coordinates u).toAdd = (d.coordinates u).toAdd := by rw [hf,hru]
    have hall := commuting_fixer_eq_one d.representation d.projection d.kernel_vector
      d.kernel_vector_ne_zero d.kernel_eq d.kernel_fixed d.indecomposable f hfcomm
      (d.coordinates u).toAdd hu hfu
    change r ∈ centralizer (normalizerMoved L : Set G)
    rw [mem_centralizer_iff]
    intro v hv
    have he := hall (d.coordinates ⟨v,hv⟩).toAdd
    rw [hf] at he
    have hact := d.coordinates.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hact)).symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr u.property))

/-- Assemble the rank-four branch directly into the original centralizer-analysis interface. -/
theorem orbitFacts {T : Sylow 2 G} {p : ℕ} [Fact p.Prime]
    (h : SourceCentralizerStructure.Elimination.Context T L p) :
    SourceCentralizerStructure.Elimination.OrbitFacts T L p where
  irreducible u hu _ _ := d.radical_irreducible h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides ⟨u,hu⟩
  index u s := d.centralizer_index_le_two h.sylow_normalizes ⟨u,s.mem⟩ s.local_sylow
  core_action u s hnt := by
    change (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤ _
    rw [d.core_centralizer_eq h.hypothesis h.many h.maximal h.nonquasisimple
      h.odd h.divides ⟨u,s.mem⟩ hnt]
    exact inf_le_right

end RankFourMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
