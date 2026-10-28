module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Natural
public import Theory.Representation.SL3DoubledNaturalOffenders.BinaryOrbits

/-!
# Doubled-natural L₃(2) orbits on the original moved module

The marking is on the literal group LT and retains both its component
quotient and its actual multiplicity involution. Its independent-pair orbit
has size 42 and elementary four-group component stabilizer. The possible
selected rank-one orbit has size 14 and S₄ component stabilizer. When the
multiplicity involution occurs, it is realized in the original T and the
diagonal is the unique T-invariant natural copy.

The odd seven-point diagonal orbit excludes that copy for a selected
noncentral representative. The two-core commutation theorem then forces
its point stabilizer to act trivially on all U. Four-group lifts and the
coprime S₄ cover give irreducibility on the original odd Frattini plane.
These results discharge all three fields of the literal OrbitFacts consumer.
The index bound retains the local Sylow condition in C_M(u); no marking
field assumes an orbit, stabilizer, invariant-copy or core-action conclusion.

Construction of the marking remains with the 13.1.10 classification owner.
Source: Aschbacher--Smith, 13.1.10(3) and 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.OneCohomology.SLThreeCentralExtension
open Representation.SL3DoubledNaturalOffenders.BinaryOrbits
variable {G : Type*} [Group G] [Finite G]

/-- An actual doubled-natural LT action, including its multiplicity involution.
The original component maps to SL₃ times the identity multiplicity action. -/
structure DoubledNaturalMarking (T : Sylow 2 G) (L : Subgroup G) where
  invariant : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G)
  quotient : (L ⊔ (T : Subgroup G) : Subgroup G) →*
    BinaryLinearThree.Group × Equiv.Perm (Fin 2)
  component_quotient : L →* BinaryLinearThree.Group
  component_surjective : Function.Surjective component_quotient
  component_eq : ∀ l : L, quotient (inclusion le_sup_left l) = (component_quotient l,1)
  coordinates : normalizerMoved L ≃* Multiplicative V
  equivariant : ∀ m v, (coordinates (action L (inclusion invariant m) v)).toAdd =
    outerRepresentation (quotient m) (coordinates v).toAdd

namespace DoubledNaturalMarking
variable {T : Sylow 2 G} {L : Subgroup G} (d : DoubledNaturalMarking T L)
include d

omit [Finite G] in
theorem component_equivariant (l : L) (v : normalizerMoved L) :
    (d.coordinates (componentAction L l v)).toAdd = rho (d.component_quotient l) (d.coordinates v).toAdd := by
  have he := d.equivariant (inclusion le_sup_left l) v
  rw [d.component_eq,outer_inner] at he
  exact he

omit [Finite G] in
/-- The model quotient on L has precisely the kernel of the original action. -/
theorem component_kernel :
    d.component_quotient.ker = (componentAction L).ker := by
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have he (v : normalizerMoved L) :
      (d.coordinates (componentAction L l v)).toAdd =
        rho (d.component_quotient l) (d.coordinates v).toAdd :=
    d.component_equivariant l v
  constructor
  · intro hl
    apply MulEquiv.ext
    intro v
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [he]
    change rho (d.component_quotient l)
      (d.coordinates v).toAdd = _
    rw [hl,map_one]
    rfl
  · intro hl
    apply Representation.SL3DoubledNaturalOffenders.representation_injective (ZMod 2)
    rw [map_one]
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd x)
    have hh := he v
    rw [hl,hv] at hh
    rw [MulAut.one_apply,hv] at hh
    change x = rho (d.component_quotient l) x at hh
    change rho (d.component_quotient l) x = x
    exact hh.symm

/-- Compatibility with the literal source quotient L/O∞(L). -/
theorem component_kernel_eq_radical
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L)) :
    d.component_quotient.ker = solvableRadical L := by
  rw [d.component_kernel, componentAction_ker_eq_radical h hmany hL hn]

omit [Finite G] in
/-- The literal LT-centralizer is the comap of the marked outer stabilizer. -/
theorem centralizer_subgroupOf_eq (u : normalizerMoved L) :
    (centralizer ({(u : G)} : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) =
      (outerStabilizer (d.coordinates u).toAdd).comap d.quotient := by
  ext m
  change (m : G) ∈ centralizer ({(u : G)} : Set G) ↔
    outerRepresentation (d.quotient m) (d.coordinates u).toAdd = (d.coordinates u).toAdd
  rw [mem_centralizer_singleton_iff, ← d.equivariant]
  constructor
  · intro hc
    have hh : action L (inclusion d.invariant m) u = u := by
      apply Subtype.ext
      change (m : G)*(u : G)*(m : G)⁻¹ = (u : G)
      rw [hc,mul_inv_cancel_right]
    rw [hh]
  · intro he
    have hh := d.coordinates.injective (Multiplicative.toAdd.injective he)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)

omit [Finite G] in
/-- The component image preserves precisely the original point-centralizer map. -/
theorem component_centralizer_image (u : normalizerMoved L) :
    ((centralizer ({(u : G)} : Set G)).subgroupOf L).map d.component_quotient =
      vectorStabilizer rho (d.coordinates u).toAdd := by
  have he : (centralizer ({(u : G)} : Set G)).subgroupOf L =
      (vectorStabilizer rho (d.coordinates u).toAdd).comap d.component_quotient := by
    ext l
    change (l : G) ∈ centralizer ({(u : G)} : Set G) ↔
      rho (d.component_quotient l) (d.coordinates u).toAdd = (d.coordinates u).toAdd
    rw [mem_centralizer_singleton_iff,← d.component_equivariant]
    constructor
    · intro hc
      have hh : componentAction L l u = u := by
        apply Subtype.ext
        change (l : G)*(u : G)*(l : G)⁻¹ = (u : G)
        rw [hc,mul_inv_cancel_right]
      rw [hh]
    · intro hh
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val
        (d.coordinates.injective (Multiplicative.toAdd.injective hh)))
  rw [he,map_comap_eq_self_of_surjective d.component_surjective]

private def centralizerImageEquivModel (u : normalizerMoved L) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
      (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
        d.component_quotient) := by
  let C := (centralizer ({(u : G)} : Set G)).subgroupOf L
  let a := (componentAction L).domRestrict C
  let q := d.component_quotient.domRestrict C
  have hk : a.ker = q.ker := by
    dsimp only [a,q]
    rw [MonoidHom.ker_domRestrict,MonoidHom.ker_domRestrict,d.component_kernel]
  have ha : a.range = C.map (componentAction L) := by
    change ((componentAction L).comp C.subtype).range = _
    rw [MonoidHom.range_comp,range_subtype]
  have hq : q.range = C.map d.component_quotient := by
    change ((d.component_quotient).comp C.subtype).range = _
    rw [MonoidHom.range_comp,range_subtype]
  exact (MulEquiv.subgroupCongr ha.symm).trans
    ((QuotientGroup.quotientKerEquivRange a).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        ((QuotientGroup.quotientKerEquivRange q).trans (MulEquiv.subgroupCongr hq))))

/-- The literal component-centralizer image in the 42-vector orbit is E₄. -/
def independentCentralizerEquiv (u : normalizerMoved L)
    (hu : (d.coordinates u).toAdd ∈ independent) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
      Multiplicative (ZMod 2 × ZMod 2) :=
  (d.centralizerImageEquivModel u).trans
    ((MulEquiv.subgroupCongr (d.component_centralizer_image u)).trans
      (independentStabilizerEquiv (d.coordinates u).toAdd hu))

/-- Every nonzero rank-one vector has the literal S₄ component-centralizer image. -/
def dependentCentralizerEquiv (u : normalizerMoved L)
    (hu : (d.coordinates u).toAdd ≠ 0) (hi : (d.coordinates u).toAdd ∉ independent) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
      Equiv.Perm (Fin 4) :=
  (d.centralizerImageEquivModel u).trans
    ((MulEquiv.subgroupCongr (d.component_centralizer_image u)).trans
      (dependentStabilizerEquiv (d.coordinates u).toAdd hu hi))

omit [Finite G] in
theorem quotient_surjective_of_swap (m : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hm : (d.quotient m).2 = Equiv.swap 0 1) : Function.Surjective d.quotient := by
  rintro ⟨g,s⟩
  rcases perm_two s with rfl | rfl
  · obtain ⟨l,hl⟩ := d.component_surjective g
    exact ⟨inclusion le_sup_left l,by rw [d.component_eq,hl]⟩
  · obtain ⟨l,hl⟩ := d.component_surjective ((d.quotient m).1⁻¹*g)
    refine ⟨m * inclusion le_sup_left l,?_⟩
    rw [map_mul,d.component_eq,hl]
    apply Prod.ext
    · exact mul_inv_cancel_left _ _
    · simpa using hm

omit [Finite G] in
theorem quotient_alternative : Function.Surjective d.quotient ∨
    ∀ m, (d.quotient m).2 = 1 := by
  classical
  by_cases hh : ∃ m, (d.quotient m).2 = Equiv.swap 0 1
  · obtain ⟨m,hm⟩ := hh
    exact Or.inl (d.quotient_surjective_of_swap m hm)
  · right
    intro m
    exact (perm_two (d.quotient m).2).resolve_right (fun hm => hh ⟨m,hm⟩)

omit [Finite G] in
theorem first_quotient_surjective : Function.Surjective ((MonoidHom.fst _ _).comp d.quotient) := by
  intro g
  obtain ⟨l,hl⟩ := d.component_surjective g
  refine ⟨inclusion le_sup_left l,?_⟩
  change (d.quotient (inclusion le_sup_left l)).1 = g
  rw [d.component_eq,hl]

omit [Finite G] in
theorem centralizer_index_of_trivial_multiplicity
    (ht : ∀ m, (d.quotient m).2 = 1) (u : normalizerMoved L) :
    (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) =
      (vectorStabilizer rho (d.coordinates u).toAdd).index := by
  have he : (outerStabilizer (d.coordinates u).toAdd).comap d.quotient =
      (vectorStabilizer rho (d.coordinates u).toAdd).comap
        ((MonoidHom.fst _ _).comp d.quotient) := by
    ext m
    change outerRepresentation (d.quotient m) (d.coordinates u).toAdd = (d.coordinates u).toAdd ↔
      rho (d.quotient m).1 (d.coordinates u).toAdd = (d.coordinates u).toAdd
    rw [show d.quotient m = ((d.quotient m).1,1) from Prod.ext rfl (ht m),outer_inner]
  change ((centralizer ({(u : G)} : Set G)).subgroupOf _).index = _
  rw [d.centralizer_subgroupOf_eq,he,index_comap_of_surjective _ d.first_quotient_surjective]

omit [Finite G] in
theorem centralizer_index_of_surjective (hq : Function.Surjective d.quotient)
    (u : normalizerMoved L) :
    (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) =
      (outerStabilizer (d.coordinates u).toAdd).index := by
  change ((centralizer ({(u : G)} : Set G)).subgroupOf _).index = _
  rw [d.centralizer_subgroupOf_eq,index_comap_of_surjective _ hq]

omit [Finite G] in
/-- The literal LT orbit of an independent pair has 42 points in either outer case. -/
theorem independent_centralizer_index (u : normalizerMoved L)
    (hu : (d.coordinates u).toAdd ∈ independent) :
    (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) = 42 := by
  rcases d.quotient_alternative with hq | ht
  · rw [d.centralizer_index_of_surjective hq,independent_outer_index _ hu]
  · rw [d.centralizer_index_of_trivial_multiplicity ht,independent_stabilizer_index _ hu]

omit [Finite G] in
theorem centralizer_index_not_four (u : normalizerMoved L) :
    ¬ 4 ∣ (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) := by
  rcases d.quotient_alternative with hq | ht
  · rw [d.centralizer_index_of_surjective hq]
    exact outer_index_not_four _
  · rw [d.centralizer_index_of_trivial_multiplicity ht]
    exact inner_index_not_four _

/-- Only the original local Sylow condition yields the literal index bound. -/
theorem centralizer_index_le_two (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≤ 2 := by
  have hs : IsSylowIn 2 (T : Subgroup G) (L ⊔ (T : Subgroup G)) :=
    isSylowIn_iff.mpr ⟨T.isPGroup',le_sup_right,fun A hA hTA _ => T.is_maximal' hA hTA⟩
  have hl := hlocal.restrict (inf_le_inf_right _ le_sup_right)
    (inf_le_inf_right _ d.invariant)
  exact SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_le_two
    (T : Subgroup G) (L ⊔ (T : Subgroup G)) _ hs hl (d.centralizer_index_not_four u)

private theorem selected_centralized_of_index_seven (u : normalizerMoved L)
    (h7 : (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) = 7)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  have hi := d.centralizer_index_le_two u hlocal
  have hs : IsSylowIn 2 (T : Subgroup G) (L ⊔ (T : Subgroup G)) :=
    isSylowIn_iff.mpr ⟨T.isPGroup',le_sup_right,fun A hA hTA _ => T.is_maximal' hA hTA⟩
  have hl := hlocal.restrict (inf_le_inf_right _ le_sup_right) (inf_le_inf_right _ d.invariant)
  have hd := SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_dvd
    (T : Subgroup G) (L ⊔ (T : Subgroup G)) _ hs hl
  rw [h7] at hd
  apply relIndex_eq_one.mp
  have hz : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≠ 0 :=
    ne_zero_of_dvd_ne_zero (by decide : (7 : ℕ) ≠ 0) hd
  interval_cases hx : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) <;> norm_num [hx] at *

/-- Selected noncentral vectors cannot lie in the invariant diagonal copy. -/
theorem selected_not_diagonal (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    (d.coordinates u).toAdd ∉ Representation.SL3DoubledNaturalOffenders.BinaryOrbits.diagonal := by
  intro hd
  have hz : (d.coordinates u).toAdd ≠ 0 := by
    intro hz
    have hu1 : u = 1 := d.coordinates.injective (Multiplicative.toAdd.injective (by simpa using hz))
    apply hnt
    intro t _
    rw [mem_centralizer_singleton_iff]
    simp [hu1]
  apply hnt
  apply d.selected_centralized_of_index_seven u _ hlocal
  rcases d.quotient_alternative with hq | ht
  · rw [d.centralizer_index_of_surjective hq,diagonal_outer_index _ hd hz]
  · rw [d.centralizer_index_of_trivial_multiplicity ht]
    exact dependent_inner_index _ hz (fun hi => hi.2.2 hd)

/-- The possible selected rank-one branch has the actual 14-point LT orbit. -/
theorem selected_rankOne_index (u : normalizerMoved L)
    (hu : (d.coordinates u).toAdd ∈ rankOne)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    Function.Surjective d.quotient ∧
      (centralizer ({(u : G)} : Set G)).relIndex (L ⊔ (T : Subgroup G)) = 14 := by
  rcases d.quotient_alternative with hq | ht
  · exact ⟨hq,by rw [d.centralizer_index_of_surjective hq,rankOne_outer_index _ hu]⟩
  · apply False.elim
    apply hnt
    apply d.selected_centralized_of_index_seven u _ hlocal
    rw [d.centralizer_index_of_trivial_multiplicity ht]
    apply dependent_inner_index
    · intro hz
      rcases hu with hu | hu
      · exact hu.1 (congrFun hz 0)
      · exact hu.2 (congrFun hz 1)
    · intro hi
      rcases hu with hu | hu
      · exact hi.2.1 hu.2
      · exact hi.1 hu.1

omit [Finite G] in
/-- The nontrivial multiplicity action in LT is realized by the original T. -/
theorem exists_sylow_swap (hq : Function.Surjective d.quotient) :
    ∃ t : T, (d.quotient (inclusion le_sup_right t)).2 = Equiv.swap 0 1 := by
  classical
  by_contra hh
  have ht (t : T) : (d.quotient (inclusion le_sup_right t)).2 = 1 :=
    (perm_two _).resolve_right (fun hs => hh ⟨t,hs⟩)
  let f := (MonoidHom.snd BinaryLinearThree.Group (Equiv.Perm (Fin 2))).comp d.quotient
  let K := f.ker.map (L ⊔ (T : Subgroup G)).subtype
  have hLK : L ≤ K := by
    intro l hl
    refine ⟨inclusion le_sup_left ⟨l,hl⟩,?_,rfl⟩
    change (d.quotient (inclusion le_sup_left ⟨l,hl⟩)).2 = 1
    rw [d.component_eq]
  have hTK : (T : Subgroup G) ≤ K := by
    intro t htT
    exact ⟨inclusion le_sup_right ⟨t,htT⟩,ht ⟨t,htT⟩,rfl⟩
  obtain ⟨m,hm⟩ := hq (1,Equiv.swap 0 1)
  obtain ⟨k,hk,hkm⟩ := (sup_le hLK hTK) m.property
  have hkm' : k = m := Subtype.ext hkm
  rw [hkm'] at hk
  change (d.quotient m).2 = 1 at hk
  rw [hm] at hk
  exact (by decide : (Equiv.swap (0 : Fin 2) 1) ≠ 1) hk

/-- The natural copy as a subgroup of the original U, with marked coordinates. -/
@[expose] def naturalCopy (e : BinaryLinearThree.W.IntertwiningMap rho) : Subgroup (normalizerMoved L) where
  carrier := {u | (d.coordinates u).toAdd ∈ e.toLinearMap.range}
  one_mem' := by
    change (d.coordinates 1).toAdd ∈ e.toLinearMap.range
    rw [map_one]
    exact e.toLinearMap.range.zero_mem
  mul_mem' := by
    intro u v hu hv
    change (d.coordinates (u*v)).toAdd ∈ e.toLinearMap.range
    rw [map_mul]
    exact e.toLinearMap.range.add_mem hu hv
  inv_mem' := by
    intro u hu
    change (d.coordinates u⁻¹).toAdd ∈ e.toLinearMap.range
    rw [map_inv]
    exact e.toLinearMap.range.neg_mem hu

omit [Finite G] in
/-- The invariant natural copy is unique for the literal T-conjugation action. -/
theorem unique_sylow_invariant_copy (hq : Function.Surjective d.quotient)
    (e : BinaryLinearThree.W.IntertwiningMap rho) (he : Function.Injective e)
    (hi : ∀ (t : T) (u : normalizerMoved L), u ∈ d.naturalCopy e →
      action L (inclusion (le_sup_right.trans d.invariant) t) u ∈ d.naturalCopy e) :
    d.naturalCopy e = d.naturalCopy diagonalEmbedding := by
  obtain ⟨t,ht⟩ := d.exists_sylow_swap hq
  have hc : e.toLinearMap.range = Representation.SL3DoubledNaturalOffenders.BinaryOrbits.diagonal := by
    apply unique_swap_invariant_copy (d.quotient (inclusion le_sup_right t)).1 e he
    intro v hv
    obtain ⟨u,hu⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
    have hu' : (d.coordinates u).toAdd = v := congrArg Multiplicative.toAdd hu
    have hmem : u ∈ d.naturalCopy e := by
      change (d.coordinates u).toAdd ∈ e.toLinearMap.range
      rw [hu']
      exact hv
    have hx := hi t u hmem
    change (d.coordinates (action L (inclusion d.invariant (inclusion le_sup_right t)) u)).toAdd ∈
      e.toLinearMap.range at hx
    rw [d.equivariant,hu'] at hx
    rw [show d.quotient (inclusion le_sup_right t) =
      ((d.quotient (inclusion le_sup_right t)).1,Equiv.swap 0 1) from Prod.ext rfl ht] at hx
    exact hx
  ext u
  change (d.coordinates u).toAdd ∈ e.toLinearMap.range ↔
    (d.coordinates u).toAdd ∈ diagonalEmbedding.toLinearMap.range
  rw [hc,diagonalEmbedding_range]

omit [Finite G] in
theorem diagonal_copy_invariant (t : T) (u : normalizerMoved L)
    (hu : u ∈ d.naturalCopy diagonalEmbedding) :
    action L (inclusion (le_sup_right.trans d.invariant) t) u ∈ d.naturalCopy diagonalEmbedding := by
  change (d.coordinates u).toAdd ∈ diagonalEmbedding.toLinearMap.range at hu
  change (d.coordinates (action L (inclusion d.invariant (inclusion le_sup_right t)) u)).toAdd ∈
    diagonalEmbedding.toLinearMap.range
  rw [diagonalEmbedding_range] at hu ⊢
  rw [d.equivariant]
  exact diagonal_invariant _ _ hu

/-- The literal two-core centralizer equality, for the original selected representative. -/
theorem core_centralizer_eq
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G)))
    (hnt : ¬ (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G)) :
    (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({(u : G)} : Set G) =
      (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (normalizerMoved L : Set G) := by
  apply le_antisymm
  · intro r hr
    refine ⟨hr.1,?_⟩
    have hrJ : r ∈ L ⊔ (T : Subgroup G) :=
      (pCoreIn_le 2 (XiP p L ⊔ (T : Subgroup G))).trans (sup_le_sup_right (XiP_le p L) _) hr.1
    let rJ : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨r,hrJ⟩
    let rM := inclusion d.invariant rJ
    have hc : ∀ k v, outerRepresentation (d.quotient rJ) (rho k v) =
        rho k (outerRepresentation (d.quotient rJ) v) := by
      intro k v
      obtain ⟨l,hl⟩ := d.component_surjective k
      obtain ⟨w,hw⟩ := d.coordinates.surjective (Multiplicative.ofAdd v)
      have hw' : (d.coordinates w).toAdd = v := congrArg Multiplicative.toAdd hw
      have he := radicalCore_commutes_component_action h hmany hL hn ho hd rM hr.1 l
      have hev := congrArg (fun a : MulAut (normalizerMoved L) => (d.coordinates (a w)).toAdd) he
      change (d.coordinates (action L (inclusion d.invariant rJ) (componentAction L l w))).toAdd =
        (d.coordinates (componentAction L l (action L (inclusion d.invariant rJ) w))).toAdd at hev
      rw [d.equivariant,d.component_equivariant,d.component_equivariant,d.equivariant,hl,hw'] at hev
      exact hev
    have hru : action L rM u = u := by
      apply Subtype.ext
      change r * (u : G) * r⁻¹ = u
      rw [mem_centralizer_singleton_iff.mp hr.2,mul_inv_cancel_right]
    have hfix : outerRepresentation (d.quotient rJ) (d.coordinates u).toAdd = (d.coordinates u).toAdd := by
      rw [← d.equivariant]
      exact congrArg (fun v => (d.coordinates v).toAdd) hru
    have hq : d.quotient rJ = 1 := commuting_fixer_trivial _ _ hc _
      (d.selected_not_diagonal u hlocal hnt) hfix
    change r ∈ centralizer (normalizerMoved L : Set G)
    rw [mem_centralizer_iff]
    intro v hv
    have he := d.equivariant rJ ⟨v,hv⟩
    rw [hq,map_one] at he
    have he' : action L rM ⟨v,hv⟩ = ⟨v,hv⟩ :=
      d.coordinates.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he')).symm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr u.property))

private theorem independent_radical_irreducible
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) (hu : (d.coordinates u).toAdd ∈ independent) :
    RadicalCentralizerIrreducible L p u := by
  let σ := xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)
  let C := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map σ
  obtain ⟨f,hf,hk,he⟩ := moved_action_central_cover h hmany hL hn ho hd
  obtain ⟨_,q,hq,hq3,_,F,hF,hfin,hcard,⟨e⟩⟩ :=
    component_frattini_cover_model h.simpleQTKE hL.1.1 hn ho hd
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F
    (by rw [hcard]; exact hq.odd_of_ne_two (by omega))
  let A := ((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L).rangeRestrict
  let eA : A ≃* Multiplicative (ZMod 2 × ZMod 2) :=
    (((A.equivMapOfInjective (componentAction L).range.subtype
      (componentAction L).range.subtype_injective).trans
      (MulEquiv.subgroupCongr (by rw [map_map,MonoidHom.subtype_comp_rangeRestrict]))).trans
      (d.independentCentralizerEquiv u hu))
  have hAc : Nat.card A = 4 := by
    rw [Nat.card_congr eA.toEquiv,Nat.card_eq_fintype_card]
    decide
  have hAs : ∀ a : A, a ^ 2 = 1 := by
    intro a
    apply eA.injective
    rw [map_pow,map_one]
    exact (by decide : ∀ x : Multiplicative (ZMod 2 × ZMod 2), x ^ 2 = 1) _
  obtain ⟨w⟩ := f.quaternion_comap_of_four h2 e hf hk A hAc hAs
  have hAC : A.comap f ≤ ((centralizer ({(u : G)} : Set G)).subgroupOf L).map σ.rangeRestrict := by
    rw [component_point_image_preimage L p u f he]
  let j : A.comap f →* C := (σ.range.subtype.comp (A.comap f).subtype).codRestrict C (by
    intro x
    obtain ⟨l,hl,hel⟩ := hAC x.property
    exact ⟨l,hl,congrArg Subtype.val hel⟩)
  have hj : Function.Injective j := by
    intro x y hxy
    have hh := congrArg (fun z : C => (z : MulAut (XiFrattiniQuotient (XiP p L)))) hxy
    exact Subtype.ext (Subtype.ext hh)
  let τ := xiFrattiniAction (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))
    (XiP p L) (XiP_invariant p inf_le_left)
  have hCτ : C ≤ τ.range := by
    rintro _ ⟨l,hl,rfl⟩
    refine ⟨⟨l,L.le_normalizer l.property,hl⟩,?_⟩
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with | H x =>
      induction x using QuotientGroup.induction_on with | H x => rfl
  apply radicalCentralizerIrreducible_of_quaternion h.simpleQTKE hL.1.1 hn ho hd u
  exact ⟨(inclusion hCτ).comp (j.comp w.symm.toMonoidHom),
    (inclusion_injective hCτ).comp (hj.comp w.symm.injective)⟩

/-- Every nonzero doubled-natural point centralizer is irreducible on the
original odd Frattini plane: E₄ lifts to Q₈, and S₄ lifts to coprime order 48. -/
theorem radical_irreducible
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) : RadicalCentralizerIrreducible L p u := by
  by_cases hz : (d.coordinates u).toAdd = 0
  · have hu1 : u = 1 := d.coordinates.injective (Multiplicative.toAdd.injective (by simpa using hz))
    apply radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd
    intro t _
    rw [mem_centralizer_singleton_iff]
    simp [hu1]
  · by_cases hi : (d.coordinates u).toAdd ∈ independent
    · exact d.independent_radical_irreducible h hmany hL hn ho hd u hi
    · let e := d.dependentCentralizerEquiv u hz hi
      apply radicalCentralizerIrreducible_of_coprime_component_image h hmany hL hn ho hd u
      · intro hc
        have he := congrArg e ((isMulCommutative_iff.mp hc)
          (e.symm (Equiv.swap (0 : Fin 4) 1)) (e.symm (Equiv.swap (1 : Fin 4) 2)))
        simp only [map_mul,e.apply_symm_apply] at he
        exact (by decide : Equiv.swap (0 : Fin 4) 1 * Equiv.swap 1 2 ≠
          Equiv.swap 1 2 * Equiv.swap 0 1) he
      · rw [component_centralizer_frattini_card h hmany hL hn ho hd u,
          Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
        have hp := (radical_frattini_plane h.simpleQTKE hL.1.1 hn ho hd).1
        apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        intro hdiv
        have hh : p ∣ 3 * 2^4 := hdiv
        rcases (Fact.out : p.Prime).dvd_mul.mp hh with h3 | h16
        · have := Nat.le_of_dvd (by decide : 0 < 3) h3
          omega
        · have h2 := (Fact.out : p.Prime).dvd_of_dvd_pow h16
          have := Nat.le_of_dvd (by decide : 0 < 2) h2
          omega

/-- The doubled branch supplies the literal classification consumer, with
all orbit, stabilizer and core-action premises proved from the marking. -/
theorem orbitFacts {p : ℕ} [Fact p.Prime]
    (h : SourceCentralizerStructure.Elimination.Context T L p) :
    SourceCentralizerStructure.Elimination.OrbitFacts T L p where
  irreducible u hu _ _ := d.radical_irreducible h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides ⟨u,hu⟩
  index u s := d.centralizer_index_le_two ⟨u,s.mem⟩ s.local_sylow
  core_action u s hnt := by
    change (XiP p L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer ({u} : Set G) ≤ _
    rw [d.core_centralizer_eq h.hypothesis h.many h.maximal h.nonquasisimple
      h.odd h.divides ⟨u,s.mem⟩ s.local_sylow hnt]
    exact inf_le_right

end DoubledNaturalMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
