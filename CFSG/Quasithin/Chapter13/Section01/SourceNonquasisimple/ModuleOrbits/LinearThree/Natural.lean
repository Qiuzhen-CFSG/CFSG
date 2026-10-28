module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree.Source

/-!
# The single natural L₃(2) branch on the original moved module

The natural seven-point orbit has S₄ stabilizer. Since seven is odd, a
representative chosen with C_T(u) Sylow in C_M(u) is centralized by T.
The literal S₄ component image gives coprime nonabelian action on the odd
Frattini plane. Together these instantiate the original OrbitFacts consumer.
The marking contains only the normalizer quotient, component surjectivity,
coordinates and equivariance; its component kernel is proved to be O∞(L).

Source: Aschbacher--Smith, 13.1.10(3) and 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Representation.OneCohomology.SLThreeCentralExtension
variable {G : Type*} [Group G] [Finite G]

/-- A single natural copy, with the original normalizer and component maps. -/
structure NaturalMarking (L : Subgroup G) where
  quotient : normalizer (L : Set G) →* BinaryLinearThree.Group
  component_surjective : Function.Surjective (quotient.comp (inclusion L.le_normalizer))
  coordinates : normalizerMoved L ≃* Multiplicative BinaryLinearThree.Vector
  equivariant : ∀ m v, (coordinates (action L m v)).toAdd =
    BinaryLinearThree.W (quotient m) (coordinates v).toAdd

namespace NaturalMarking
variable {L : Subgroup G} (d : NaturalMarking L)
include d

omit [Finite G] in
/-- The model quotient on L has precisely the kernel of the original action. -/
theorem component_kernel :
    (d.quotient.comp (inclusion L.le_normalizer)).ker = (componentAction L).ker := by
  ext l
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  have he (v : normalizerMoved L) :
      (d.coordinates (componentAction L l v)).toAdd =
        BinaryLinearThree.W (d.quotient (inclusion L.le_normalizer l)) (d.coordinates v).toAdd :=
    d.equivariant (inclusion L.le_normalizer l) v
  constructor
  · intro hl
    apply MulEquiv.ext
    intro v
    apply d.coordinates.injective
    apply Multiplicative.toAdd.injective
    rw [he]
    change BinaryLinearThree.W ((d.quotient.comp (inclusion L.le_normalizer)) l)
      (d.coordinates v).toAdd = _
    rw [hl,map_one]
    rfl
  · intro hl
    apply Representation.specialLinearNatural_injective 3
    rw [map_one]
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := d.coordinates.surjective (Multiplicative.ofAdd x)
    have hh := he v
    rw [hl,hv] at hh
    rw [MulAut.one_apply,hv] at hh
    change x = BinaryLinearThree.W (d.quotient (inclusion L.le_normalizer l)) x at hh
    change BinaryLinearThree.W (d.quotient (inclusion L.le_normalizer l)) x = x
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
      (vectorStabilizer BinaryLinearThree.W (d.coordinates u).toAdd).comap d.quotient := by
  ext m
  change (m : G) ∈ centralizer ({(u : G)} : Set G) ↔
    BinaryLinearThree.W (d.quotient m) (d.coordinates u).toAdd = (d.coordinates u).toAdd
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
        vectorStabilizer BinaryLinearThree.W (d.coordinates u).toAdd := by
  have he : (centralizer ({(u : G)} : Set G)).subgroupOf L =
      (vectorStabilizer BinaryLinearThree.W (d.coordinates u).toAdd).comap
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

omit [Finite G] in
/-- The original component centralizer has the natural S₄ stabilizer. -/
def centralizerImageEquivSymmetric (u : normalizerMoved L)
    (hu : (d.coordinates u).toAdd ≠ 0) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map
      (d.quotient.comp (inclusion L.le_normalizer))) ≃* Equiv.Perm (Fin 4) := by
  have he : vectorStabilizer BinaryLinearThree.W (d.coordinates u).toAdd =
      BinaryLinearThree.OrbitStabilizers.natural (d.coordinates u).toAdd := by
    ext g
    rw [BinaryLinearThree.OrbitStabilizers.mem_natural]
    rfl
  exact (MulEquiv.subgroupCongr ((d.component_centralizer_image u).trans he)).trans
    (BinaryLinearThree.OrbitStabilizers.naturalEquivSymmetric (d.coordinates u).toAdd hu)

def movedCentralizerEquivSymmetric (u : normalizerMoved L)
    (hu : (d.coordinates u).toAdd ≠ 0) :
    (((centralizer ({(u : G)} : Set G)).subgroupOf L).map (componentAction L)) ≃*
      Equiv.Perm (Fin 4) :=
  (d.centralizerImageEquivModel u).trans (d.centralizerImageEquivSymmetric u hu)

omit [Finite G] in
/-- The seven-point natural orbit, on the original normalizer quotient. -/
theorem centralizer_index (u : normalizerMoved L) (hu : (d.coordinates u).toAdd ≠ 0) :
    (centralizer ({(u : G)} : Set G)).relIndex (normalizer (L : Set G)) = 7 := by
  change ((centralizer ({(u : G)} : Set G)).subgroupOf _).index = _
  rw [d.centralizer_subgroupOf_eq,index_comap_of_surjective _ d.quotient_surjective,
    vectorStabilizer_index]
  have he : Set.range (fun g => BinaryLinearThree.W g (d.coordinates u).toAdd) =
      {x : BinaryLinearThree.Vector | x ≠ 0} := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩ he
      apply hu
      simpa using congrArg (BinaryLinearThree.W g⁻¹) he
    · exact BinaryLinearThree.natural_transitive_nonzero _ x hu
  rw [he,Nat.card_eq_fintype_card]
  decide +kernel

/-- A locally Sylow representative in the natural copy is centralized by T. -/
theorem selected_centralized {T : Sylow 2 G}
    (hT : (T : Subgroup G) ≤ normalizer (L : Set G)) (u : normalizerMoved L)
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(u : G)} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({(u : G)} : Set G))) :
    (T : Subgroup G) ≤ centralizer ({(u : G)} : Set G) := by
  by_cases hu : (d.coordinates u).toAdd = 0
  · have hu1 : u = 1 := d.coordinates.injective (by
      apply Multiplicative.toAdd.injective
      simpa using hu)
    intro t _
    rw [mem_centralizer_singleton_iff]
    simp [hu1]
  · have hs : IsSylowIn 2 (T : Subgroup G) (normalizer (L : Set G)) :=
      isSylowIn_iff.mpr ⟨T.isPGroup',hT,fun A hA hTA _ => T.is_maximal' hA hTA⟩
    have hi := SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_le_two
      (T : Subgroup G) (normalizer (L : Set G)) (centralizer ({(u : G)} : Set G)) hs hlocal
      (by rw [d.centralizer_index u hu]; decide)
    have hd := SourceCentralizerOrbits.SymmetricFive.sylow_intersection_index_dvd
      (T : Subgroup G) (normalizer (L : Set G)) (centralizer ({(u : G)} : Set G)) hs hlocal
    rw [d.centralizer_index u hu] at hd
    have he : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) = 1 := by
      have hz : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) ≠ 0 :=
        ne_zero_of_dvd_ne_zero (by decide : (7 : ℕ) ≠ 0) hd
      interval_cases hx : (centralizer ({(u : G)} : Set G)).relIndex (T : Subgroup G) <;> norm_num [hx] at *
    exact relIndex_eq_one.mp he

/-- Natural S₄ stabilizers have coprime nonabelian action on the odd plane. -/
theorem radical_irreducible {T : Sylow 2 G}
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : normalizerMoved L) : RadicalCentralizerIrreducible L p u := by
  by_cases hu : (d.coordinates u).toAdd = 0
  · have hu1 : u = 1 := d.coordinates.injective (by
      apply Multiplicative.toAdd.injective
      simpa using hu)
    apply radicalCentralizerIrreducible_of_sylow_centralizes h.simpleQTKE hL.1.1 hn ho hd
    intro t _
    rw [mem_centralizer_singleton_iff]
    simp [hu1]
  · let e := d.movedCentralizerEquivSymmetric u hu
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

/-- The natural branch supplies all literal centralizer-analysis inputs.
A selected noncentral vector cannot occur because its orbit has odd size. -/
theorem orbitFacts {T : Sylow 2 G} {p : ℕ} [Fact p.Prime]
    (h : SourceCentralizerStructure.Elimination.Context T L p) :
    SourceCentralizerStructure.Elimination.OrbitFacts T L p where
  irreducible u hu _ _ := d.radical_irreducible h.hypothesis h.many h.maximal
    h.nonquasisimple h.odd h.divides ⟨u,hu⟩
  index u s := by
    have hi := d.selected_centralized h.sylow_normalizes ⟨u,s.mem⟩ s.local_sylow
    change (centralizer ({u} : Set G)).relIndex (T : Subgroup G) ≤ 2
    rw [relIndex_eq_one.mpr hi]
    decide
  core_action u s hnt := (hnt (d.selected_centralized h.sylow_normalizes ⟨u,s.mem⟩ s.local_sylow)).elim

end NaturalMarking
end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
