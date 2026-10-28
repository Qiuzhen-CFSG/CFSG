module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameCoreCoverage
public import Theory.Representation.SL3.PointRadicalDualCard

/-!
# Exact orders in the original linear-four component core

A subgroup of Q fixed modulo U by R₂ maps into the point-radical fixed
space on the original doubled dual. Its four field coordinates, together
with the three-dimensional natural kernel U, bound its order by 2^(7n).
This bound uses the original secondary projection and needs no secondary
source record or terminal quotient assumption.

For P=O₂(K_Z) in the linear-four branch, the proved identities P'=Z_S
and PQ=R₂ put P∩Q in that fixed space. The original index |P:P∩Q|=16
therefore gives |P|≤2^18. The nontrivial component section has degree
sixteen or eighteen and its denominator contains Φ(P), of order four.
The upper bound forces the section to be all of P/Φ(P), of order 2^16.
Consequently |P|=2^18 and |P∩Q|=2^14, through the original subtype maps.

The terminal application retains MSData and SecondarySourceData. In
particular these order computations do not construct the strict
core-enlargement field or select an extension action on the remaining
sixteen-dimensional quotient. The independent whole-core classification,
quotient recognition and final nonblock assembly retain their existing
owners and premises.
Source: Aschbacher--Smith, C.1.34(3), pp.136--137, and the conclusion of
original 4.3.2, pp.618--619; the same point-radical and Frattini actions
used in NonblockEndgameCoreCoverage and NonblockEndgameBoundedCore.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Matrix.PSL3.LinearThree Representation.SL3ParabolicNatural
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ} {d : MSData c n}
namespace RootCoordinates
variable (m : RootCoordinates d)
include m

/-- A subgroup of Q fixed modulo U by the radical has order at most 2^(7n). -/
theorem core_point_fixed_card_le (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (A : Subgroup G) (hAQ : A ≤ Q c) (hcomm : ⁅R₂ c,A⁆ ≤ U c) :
    Nat.card A ≤ 2^(7*n) := by
  obtain ⟨p,hp,hk,he,_⟩ := d.exists_elementary_dual_lifts
  let f := p.comp (inclusion hAQ)
  let B := f.range.toAddSubgroup'
  have hB (v) (hv : v ∈ B) (g : pointRadicalSL d.field.Carrier) :
      ((Representation.specialLinearNatural 3).dual.prod
        (Representation.specialLinearNatural 3).dual) g.val.val v = v := by
    obtain ⟨a,ha⟩ := hv
    change f a = Multiplicative.ofAdd v at ha
    have hg : (g : pointLocalSL d.field.Carrier) ∈ pCore 2 (pointLocalSL d.field.Carrier) := by
      rw [pointLocalSL_twoCore_eq]
      exact g.property
    rw [←m.secondary_core_image hn] at hg
    obtain ⟨k,hkcore,hkg⟩ := hg
    have hkr : (k : G) ∈ R₂ c := secondary_core_le_radical D (mem_map_of_mem _ hkcore)
    let k' : K c := ⟨k,secondary_le_original k.property⟩
    let q : Q c := ⟨a,hAQ a.property⟩
    let q' : Q c := ⟨(k:G)*(a:G)*(k:G)⁻¹,
      (mem_normalizer_iff.mp (d.doubleDual.2.1 k'.property) a).mp (hAQ a.property)⟩
    have hz : q' * q⁻¹ ∈ p.ker := by
      rw [hk]
      exact hcomm (commutator_mem_commutator hkr a.property)
    have hpq : p q' = p q := by
      have hh : p (q' * q⁻¹) = 1 := hz
      rw [map_mul,map_inv] at hh
      exact mul_inv_eq_one.mp hh
    have hkg' : linearThreeActor d.model k' = g.val.val := congrArg Subtype.val hkg
    have hh := he k' q q' rfl
    rw [hpq,hkg'] at hh
    have hpa : p q = Multiplicative.ofAdd v := ha
    rw [hpa] at hh
    exact hh.symm
  have hBc := doubledDual_pointRadical_fixed_card_le B hB
  have hfc : Nat.card f.range ≤ (Nat.card d.field.Carrier)^4 := by
    let e : B ≃ f.range := {
      toFun x := ⟨Multiplicative.ofAdd x.val,x.property⟩
      invFun x := ⟨x.val.toAdd,x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    exact (Nat.card_congr e).symm ▸ hBc
  have hkc : Nat.card f.ker ≤ Nat.card (U c) := by
    let j : f.ker → U c := fun a => ⟨a.val,by
      have hz : (⟨a.val,hAQ a.val.property⟩ : Q c) ∈ p.ker := a.property
      have hz' : (⟨a.val,hAQ a.val.property⟩ : Q c) ∈ (U c).subgroupOf (Q c) := hk ▸ hz
      exact hz'⟩
    apply Nat.card_le_card_of_injective j
    intro x y heq
    exact Subtype.ext (Subtype.ext (congrArg (fun z : U c => (z : G)) heq))
  have hc := f.ker.index_mul_card
  rw [index_ker] at hc
  have hu : Nat.card (U c) = 2^(3*n) := by
    rw [card_map_of_injective (Q c).subtype_injective,d.center_card]
  have hh := Nat.mul_le_mul hfc hkc
  rw [hc,hu,d.field.card_eq,d.degree_eq,←pow_mul,←pow_add] at hh
  convert hh using 1
  congr 1
  omega

end RootCoordinates
namespace RootCoordinates
variable {d : MSData c 2} (m : RootCoordinates d)
  (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
  (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (e : (s.component ⧸ pCore 2 s.component) ≃* Matrix.PSL3Four.PSL)
include m s D h e

/-- The actual core intersection has at most fourteen binary dimensions. -/
theorem component_core_intersection_card_le :
    Nat.card (Q c ⊓ (s.component.map (rootNormalizer c).subtype).pCoreIn 2 : Subgroup G) ≤ 2^14 := by
  let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
  let A := Q c ⊓ P
  have hPP : ⁅P,P⁆ ≤ U c := by
    obtain ⟨hp,_,_,_⟩ := d.linearFour_special_root m s D h e
    rw [map_subtype_commutator] at hp
    exact hp.le.trans d.root_le_center
  have hQQ : ⁅Q c,Q c⁆ ≤ U c := by
    have hh := d.core_derived_eq_center
    rw [map_subtype_commutator] at hh
    exact hh.le
  have hQ : Q c ≤ commutatorPreimage (R₂ c) A (U c) :=
    le_commutatorPreimage (core_le_radical c) ((commutator_mono le_rfl inf_le_left).trans hQQ)
  have hP : P ≤ commutatorPreimage (R₂ c) A (U c) :=
    le_commutatorPreimage (s.component_core_le D) ((commutator_mono le_rfl inf_le_right).trans hPP)
  have hR : R₂ c ≤ commutatorPreimage (R₂ c) A (U c) :=
    (m.component_core_sup_original_core s D h e).ge.trans (sup_le hQ hP)
  have hRU : R₂ c ≤ normalizer (U c : Set G) :=
    (m.radical_le_original (by decide) D s.core_eq).trans d.natural.2.1
  exact m.core_point_fixed_card_le (by decide) D A inf_le_left
    ((le_commutatorPreimage_iff (R₂ c) A (U c) (R₂ c) hRU).mp hR).2

/-- Point-radical fixed coordinates and the exact index sixteen bound the whole core. -/
theorem component_core_card_le :
    Nat.card ((s.component.map (rootNormalizer c).subtype).pCoreIn 2) ≤ 2^18 := by
  let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
  have hc := ((Q c ⊓ P).subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Q c ⊓ P ≤ P from inf_le_right)).toEquiv] at hc
  change Nat.card (Q c ⊓ P : Subgroup G) * (Q c ⊓ P).relIndex P = Nat.card P at hc
  rw [m.component_core_intersection_index s D h e] at hc
  have hh := Nat.mul_le_mul_right 16 (m.component_core_intersection_card_le s D h e)
  rw [hc] at hh
  exact hh

/-- The bound forces the moved section to be the whole sixteen-dimensional
Frattini quotient of the original component core. -/
theorem component_core_exact_order :
    let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
    Nat.card P = 2^18 ∧ Nat.card (P ⧸ frattini P) = 2^16 ∧
      ¬ ⁅s.component.map (rootNormalizer c).subtype,P⁆ ≤ (frattini P).map P.subtype := by
  let M := s.component.map (rootNormalizer c).subtype
  let P := M.pCoreIn 2
  let F := (frattini P).map P.subtype
  have hcore : P = ((pCore 2 s.component).map s.component.subtype).map
      (rootNormalizer c).subtype := by
    dsimp only [P,M]
    rw [←map_pCoreIn_of_injective 2 s.component (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective]
    rfl
  obtain ⟨X,hX,hXK,hr,hfix,_,_,_,hcomm,_,_⟩ := d.exists_source_cubic_root D
  obtain ⟨A,B,hBA,hA,hFB,_,_,hmoved,hd⟩ :=
    m.exists_moved_core_section s D X hX hXK hr hfix hcomm e h
  have hAP : A ≤ P := hA.trans hcore.ge
  have hF : Nat.card (frattini P) = 4 := (d.linearFour_special_root m s D h e).2.2.2
  have hFc : Nat.card F = 4 := (card_map_of_injective P.subtype_injective).trans hF
  have hBc : 4 ≤ Nat.card B := hFc ▸
    Nat.card_le_card_of_injective (inclusion hFB) (inclusion_injective hFB)
  have hAc : Nat.card A ≤ Nat.card P :=
    Nat.card_le_card_of_injective (inclusion hAP) (inclusion_injective hAP)
  have hPc : Nat.card P ≤ 2^18 := m.component_core_card_le s D h e
  have hcard := (B.subgroupOf A).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv] at hcard
  change Nat.card B * B.relIndex A = Nat.card A at hcard
  have hdegree : B.relIndex A = 2^16 := by
    rcases hd with hd | hd
    · exact hd
    · rw [hd] at hcard
      norm_num at hcard hPc
      omega
  rw [hdegree] at hcard
  norm_num at hcard hPc
  have hPe : Nat.card P = 2^18 := by norm_num; omega
  have hAe : A = P := eq_of_le_of_card_ge hAP (by omega)
  have hBe : B = F := (eq_of_le_of_card_ge hFB (by rw [hFc]; omega)).symm
  refine ⟨hPe,?_,?_⟩
  · have hh := (frattini P).index_mul_card
    rw [hF,hPe] at hh
    rw [←Subgroup.index_eq_card]
    change (frattini P).index = 2^16
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 4)
    exact hh.trans (by norm_num)
  · simpa only [hAe,hBe] using hmoved

/-- The core meets Q in exactly fourteen binary dimensions. -/
theorem component_core_intersection_card :
    Nat.card (Q c ⊓ (s.component.map (rootNormalizer c).subtype).pCoreIn 2 : Subgroup G) = 2^14 := by
  let P := (s.component.map (rootNormalizer c).subtype).pCoreIn 2
  have hc := ((Q c ⊓ P).subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show Q c ⊓ P ≤ P from inf_le_right)).toEquiv] at hc
  change Nat.card (Q c ⊓ P : Subgroup G) * (Q c ⊓ P).relIndex P = Nat.card P at hc
  rw [m.component_core_intersection_index s D h e,(m.component_core_exact_order s D h e).1] at hc
  change Nat.card (Q c ⊓ P : Subgroup G) = 2^14
  apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 16)
  exact hc.trans (by norm_num)

end RootCoordinates
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
