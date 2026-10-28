module
public import Theory.GroupTheory.PResidual.CentralModuleFixed
public import Theory.ThreeSubgroups
/-!
# Mixed displacement through two central module layers

For two normalized two-perfect actors on an abelian two-group, commuting
actions allow interchange of their successive commutators. Coprime
commutator idempotence makes the mixed displacement fully moved by each
actor. If the mixed action vanishes on both layers of a filtration, the
whole mixed displacement is therefore trivial. Applying this to the
literal central quotient and removing central errors gives the second
statement; no splitting of the original module is assumed.

Source application: Aschbacher--Smith, proof of 12.6.33, case (a), printed
p.838. The original subgroup and quotient application is in
`Chapter12/Section06/LocalAlternatives/NonTensor`.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
private theorem normalizes_commutator {A B C : Subgroup G}
    (hAB : A ≤ normalizer (B : Set G)) (hAC : A ≤ normalizer (C : Set G)) :
    A ≤ normalizer (⁅B,C⁆ : Subgroup G) := by
  intro a ha
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hAB ha),
    mem_normalizer_iff_map_conj_eq.mp (hAC ha)]

omit [Finite G] in
private theorem exchange (U A B : Subgroup G) [IsMulCommutative U]
    (hAU : A ≤ normalizer (U : Set G)) (hBU : B ≤ normalizer (U : Set G))
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G))
    (hc : ⁅A,B⁆ ≤ centralizer (U : Set G)) : ⁅⁅U,A⁆,B⁆ = ⁅⁅U,B⁆,A⁆ := by
  have hzero : ⁅⁅A,B⁆,U⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hc
  have hnorm (X Y : Subgroup G) (hXU : X ≤ normalizer (U : Set G))
      (hYU : Y ≤ normalizer (U : Set G))
      (hXY : X ≤ normalizer (Y : Set G)) :
      U ≤ normalizer (⁅⁅U,X⁆,Y⁆ : Subgroup G) ∧
      X ≤ normalizer (⁅⁅U,X⁆,Y⁆ : Subgroup G) ∧
      Y ≤ normalizer (⁅⁅U,X⁆,Y⁆ : Subgroup G) := by
    have hUX : ⁅U,X⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hXU
    have hW : ⁅⁅U,X⁆,Y⁆ ≤ U :=
      (commutator_mono hUX le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hYU)
    exact ⟨((le_centralizer U).trans (centralizer_le hW)).trans
      (Subgroup.centralizer_le_normalizer _),
      normalizes_commutator (normalizer_commutator_ge_right U X) hXY,
      normalizer_commutator_ge_right _ _⟩
  apply le_antisymm
  · obtain ⟨hu,hb,ha⟩ := hnorm B A hBU hAU hBA
    apply commutator_commutator_le_of_rotate_of_le_normalizer hu ha hb
    · rw [hzero]; exact bot_le
    · rw [commutator_comm B U]
  · obtain ⟨hu,ha,hb⟩ := hnorm A B hAU hBU hAB
    apply commutator_commutator_le_of_rotate_of_le_normalizer hu hb ha
    · rw [commutator_comm B A,hzero]; exact bot_le
    · rw [commutator_comm A U]

/-- Two normalized two-perfect actors with commuting actions have no mixed
displacement if it vanishes on both layers of a filtration. -/
theorem twoPerfect_mixed_commutator_eq_bot (U I A B : Subgroup G) [IsMulCommutative U]
    (hU : IsPGroup 2 U) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hAU : A ≤ normalizer (U : Set G)) (hBU : B ≤ normalizer (U : Set G))
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G))
    (hc : ⁅A,B⁆ ≤ centralizer (U : Set G))
    (hupper : ⁅⁅U,A⁆,B⁆ ≤ I) (hlower : ⁅⁅I,A⁆,B⁆ = ⊥) :
    ⁅⁅U,A⁆,B⁆ = ⊥ := by
  have hWUA : ⁅U,A⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hAU
  have hWUB : ⁅U,B⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hBU
  have hWA : ⁅⁅⁅U,A⁆,B⁆,A⁆ = ⁅⁅U,A⁆,B⁆ := by
    rw [exchange U A B hAU hBU hAB hBA hc]
    exact commutator_isPPerfect_idempotent A ⁅U,B⁆ hA (hU.to_le hWUB)
      (normalizes_commutator hAU hAB)
  have hWB : ⁅⁅⁅U,A⁆,B⁆,B⁆ = ⁅⁅U,A⁆,B⁆ :=
    commutator_isPPerfect_idempotent B ⁅U,A⁆ hB (hU.to_le hWUA)
      (normalizes_commutator hBU hBA)
  apply le_bot_iff.mp
  calc
    ⁅⁅U,A⁆,B⁆ = ⁅⁅⁅⁅U,A⁆,B⁆,A⁆,B⁆ := by rw [hWA,hWB]
    _ ≤ ⁅⁅I,A⁆,B⁆ := commutator_mono (commutator_mono hupper le_rfl) le_rfl
    _ = ⊥ := hlower

/-- The same two-layer argument on the literal central quotient, followed by
lifting through the central two-layer. -/
theorem twoPerfect_mixed_commutator_eq_bot_modulo (U I A B Z : Subgroup G) [IsMulCommutative U] [Z.Normal]
    (hU : IsPGroup 2 U) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hAU : A ≤ normalizer (U : Set G)) (hBU : B ≤ normalizer (U : Set G))
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G))
    (hZ : Z ≤ center G) (hc : ⁅⁅A,B⁆,U⁆ ≤ Z)
    (hupper : ⁅⁅U,A⁆,B⁆ ≤ I) (hlower : ⁅⁅I,A⁆,B⁆ ≤ Z) :
    ⁅⁅U,A⁆,B⁆ = ⊥ := by
  let q := QuotientGroup.mk' Z
  have hn {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) :
      X.map q ≤ normalizer (Y.map q : Set (G ⧸ Z)) :=
    (map_mono h).trans (Y.le_normalizer_map q)
  have himage : ⁅⁅U.map q,A.map q⁆,B.map q⁆ = ⊥ := by
    apply twoPerfect_mixed_commutator_eq_bot (U.map q) (I.map q) (A.map q) (B.map q)
      (hU.map q)
      (hA.of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A))
      (hB.of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B))
      (hn hAU) (hn hBU) (hn hAB) (hn hBA)
    · apply commutator_eq_bot_iff_le_centralizer.mp
      rw [←map_commutator,←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
      exact hc
    · simpa only [map_commutator] using map_mono (f := q) hupper
    · rw [←map_commutator,←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk']
      exact hlower
  have hcentral : ⁅⁅U,A⁆,B⁆ ≤ Z := by
    rwa [←map_commutator,←map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at himage
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact centralizes_of_isPPerfect_central_displacement B U ⁅U,A⁆ Z hB hU hBU
    le_normalizer_of_normal (hZ.trans (center_le_centralizer _))
    (le_normalizer_iff_commutator_le_left.mp hAU) hcentral
end Subgroup

