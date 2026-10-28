module
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.TripleSolvable
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The index-63 obstruction in native M23 two-locals

A full-Sylow subgroup of relative index 63 has order 8064. If its two-core
is nontrivial, its normalizer lies in a maximal two-local. Native coverage
identifies the latter with the triple or heptad stabilizer. The triple
stabilizer is seven-free by its actual point-stabilizer comparison with M22.
In the heptad stabilizer the subgroup has index five. Its image under the
original quotient onto A7 has index one or five; divisibility excludes one,
and the faithful coset action of the simple A7 excludes five.

The point-component consumer retains the literal two-core and quotient maps
in Chapter12.Section05.NaturalSource.Local.Components.PointSporadicComplete.
Source: Aschbacher--Smith 12.5.3, pp.817--818; GLS3 Table 5.3d.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.SylowTwoLocals

private theorem triple_seven_free : ¬ 7 ∣ Nat.card tripleStabilizer := by
  open TripleSolvable in
  have hmark : ¬ 7 ∣ Nat.card markedStabilizer := by
    let K := markedPointStabilizer
    have hc : Nat.card K = 1920 := by
      rw [←Nat.card_congr firstEquivMarkedPoint.toEquiv]
      exact m22PairStabilizer_card
    have hi : K.index ≤ 3 := by
      rw [MulAction.index_stabilizer]
      have ho : MulAction.orbit markedStabilizer (9 : Fin 23) ⊆
          (markedTriple : Set (Fin 23)) := by
        intro x hx
        obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
        have hm : (9 : Fin 23) ∈ markedTriple := by simp [m22M23AugmentedBlock]
        have hg := Finset.smul_mem_smul_finset (a := g.val) hm
        rwa [show g.val • markedTriple = markedTriple from g.property] at hg
      have hh := Set.ncard_le_ncard ho
      have ht : markedTriple.card = 3 := by decide +kernel
      simpa only [Set.ncard_coe_finset,ht] using hh
    have hp : 0 < K.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
    intro hd
    rw [←K.card_mul_index,hc] at hd
    rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hd | hd
    · norm_num at hd
    · have hh := Nat.le_of_dvd hp hd
      omega
  obtain ⟨g,hg⟩ := TripleSolvable.exists_triple_transport
  let e : tripleStabilizer ≃* TripleSolvable.markedStabilizer :=
    MulAction.stabilizerEquivStabilizer hg.symm
  rwa [Nat.card_congr e.toEquiv]

private theorem alternatingSeven_no_index_five (J : Subgroup (alternatingGroup (Fin 7)))
    (hi : J.index = 5) : False := by
  let := alternatingGroup.isSimpleGroup (α := Fin 7) (by simp)
  have hn : J.normalCore = ⊥ := by
    rcases (inferInstance : J.normalCore.Normal).eq_bot_or_eq_top with he | he
    · exact he
    · have ht : J = ⊤ := top_unique (he ▸ J.normalCore_le)
      simp [ht] at hi
  let f := MulAction.toPermHom (alternatingGroup (Fin 7)) ((alternatingGroup (Fin 7)) ⧸ J)
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
    (J.normalCore_eq_ker.symm.trans hn)
  have hb := Nat.card_le_card_of_injective f hf
  rw [Nat.card_perm, ←J.index_eq_card,hi,nat_card_alternatingGroup,Nat.card_fin] at hb
  norm_num at hb

private theorem heptad_no_card_8064 (J : Subgroup heptadStabilizer)
    (hc : Nat.card J = 8064) : False := by
  have hi : J.index = 5 := by
    have hh := J.card_mul_index
    rw [hc,heptadStabilizer_card] at hh
    omega
  obtain ⟨q,hq,_⟩ := heptadStabilizer_alternating_quotient
  have hd : (J.map q).index ∣ 5 := hi ▸ index_map_dvd J hq
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with he | he
  · have ht : J.map q = ⊤ := index_eq_one.mp he
    have hdiv := J.card_map_dvd q
    rw [ht,card_top,nat_card_alternatingGroup,Nat.card_fin,hc] at hdiv
    norm_num at hdiv
  · exact alternatingSeven_no_index_five _ he

/-- A subgroup in a Sylow-containing native M23 two-local cannot have order 8064. -/
theorem no_card_8064_in_twoLocal (S : Sylow 2 M23) (N J : Subgroup M23)
    (hN : IsTwoLocal N) (hSN : (S : Subgroup M23) ≤ N) (hJN : J ≤ N)
    (hc : Nat.card J = 8064) : False := by
  obtain ⟨M,hNM,hM⟩ := Finite.exists_le_maximal hN
  obtain ⟨i,⟨e⟩⟩ := sylow_maximal_twoLocal_coverage S M hM (hSN.trans hNM)
  let A := J.subgroupOf M
  have hAM : Nat.card A = 8064 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hJN.trans hNM)).toEquiv).trans hc
  let B := A.map e.toMonoidHom
  have hB : Nat.card B = 8064 := (card_map_of_injective e.injective).trans hAM
  fin_cases i
  · exact heptad_no_card_8064 B hB
  · have hd : 7 ∣ Nat.card (candidate 1) :=
      (by rw [hB]; decide : 7 ∣ Nat.card B).trans B.card_subgroup_dvd_card
    exact triple_seven_free hd

/-- The native M23 two-local geometry excludes a full-Sylow index-63 subgroup
with nontrivial intrinsic two-core. -/
theorem no_sixtyThree_index_of_core_ne_bot (S : Sylow 2 M23) (J : Subgroup M23)
    (hSJ : (S : Subgroup M23) ≤ J) (hc : pCore 2 J ≠ ⊥)
    (hi : (S : Subgroup M23).relIndex J = 63) : False := by
  have hScard : Nat.card S = 128 := by
    rw [S.card_eq_multiplicity,m23_order]
    decide +kernel
  have hJcard : Nat.card J = 8064 := by
    have hh := relIndex_mul_relIndex ⊥ (S : Subgroup M23) J bot_le hSJ
    rw [relIndex_bot_left,relIndex_bot_left,hi,hScard] at hh
    omega
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set M23) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hN : IsTwoLocal (normalizer (J.pCoreIn 2 : Set M23)) := by
    refine ⟨J.pCoreIn 2,?_,pCore_isPGroup.map J.subtype,rfl⟩
    intro he
    exact hc ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)
  exact no_card_8064_in_twoLocal S _ J hN (hSJ.trans hJN) hJN hJcard

end Sporadic.Mathieu.M23Geometry.SylowTwoLocals
