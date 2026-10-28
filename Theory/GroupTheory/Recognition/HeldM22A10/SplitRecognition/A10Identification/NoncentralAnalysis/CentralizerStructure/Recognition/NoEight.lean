module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Section
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.SourceChecks

/-!
# No elements of order eight in Held's noncentral centralizer

The checked normal forms of the concrete local group show that each element
centralizing mu has fourth power one. Transport gives the same statement in
P = C_C(pi). Nonfusion makes P a Sylow two-subgroup of C, so a hypothetical
element of order eight could be conjugated into P, a contradiction.

This supplies the order obstruction used on p.235 of Held's Lemma 4.2.
It alone does not exclude PSL2(7): the action obtained by adjoining mu'
must first be proved faithful.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, pp.234--235.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
universe u
namespace Coordinates
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem centralizing_word_pow_four :
    ∀ a : NoncentralAnalysis.Coordinates.Code,
      NoncentralAnalysis.Coordinates.word a * NoncentralAnalysis.Coordinates.mu =
        NoncentralAnalysis.Coordinates.mu * NoncentralAnalysis.Coordinates.word a →
      NoncentralAnalysis.Coordinates.word a ^ 4 = 1 := by
  decide +kernel
end Coordinates

variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

public theorem P_pow_four (x : P D e) : x ^ 4 = 1 := by
  have hmem : x.1.1 ∈ D.centralizer ⊓ C D e :=
    ⟨mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property)), x.1.property⟩
  rw [← NoncentralAnalysis.Coordinates.ambient_centralizer_mu_map D e] at hmem
  obtain ⟨y, hy, hxy⟩ := hmem
  obtain ⟨a, ha⟩ := NoncentralAnalysis.Coordinates.word_bijective.surjective y
  have hy4 : y ^ 4 = 1 := by
    rw [← ha]
    apply Coordinates.centralizing_word_pow_four a
    rw [ha]
    exact mem_centralizer_singleton_iff.mp hy
  apply Subtype.ext
  apply Subtype.ext
  change x.1.1 ^ 4 = 1
  rw [← hxy, ← map_pow, hy4, map_one]

public theorem no_order_eight [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (x : C D e) :
    orderOf x ≠ 8 := by
  intro hx
  have hcyclic : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 3)
    (by rw [Nat.card_zpowers, hx]; decide)
  obtain ⟨T, hT⟩ := hcyclic.exists_le_sylow
  obtain ⟨S, hS⟩ := exists_sylow_eq_P D e hfusion
  let tx : T := ⟨x, hT (mem_zpowers x)⟩
  let f : T ≃* P D e := (T.equiv S).trans (MulEquiv.subgroupCongr hS)
  have ht4 : tx ^ 4 = 1 := by
    apply f.injective
    rw [map_pow, map_one]
    exact P_pow_four D e (f tx)
  have hx4 : x ^ 4 = 1 := congrArg Subtype.val ht4
  have hdiv := orderOf_dvd_of_pow_eq_one hx4
  rw [hx] at hdiv
  norm_num at hdiv

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure
