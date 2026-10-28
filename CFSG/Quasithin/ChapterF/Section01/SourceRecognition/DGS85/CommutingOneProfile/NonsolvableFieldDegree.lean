module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullElementaryMarkedProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OriginalNonElementarySource
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# The original alpha field degree in both commuting distance-one branches

Split on the literal quotient of the full Borel two-core by the beta core.
The elementary source gives a linear beta marking; the nonelementary source
selects PSU3 or SU3. Both give q_alpha = q_beta^2. Compare the original left
quotient with the actual graph actor through its starred inclusion, then
compare Sylow orders to retain the ORIGINAL field exponent.

A beta marking over the field of order two makes its quotient solvable in
all three cases. Its two-core and the original factor inclusion then make
the original beta parabolic solvable, contradicting the consumer hypothesis.
Thus the alpha exponent is twice an integer greater than one. The consumer
modules use this to exclude odd exponents and the original A5 alpha branch.
Neither local catalogues nor elementary/nonelementary selection are inputs.

This is an oriented source exclusion, not marked recognition for arbitrary
fields. The binary and unrestricted solvable branches and the remaining
unitary apartment construction stay with the full (11.7)--(11.8) assembly.
Source: DGS, Groups and Graphs (1985), (11.7)(d), pp.174--175, and
(11.8)(a,c), pp.175--177; source reduction (6.1)--(6.2), pp.118--119.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction OriginalExtension SuzukiContainment Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem linear_degree_unique {H : Type*} [Group H]
    {n m : ℕ} (_hn : 0 < n) (_hm : 0 < m)
    (en : ClassicalGroup.IsPSL H 2 (2^n)) (em : ClassicalGroup.IsPSL H 2 (2^m)) : n = m := by
  obtain ⟨F,fF,finF,hF,⟨eF⟩⟩ := en
  obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := em
  let _ := fF
  let _ := finF
  let _ := fK
  let _ := finK
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype K := Fintype.ofFinite K
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  let _ : CharP K 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hK)
  let e := eF.symm.trans eK
  let T : Sylow 2 PSL(2,F) := Classical.choice inferInstance
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : Nat.card T = Nat.card F :=
    (Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T).symm.toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have hU : Nat.card U = Nat.card K :=
    (Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive U).symm.toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have he : Nat.card T = Nat.card U := Nat.card_congr
    ((T : Subgroup PSL(2,F)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  have hh : 2^n = 2^m := by rw [←hF,←hK,←hT,←hU]; exact he
  exact Nat.pow_right_injective (by decide : 1 < 2) hh

omit [Finite G] in
private theorem mapped_linear_marking (h : HypothesisF11 L S) {n : ℕ} (_hn : 0 < n)
    (en : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).map
        (G₀ L S).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).map
            (G₀ L S).subtype)) 2 (2^n) := by
  obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := en
  let _ := fK
  let _ := finK
  let _ : Fintype K := Fintype.ofFinite K
  let _ : CharP K 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hK)
  let a := (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) false)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective
  exact ⟨K,fK,finK,hK,⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm.trans
    (reduced_graphLinearQuotient h false eK)⟩⟩

private theorem mapped_beta_not_solvable (h : HypothesisF11 L S)
    (hns : ¬ Group.IsSolvable (parabolic L S 1)) :
    ¬ Group.IsSolvable
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (G₀ L S).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
            (G₀ L S).subtype)) := by
  intro hsol
  let M := (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
    (G₀ L S).subtype
  let _ := hsol
  let _ : Group.IsNilpotent (pCore 2 M) := (pCore_isPGroup (p := 2) (G := M)).isNilpotent
  let _ : Group.IsSolvable M := (Group.isSolvable_iff_subgroup_quotient (pCore 2 M)).mpr
    ⟨inferInstance,inferInstance⟩
  have hLM : L 1 ≤ M := by
    change L 1 ≤ (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
      (G₀ L S).subtype
    rw [reduced_graphLocalGroup_image h]
    exact (local_le_starredParabolic 1).trans le_sup_left
  let _ : Group.IsSolvable (L 1) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hLM)
  exact hns ((h.parabolic_solvable_iff_local_quotient 1).mpr inferInstance)

/-- Both commuting distance-one source branches force an even left field
exponent at least four when the original parabolics are nonsolvable. -/
theorem original_nonsolvable_commuting_one_field_degree
    (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false)
      (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (hns : ∀ i : Fin 2, ¬ Group.IsSolvable (parabolic L S i))
    {n : ℕ} (hn : 0 < n)
    (en : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ m : ℕ, 1 < m ∧ n = 2*m := by
  let F := reducedFamily L S
  let M (i : Bool) := (graphLocalGroup F (base F i)).map (G₀ L S).subtype
  have hma := mapped_linear_marking h hn en
  have hmb := mapped_beta_not_solvable h (hns 1)
  have models (i : Bool) : IsRankOneModel (M i ⧸ pCore 2 (M i)) := by
    let a := (graphLocalGroup F (base F i)).equivMapOfInjective (G₀ L S).subtype
      (G₀ L S).subtype_injective
    exact (reduced_actor_models_of_nonsolvable_parabolics h hns (base F i)).of_equiv
      (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).symm
  let R := twoCore (commonBorel L S)
  let N := (Q F (base F true)).map (G₀ L S).subtype
  have hq : N = (parabolic L (reducedSylow L S) 1).pCoreIn 2 :=
    (NoncommutingProfile.reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
  have hN : (N.subgroupOf R).Normal := by
    rw [hq]
    exact FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow 1
  let _ := hN
  by_cases he : IsElementaryAbelian 2 (R ⧸ N.subgroupOf R)
  · obtain ⟨m,hm,markB,markA,_⟩ := original_borel_elementary_orders_and_paths_of_source
      h hc hb hcomm ⟨hN,he⟩
    have hdegree := linear_degree_unique hn (by omega : 0 < 2*m) hma markA
    refine ⟨m,?_,hdegree⟩
    by_contra hh
    have hm1 : m=1 := by omega
    subst m
    obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := markB
    let _ := fK
    let _ := finK
    let _ : Group.IsSolvable PSL(2,K) := Theory.PSL2.OuterSolvable.isSolvable_of_card_two
      (by simpa using hK)
    exact hmb (Group.isSolvable_of_isSolvable_injective (f := eK.toMonoidHom) eK.injective)
  · obtain ⟨m,hm,markB⟩ := original_borel_nonElementary_unitary_beta
      h hc hb hcomm (models false) (models true) ⟨hN,he⟩
    have markA := (original_unitary_field_and_valences h hc hb hcomm (models false) hm markB).1
    have hdegree := linear_degree_unique hn (by omega : 0 < 2*m) hma markA
    refine ⟨m,?_,hdegree⟩
    by_contra hh
    have hm1 : m=1 := by omega
    subst m
    rcases markB with markB | markB
    · exact hmb (projective_unitary_two_isSolvable (by simpa using markB))
    · exact hmb (special_unitary_two_isSolvable (by simpa using markB))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
