module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySourceRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PairReorientation

/-!
# The elementary source comparison in the reverse critical orientation

Swapping the original factors preserves the full common Borel, its two-core
and the reduced ambient subgroup. The equivariant relabeling carries the
directed critical escape through the full local kernel. The resulting
amalgam isomorphism retains the full middle group and both inclusion maps.

An original linear beta marking makes the literal full-Borel core quotient
elementary: identify its preimage with the actual local Sylow quotient and
transport it through the original completion inclusion. Comparing Sylow
orders excludes PSL2(2) when the original field exponent exceeds one. The
proved elementary source construction then supplies the marked U4 comparison;
reversing its two endpoint maps gives the required original orientation.

The original-pair and Chapter 12 consumers use this without a branch-selection
premise. The unrestricted binary and unitary source constructions remain with
the full source assembly.
Source: DGS, Groups and Graphs (1985), the graph reduction (6.1)--(6.2),
pp.118--119, (11.7), pp.174--175, and Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile.ReversedElementary
open Reduction OriginalExtension SuzukiContainment Subgroup.CosetGeometry.RankTwo CommutingNontrivial
variable {G : Type*} [Group G] (A B S : Subgroup G)
private theorem pair_commonBorel_swap : commonBorel ![B,A] S = commonBorel ![A,B] S := by
  change borel B S ⊔ borel A S ⊔ S = borel A S ⊔ borel B S ⊔ S
  rw [sup_comm (borel B S) (borel A S)]
private theorem pair_parabolic_swap (i : Fin 2) :
    parabolic ![B,A] S i = parabolic ![A,B] S (other i) := by fin_cases i <;> rfl
private theorem pair_starredParabolic_swap (i : Fin 2) :
    starredParabolic ![B,A] S i = starredParabolic ![A,B] S (other i) := by
  unfold starredParabolic
  rw [pair_parabolic_swap A B S i]
  fin_cases i <;> rfl
private theorem pair_B₀_swap : B₀ ![B,A] S = B₀ ![A,B] S := by
  unfold B₀
  rw [pair_commonBorel_swap A B S,pair_starredParabolic_swap A B S 0,
    pair_starredParabolic_swap A B S 1]
  change (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 1) ⊔
      (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 0) ⊔ _ = _
  rw [sup_comm (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 1)
    (commonBorel ![A,B] S ⊓ starredParabolic ![A,B] S 0)]
private theorem pair_P₀_swap (i : Fin 2) : P₀ ![B,A] S i = P₀ ![A,B] S (other i) := by
  unfold P₀
  rw [pair_starredParabolic_swap A B S i,pair_B₀_swap A B S]
private theorem pair_G₀_swap : G₀ ![B,A] S = G₀ ![A,B] S := by
  unfold G₀
  rw [pair_P₀_swap A B S 0,pair_P₀_swap A B S 1]
  change P₀ ![A,B] S 1 ⊔ P₀ ![A,B] S 0 = _
  exact sup_comm _ _


private theorem pair_reducedSylow_swap : reducedSylow ![B,A] S = reducedSylow ![A,B] S := by
  unfold reducedSylow
  rw [pair_commonBorel_swap]

private theorem pair_family_swap :
    family (fun i => (P₀ ![B,A] S i).subgroupOf (G₀ ![A,B] S)) =
      swapFamily (reducedFamily ![A,B] S) := by
  funext i
  cases i
  · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![A,B] S)) (pair_P₀_swap A B S 0)
  · exact congrArg (fun H : Subgroup G => H.subgroupOf (G₀ ![A,B] S)) (pair_P₀_swap A B S 1)

variable (F : Bool → Subgroup G)
private theorem swap_stabilizer (v : Vertex F) :
    stabilizer (swapFamily F) (swapVertex F v) = stabilizer F v := by
  ext g
  change g • swapVertex F v = swapVertex F v ↔ g • v = v
  rw [←swapVertex_smul]
  exact (swapVertexEquiv F).injective.eq_iff

private theorem swap_Z (v : Vertex F) :
    Z (swapFamily F) (swapVertex F v) = Z F v := by
  simp only [Z,swap_stabilizer]

private theorem swap_U (v : Vertex F) :
    U (swapFamily F) (swapVertex F v) = U F v := by
  ext g
  change (∀ w ∈ ball (swapFamily F) (swapVertex F v) 1, g • w = w) ↔
    ∀ w ∈ ball F v 1, g • w = w
  constructor
  · intro hg w hw
    apply (swapVertexEquiv F).injective
    change swapVertex F (g • w) = swapVertex F w
    rw [swapVertex_smul]
    apply hg
    rcases (mem_ball_one F v w).mp hw with hw | hw
    · exact (mem_ball_one _ _ _).mpr (.inl ((swapGraphIso F).map_adj_iff.mpr hw))
    · exact (mem_ball_one _ _ _).mpr (.inr (congrArg (swapVertex F) hw))
  · intro hg w hw
    obtain ⟨w,rfl⟩ := (swapVertexEquiv F).surjective w
    change g • swapVertex F w = swapVertex F w
    rw [←swapVertex_smul]
    congr 1
    apply hg
    rcases (mem_ball_one _ _ _).mp hw with hw | hw
    · exact (mem_ball_one F v w).mpr (.inl ((swapGraphIso F).map_adj_iff.mp hw))
    · exact (mem_ball_one F v w).mpr (.inr ((swapVertexEquiv F).injective hw))


/-- Reorient the actual escape across the same critical base edge. -/
theorem critical_pair_swap
    (hc : IsCriticalPair (reducedFamily ![A,B] S)
      (base (reducedFamily ![A,B] S) true) (base (reducedFamily ![A,B] S) false))
    (hb : b (reducedFamily ![A,B] S) = 1) :
    IsCriticalPair (reducedFamily ![B,A] S)
      (base (reducedFamily ![B,A] S) false) (base (reducedFamily ![B,A] S) true) := by
  constructor
  · rw [Reduction.pair_b_swap A B S,hb,SimpleGraph.dist_eq_one_iff_adj]
    exact ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  · have hh := hc.2
    unfold reducedFamily
    rw [pair_G₀_swap A B S]
    rw [pair_family_swap]
    change ¬ Z (swapFamily (reducedFamily ![A,B] S))
      (swapVertex (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) true)) ≤
      U (swapFamily (reducedFamily ![A,B] S))
        (swapVertex (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) false))
    simpa only [swap_Z,swap_U] using hh

private theorem centers_commute_swap
    (hcomm : ⁅Z (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) false),
      Z (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) true)⁆ = ⊥) :
    ⁅Z (reducedFamily ![B,A] S) (base (reducedFamily ![B,A] S) false),
      Z (reducedFamily ![B,A] S) (base (reducedFamily ![B,A] S) true)⁆ = ⊥ := by
  unfold reducedFamily
  rw [pair_G₀_swap A B S]
  rw [pair_family_swap]
  change ⁅Z (swapFamily (reducedFamily ![A,B] S))
      (swapVertex (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) true)),
    Z (swapFamily (reducedFamily ![A,B] S))
      (swapVertex (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) false))⁆ = ⊥
  rw [swap_Z,swap_Z,commutator_comm]
  exact hcomm

/-- The full middle group and both subgroup inclusions are retained by the swap. -/
def reducedAmalgamSwap : Iso (reducedAmalgam ![A,B] S).reverse
    (reducedAmalgam ![B,A] S) where
  left := MulEquiv.subgroupCongr (by
    rw [pair_reducedSylow_swap]
    rfl)
  right := MulEquiv.subgroupCongr (by
    rw [pair_reducedSylow_swap]
    rfl)
  middle := MulEquiv.subgroupCongr (by
    rw [pair_reducedSylow_swap,pair_commonBorel_swap])
  left_commutes _ := rfl
  right_commutes _ := rfl


private theorem mapped_quotient_elementary {H : Type*} [Group H]
    (R N : Subgroup H) (hNR : N ≤ R) (f : H →* G) (hf : Function.Injective f)
    [(N.subgroupOf R).Normal]
    [((N.map f).subgroupOf (R.map f)).Normal]
    [IsElementaryAbelian 2 (R ⧸ N.subgroupOf R)] :
    IsElementaryAbelian 2 (R.map f ⧸ (N.map f).subgroupOf (R.map f)) := by
  let e := R.equivMapOfInjective f hf
  have hmap : (N.subgroupOf R).map e.toMonoidHom = (N.map f).subgroupOf (R.map f) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact mem_map_of_mem f hy
    · intro hx
      obtain ⟨y,hy,heq⟩ := hx
      exact ⟨⟨y,hNR hy⟩,hy,Subtype.ext heq⟩
  let eq := QuotientGroup.congr _ _ e hmap
  exact IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective

/-- The original linear beta factor supplies the literal full-Borel
quotient used in the elementary source branch. -/
theorem linear_beta_full_borel_elementary
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    {n : ℕ} (en : ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n)) :
    ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))) := by
  let F := reducedFamily L S
  let R := (stabilizer F (base F true) ⊓ stabilizer F (base F false)).pCoreIn 2
  let N := Q F (base F true)
  have hab : (graph F).Adj (base F true) (base F false) :=
    ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  let hn : (N.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer
    (((pCoreIn_le 2 _).trans inf_le_left).trans (stabilizer_normalizes_Q _ _))
  have hNR : N ≤ R := Noncommuting.graph_Q_le_edgeCore (reduced_triple h) hab
  obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := en
  let _ := fK
  let _ := finK
  let _ : Fintype K := Fintype.ofFinite K
  let _ : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  have eGraph : ClassicalGroup.IsPSL
      (graphLocalGroup F (base F true) ⧸ pCore 2 (graphLocalGroup F (base F true))) 2 (2^n) :=
    ⟨K,fK,finK,hK,⟨reduced_graphLinearQuotient h true eK⟩⟩
  obtain ⟨T,⟨e⟩⟩ := source_edge_core_quotient_sylow (hN := hn) (reduced_triple h)
    (reduced_borel_core_sylow h) (reducedFullEarlierLocalTheorems h) hab
  let : IsElementaryAbelian 2 T := linear_model_sylow_elementary eGraph T
  change (R ⧸ N.subgroupOf R) ≃* T at e
  let _ : IsElementaryAbelian 2 (R ⧸ N.subgroupOf R) :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hBG : B₀ L S ≤ G₀ L S :=
    (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left
  have hRG : twoCore (commonBorel L S) ≤ G₀ L S :=
    (show twoCore (commonBorel L S) ≤ B₀ L S from le_sup_right).trans hBG
  have hmap : R.map (G₀ L S).subtype = twoCore (commonBorel L S) := by
    dsimp only [R]
    rw [show stabilizer F (base F false) = F false from Subgroup.CosetGeometry.stabilizer_base _ _,
      show stabilizer F (base F true) = F true from Subgroup.CosetGeometry.stabilizer_base _ _,
      inf_comm (F true),show F false ⊓ F true = (B₀ L S).subgroupOf (G₀ L S) from
        (reduced_triple h).intersection,pCoreIn_subgroupOf 2 _ _ hBG,B₀_core h]
    exact map_subgroupOf_eq_of_le hRG
  have hNmap : N.map (G₀ L S).subtype =
      (parabolic L (reducedSylow L S) 1).pCoreIn 2 :=
    (NoncommutingProfile.reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
  have hnmap : ((N.map (G₀ L S).subtype).subgroupOf (R.map (G₀ L S).subtype)).Normal := by
    rw [hmap,hNmap]
    exact FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow
      (L := L) (S := reducedSylow L S) 1
  let _ := hnmap
  have he := mapped_quotient_elementary R N hNR (G₀ L S).subtype (G₀ L S).subtype_injective
  have hout : ∃ hn : ((N.map (G₀ L S).subtype).subgroupOf (R.map (G₀ L S).subtype)).Normal,
      letI := hn
      IsElementaryAbelian 2 (R.map (G₀ L S).subtype ⧸
        (N.map (G₀ L S).subtype).subgroupOf (R.map (G₀ L S).subtype)) := ⟨hnmap,he⟩
  rwa [hmap] at hout

private theorem linear_beta_nonbinary
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    {n : ℕ} (hn : 1 < n)
    (en : ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 (2^n)) :
    ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (G₀ L S).subtype ⧸ pCore 2
          ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
            (G₀ L S).subtype)) 2 2 := by
  intro eb
  obtain ⟨K,fK,finK,hK,⟨eK⟩⟩ := en
  let _ := fK
  let _ := finK
  let _ : Fintype K := Fintype.ofFinite K
  let _ : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  obtain ⟨F,fF,finF,hF,⟨eF⟩⟩ := eb
  let _ := fF
  let _ := finF
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card,pow_one] using hF)
  let a := (graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).equivMapOfInjective
    (G₀ L S).subtype (G₀ L S).subtype_injective
  let e := (reduced_graphLinearQuotient h true eK).symm.trans
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eF)
  let T : Sylow 2 PSL(2,K) := Classical.choice inferInstance
  let U := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hT : Nat.card T = Nat.card K :=
    (Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T).symm.toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have hU : Nat.card U = Nat.card F :=
    (Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive U).symm.toEquiv).trans
      (Nat.card_congr Multiplicative.toAdd)
  have he : Nat.card T = Nat.card U := Nat.card_congr
    ((T : Subgroup PSL(2,K)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  have hh : 2^n = 2^1 := by rw [←hK,←hT,he,hU,hF,pow_one]
  have := Nat.pow_right_injective (by decide : 1 < 2) hh
  omega

/-- When the critical alpha is the right endpoint, the original nonbinary
left linear marking supplies the entire elementary comparison, in reverse
orientation and with both original inclusion maps. -/
theorem reversed_linear_reduced_comparison
    (h : HypothesisF11 ![A,B] S)
    (hc : IsCriticalPair (reducedFamily ![A,B] S)
      (base (reducedFamily ![A,B] S) true) (base (reducedFamily ![A,B] S) false))
    (hb : b (reducedFamily ![A,B] S) = 1)
    (hcomm : ⁅Z (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) false),
      Z (reducedFamily ![A,B] S) (base (reducedFamily ![A,B] S) true)⁆ = ⊥)
    {n : ℕ} (hn : 1 < n) (en : ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 2 (2^n)) :
    ∃ (m : ℕ) (hm : 0 < m), Nonempty
      (Iso (reducedAmalgam ![A,B] S) (UnitaryFourNative.amalgam m hm true)) := by
  have hc' := critical_pair_swap A B S hc hb
  have hb' : b (reducedFamily ![B,A] S) = 1 := (pair_b_swap A B S).trans hb
  have hcomm' := centers_commute_swap A B S hcomm
  have helem := linear_beta_full_borel_elementary h.swap (n := n) en
  obtain ⟨m,hm,⟨e⟩⟩ := original_elementary_nonbinary_reduced_comparison
    h.swap hc' hb' hcomm' helem (linear_beta_nonbinary h.swap hn en)
  exact ⟨m,hm,⟨((reducedAmalgamSwap A B S).trans e).reverse⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile.ReversedElementary
