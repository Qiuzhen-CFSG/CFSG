module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.ResidualFitting
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.FixedComplementSource
public import Theory.Representation.BinaryOffender.ProjectedSeed

/-!
# A residual cubic mover from the projected generating seed

A nontrivial involution normalizing every canonical cubic factor cannot
centralize the original Fitting image on the canonical fixed complement.
Centrality on the complementary prime cores therefore supplies a noncommuting
three-core element. Its commutator with the involution is inverted and still
moves that same fixed complement.

The source fixed-complement conclusion is proved first with the literal
residual image's trivial two-core as an explicit input. A Sylow-fixed
orbit-generating seed for the acting group supplies this input by equivariant
coprime projection. The source consumer therefore replaces full Fitting
movement by solvability and that seed, without changing the original action.
When the seed belongs to a larger ambient group, the residual two-core input
must instead be transported through its normal subgroup image.

Source: Aschbacher--Smith D.2.25, printed p.190, as used in original 15.1.2,
printed pp.1084–1085.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
  [MulDistribMulAction G V] [IsElementaryAbelian 2 V] [FaithfulSMul G V]

theorem residual_threeCore_inverted_mover
    (hsplit : FixedPoints.subgroup (smallSupportGroup G V 1) V ⊔
      commutatorAction (smallSupportGroup G V 1) V = ⊤)
    {D : Type*} [Group D] [Finite D] [Group.IsSolvable D]
    (f : G →* D) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → ∀ v ∈ FixedPoints.subgroup (smallSupportGroup G V 1) V,
      x • v = v) (hcore : pCore 2 D=⊥)
    {t : G} (ht : t ∈ factorNormalizer (G:=G) (V:=V))
    (ht2 : t^2=1) (htn : f t≠1)
    (hcomp : t ∈ centralizer (SourceReduction.oddComplement G : Set G)) :
    ∃ x ∈ pCore 3 G, t*x*t⁻¹=x⁻¹ ∧ f x≠1 := by
  have hnot := residual_factorNormalizer_involution_not_centralizer
    hsplit f hf hker hcore ht ht2 htn
  have hp : ∃ p ∈ pCore 3 G, ¬ Commute (f t) (f p) := by
    by_contra! hn
    apply hnot
    apply mem_centralizer_iff.mpr
    rintro _ ⟨g,hg,rfl⟩
    rw [SourceReduction.fitting_eq_three_sup_complement] at hg
    obtain ⟨p,hp,q,hq,rfl⟩ := mem_sup_of_normal_left.mp hg
    rw [map_mul]
    apply Commute.symm
    apply (hn p hp).mul_right
    change f t*f q=f q*f t
    rw [←map_mul,←map_mul,hcomp q hq]
  obtain ⟨p,hp,hnp⟩ := hp
  let x := t*p*t⁻¹*p⁻¹
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ht2)
  refine ⟨x,(pCore 3 G).mul_mem ((inferInstance : (pCore 3 G).Normal).conj_mem p hp t)
    ((pCore 3 G).inv_mem hp),?_,?_⟩
  · dsimp [x]
    simp only [mul_inv_rev,inv_inv,hti]
    group
    simp only [show t*t=1 from by simpa only [pow_two] using ht2,one_mul]
  · intro hfx
    apply hnp
    change f t*f p=f p*f t
    rw [←map_mul,←map_mul]
    have hprod : x*(p*t)=t*p := by dsimp [x]; group
    rw [←hprod,map_mul,hfx,one_mul]
end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree

namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem residual_inverted_mover_of_twoCore (hfaith : Function.Injective ρ)
    (t : G) (ht : IsInvolution t)
    (hcomp : t ∈ centralizer (SourceReduction.oddComplement G : Set G)) :
    letI := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    pCore 2 (subspaceActionImage ρ (fixedSpace ρ Y))=⊥ →
    IsCompl (commutatorAction Y (Multiplicative V))
      (FixedPoints.subgroup Y (Multiplicative V)) →
    Nat.card (commutatorAction (zpowers t) (Multiplicative V))=4 →
    (∃ v ∈ fixedSpace ρ Y, ρ t v≠v) →
    ∃ x ∈ pCore 3 G, t*x*t⁻¹=x⁻¹ ∧ ∃ v ∈ fixedSpace ρ Y,ρ x v≠v := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ hfaith
  let Y := smallSupportGroup G (Multiplicative V) 1
  dsimp only
  intro hcore hsplit hcard hmove
  let U := fixedSpace ρ Y
  let f := invariantActionHom ρ U (fixedSpace_stable_of_normal ρ Y)
  have hf : Function.Surjective f := invariantActionHom_surjective ρ U _
  let : Group.IsSolvable (subspaceActionImage ρ U) := Group.isSolvable_of_surjective hf
  have hker (x : G) (hx : f x=1) (v : Multiplicative V)
      (hv : v ∈ FixedPoints.subgroup Y (Multiplicative V)) : x • v=v := by
    have he := congrArg (fun d => subspaceImageRepresentation ρ U d ⟨v.toAdd,hv⟩) hx
    exact congrArg Multiplicative.ofAdd (congrArg Subtype.val he)
  have hnorm : t ∈ SmallThree.factorNormalizer (G:=G) (V:=Multiplicative V) := by
    rw [SmallThree.mem_factorNormalizer_iff]
    by_contra hn
    have htfix := SmallThree.fixed_complement_of_transposition t ht hcard hsplit hn
    obtain ⟨v,hv,hm⟩ := hmove
    exact hm (congrArg Multiplicative.toAdd (htfix (Multiplicative.ofAdd v) hv))
  have htn : f t≠1 := by
    intro he
    obtain ⟨v,hv,hm⟩ := hmove
    exact hm (congrArg Multiplicative.toAdd (hker t he (Multiplicative.ofAdd v) hv))
  obtain ⟨x,hx,hi,hnx⟩ := SmallThree.residual_threeCore_inverted_mover
    hsplit.symm.sup_eq_top f hf hker hcore hnorm ht.2 htn hcomp
  refine ⟨x,hx,hi,?_⟩
  by_contra! hn
  apply hnx
  apply subspaceImageRepresentation_injective ρ U
  ext v
  exact hn v.val v.property
theorem seeded_residual_inverted_mover (hfaith : Function.Injective ρ)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w}=⊤)
    (t : G) (ht : IsInvolution t)
    (hcomp : t ∈ centralizer (SourceReduction.oddComplement G : Set G)) :
    letI := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    Odd (Nat.card Y) →
    IsCompl (commutatorAction Y (Multiplicative V))
      (FixedPoints.subgroup Y (Multiplicative V)) →
    Nat.card (commutatorAction (zpowers t) (Multiplicative V))=4 →
    (∃ v ∈ fixedSpace ρ Y, ρ t v≠v) →
    ∃ x ∈ pCore 3 G, t*x*t⁻¹=x⁻¹ ∧ ∃ v ∈ fixedSpace ρ Y,ρ x v≠v := by
  let := BinaryGroupAction.action ρ
  dsimp only
  intro hodd hsplit hcard hmove
  exact residual_inverted_mover_of_twoCore ρ hfaith t ht hcomp
    (normalOddFixedImage_twoCore ρ _ hodd S Z hfix hspan) hsplit hcard hmove

/-- The source D.2.25 fixed-complement step, from the original cyclic
hypotheses. Every small-support involution not centralizing the canonical
three-group fixes its fixed subspace pointwise. -/
theorem CoreHypotheses.fixed_smallThree_complement_of_residual_twoCore
    (h : CoreHypotheses ρ)
    (hfive : ∀ A∈QhatStar ρ,⁅pCore 5 G,A⁆=⊥)
    (hq : cubicRatio ρ=2) {t : G} (ht : t∈smallSupportInvolutions ρ) :
    letI := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    pCore 2 (subspaceActionImage ρ (fixedSpace ρ Y))=⊥ →
    t∉centralizer (Y:Set G) → fixedSpace ρ Y ≤ fixedSpace ρ (zpowers t) := by
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  change pCore 2 (subspaceActionImage ρ (fixedSpace ρ Y))=⊥ →
    t∉centralizer (Y:Set G) → fixedSpace ρ Y ≤ fixedSpace ρ (zpowers t)
  intro hres hnc
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  have hti : IsInvolution t := by
    refine ⟨?_,?_⟩
    · intro he
      have hh := ht.1
      rw [he,orderOf_one] at hh
      omega
    · rw [←ht.1]
      exact pow_orderOf_eq_one t
  have hfour : Nat.card (commutatorAction (zpowers t) (Multiplicative V))=4 := by
    rw [BinaryGroupAction.commutator_card,Representation.CyclicFixedRank.commutator_eq_range,
      ←fixedCodim_zpowers_eq_displacement_rank,(h.smallSupport_starred hq ht).2]
    norm_num
  have hYodd : Odd (Nat.card Y) :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot h.twoCore).of_dvd_nat
      (Subgroup.card_dvd_of_le (smallSupportGroup_le_fitting G (Multiplicative V) 1))
  have hcop : Nat.Coprime (Nat.card Y) (Nat.card (Multiplicative V)) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (Multiplicative V)).exists_card_eq
    rw [hn]
    exact hYodd.coprime_two_right.pow_right n
  have hsplit := (ActionSupport.fixed_support_isCompl Y hcop).symm
  have hnc' : ¬ ∀y∈Y,Commute t y := by
    intro hh
    apply hnc
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hh y hy).symm.eq)
  have hf := SmallThree.fixed_complement_of_residual_witness
    (V:=Multiplicative V) t hti hfour hsplit hnc' ?_
  · intro v hv
    rw [mem_fixedSpace_zpowers_iff]
    exact congrArg Multiplicative.toAdd (hf (Multiplicative.ofAdd v) hv)
  · intro hline
    let W := normalFixed ρ Y
    have hcard := BinaryGroupAction.subrepresentation_commutator_card ρ W (zpowers t)
    have hr : Module.finrank (ZMod 2) (W.toRepresentation t - 1).range=1 := by
      have he : 2 ^ Module.finrank (ZMod 2)
          (subspaceCommutator W.toRepresentation ⊤ (zpowers t))=2^1 :=
        hcard.symm.trans hline
      have hd := Nat.pow_right_injective (by decide : 2≤2) he
      rw [Representation.CyclicFixedRank.commutator_eq_range] at hd
      exact hd
    have hmove : ∃ v ∈ fixedSpace ρ Y,ρ t v≠v := by
      by_contra! hn
      have he : W.toRepresentation t=1 := by
        ext v
        exact hn v.val v.property
      rw [he,sub_self,LinearMap.range_zero,finrank_bot] at hr
      exact Nat.zero_ne_one hr
    obtain ⟨x,hx,hi,v,hv,hm⟩ := residual_inverted_mover_of_twoCore ρ h.faithful
      t hti (h.complement_central hfive (mem_top t)) hres hsplit hfour hmove
    refine ⟨x,hx,hi,Multiplicative.ofAdd v,hv,?_⟩
    intro he
    exact hm (congrArg Multiplicative.toAdd he)

theorem CoreHypotheses.fixed_smallThree_complement_of_seed
    (h : CoreHypotheses ρ)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hfix : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w}=⊤)
    (hfive : ∀ A∈QhatStar ρ,⁅pCore 5 G,A⁆=⊥)
    (hq : cubicRatio ρ=2) {t : G} (ht : t∈smallSupportInvolutions ρ) :
    letI := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    t∉centralizer (Y:Set G) → fixedSpace ρ Y ≤ fixedSpace ρ (zpowers t) := by
  let := BinaryGroupAction.action ρ
  let Y := smallSupportGroup G (Multiplicative V) 1
  have hodd : Odd (Nat.card Y) :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot h.twoCore).of_dvd_nat
      (Subgroup.card_dvd_of_le (smallSupportGroup_le_fitting G (Multiplicative V) 1))
  exact h.fixed_smallThree_complement_of_residual_twoCore ρ hfive hq ht
    (normalOddFixedImage_twoCore ρ Y hodd S Z hfix hspan)
end CFSG.Quasithin.ChapterD.CyclicSource
