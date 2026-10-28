module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceReduction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceTransport
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LocalAction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.OddComplement
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.GeneralizedFitting.Solvable
public import Theory.GroupAction.ElementaryTwoCyclicFixed
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.InvolutionCentralizers

/-!
# The actual noncyclic Fitting-offender reduction

A noncyclic minimum cubic actor on a faithful binary module is faithful on
O₃. The SQTK cover bounds its involution centralizers; the coprime actor
lemma then gives order four and a trivial common centralizer. The source
hyperplane-support argument, including its Frattini exclusion, proves the
three-core elementary. The complementary odd cores force the actor to fix
C_V(O₃), so the literal action of O₃A on [V,O₃] is faithful and remains starred.

`source_reduced` constructs all inputs of the existing reduced classification.
`source_configurations` gives its actual product factors and support planes.
`source_ratio_and_noncyclic` transports the ratio back to the original action
and excludes every cyclic starred actor, proving D.2.19 without a global
indecomposable classification assumption.

Source: Aschbacher–Smith, D.2.14 and D.2.19, printed pp.185–188.
The structural inputs F*=F, O₂=1 and V=[V,F] are the actual D.2.17 hypotheses;
the final wrapper discharges F*=F for the solvable Section 15.1 action.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.SourceReduction
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open ElementaryCore.SupportExclusion FittingConfigurations
open scoped ENNReal
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

def localMoved (P A : Subgroup G) [P.Normal] :
    Subrepresentation (ρ.comp (P ⊔ A).subtype) where
  toSubmodule := subspaceCommutator ρ ⊤ P
  apply_mem_toSubmodule g := fun _ hw =>
    (moved_stable ρ P (P ⊔ A) le_normalizer_of_normal g.property _).mpr hw

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem subrepresentation_faithful_of_fixed_complement
    (hf : Function.Injective ρ) (W : Subrepresentation ρ)
    (hs : W.toSubmodule ⊔ fixedSpace ρ ⊤ = ⊤) :
    Function.Injective W.toRepresentation := by
  intro a b he
  apply hf
  ext v
  obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ W.toSubmodule ⊔ fixedSpace ρ ⊤ from hs ▸ Submodule.mem_top)
  have hwab : ρ a w = ρ b w := congrArg Subtype.val
    (DFunLike.congr_fun he (⟨w, hw⟩ : W))
  have hza : ρ a z = z := hz ⟨a,mem_top a⟩
  have hzb : ρ b z = z := hz ⟨b,mem_top b⟩
  simp only [map_add, hwab, hza, hzb]

omit [FiniteDimensional (ZMod 2) V] in
theorem localMoved_fixed_complement (P A : Subgroup G) [P.Normal]
    (hp : Odd (Nat.card P)) (hfix : fixedSpace ρ P ≤ fixedSpace ρ A) :
    (localMoved ρ P A).toSubmodule ⊔ fixedSpace (ρ.comp (P ⊔ A).subtype) ⊤ = ⊤ := by
  have hf : fixedSpace ρ P ≤ fixedSpace (ρ.comp (P ⊔ A).subtype) ⊤ := by
    intro v hv g
    obtain ⟨p,hpP,a,haA,hpa⟩ := Subgroup.mem_sup_of_normal_left.mp g.val.property
    change ρ (g.val : G) v = v
    have hpv : ρ p v = v := hv ⟨p,hpP⟩
    have hav : ρ a v = v := hfix hv ⟨a,haA⟩
    rw [← hpa, map_mul, Module.End.mul_apply, hav, hpv]
  apply top_unique
  rw [← (moved_split ρ P hp).symm.sup_eq_top]
  exact sup_le_sup_left hf _

omit [FiniteDimensional (ZMod 2) V] in
theorem localMoved_full (P A : Subgroup G) [P.Normal]
    (hp : Odd (Nat.card P)) :
    subspaceCommutator (localMoved ρ P A).toRepresentation ⊤
      (P.subgroupOf (P ⊔ A)) = ⊤ := by
  let L := P ⊔ A
  let W := localMoved ρ P A
  let U := subspaceCommutator ρ ⊤ P
  have hU : subspaceCommutator ρ U P = U := by
    apply le_antisymm (subspaceCommutator_le_of_invariant ρ
      (moved_stable ρ P P P.le_normalizer))
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hpP, v, _, rfl⟩
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ U ⊔ fixedSpace ρ P from (moved_split ρ P hp).symm.sup_eq_top ▸ Submodule.mem_top)
    have he : ρ p (w + z) - (w + z) = ρ p w - w := by
      rw [map_add, show ρ p z = z from hz ⟨p,hpP⟩]
      abel
    rw [he]
    exact Submodule.subset_span ⟨p,hpP,w,hw,rfl⟩
  apply Submodule.map_injective_of_injective W.toSubmodule.subtype_injective
  have he := subspaceCommutator_map_embedding (ρ.comp L.subtype) W.toRepresentation
    (MonoidHom.id L) W.toSubmodule.subtype (fun _ _ => rfl)
    (P.subgroupOf L) ⊤
  simp only [Subgroup.map_id, Submodule.map_top, Submodule.range_subtype] at he ⊢
  rw [← he, subspaceCommutator_comp_map, map_subgroupOf_eq_of_le le_sup_left]
  exact hU

omit [Finite G] in
theorem local_threeCore (P A : Subgroup G) [P.Normal]
    (hP : IsPGroup 3 P) (hA : IsPGroup 2 A) :
    pCore 3 (P ⊔ A : Subgroup G) = P.subgroupOf (P ⊔ A) := by
  let L := P ⊔ A
  let P₀ := P.subgroupOf L
  let A₀ := A.subgroupOf L
  have hgen : P₀ ⊔ A₀ = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hq : IsPGroup 2 (L ⧸ P₀) := quotient_isPGroup_of_sup_eq_top A₀ P₀
    hA.comap_subtype (sup_comm P₀ A₀ ▸ hgen)
  have hm : (pCore 3 L).map (QuotientGroup.mk' P₀) = ⊥ := by
    have hdis := IsPGroup.disjoint_of_coprime
      (pCore_isPGroup.map (QuotientGroup.mk' P₀))
      (hq.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
    simpa using hdis.eq_bot
  apply le_antisymm
  · simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hm
  · exact le_sSup ⟨inferInstance, hP.comap_subtype⟩

theorem fixed_complement_and_reduced_of_four
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤)
    (hcard : Nat.card A = 4)
    (hfix : pCore 3 G ⊓ centralizer (A : Set G) = ⊥) :
    fixedSpace ρ (pCore 3 G) ≤ fixedSpace ρ A ∧
    ∃ s : ℕ, Reduced (localMoved ρ (pCore 3 G) A).toRepresentation
      ((pCore 3 G).subgroupOf (pCore 3 G ⊔ A)) (A.subgroupOf (pCore 3 G ⊔ A)) s := by
  let P := pCore 3 G
  let L := P ⊔ A
  let P₀ := P.subgroupOf L
  let A₀ := A.subgroupOf L
  let W := localMoved ρ P A
  let σ := W.toRepresentation
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hr : 1 < rank A := by simp only [rank, hcard]; decide
  have hfaith := actor_faithful_three ρ hf hA hr hF hcore
  have hsupport := source_lemma_D_2_14_hyperplaneSupport ρ hf hA hcard hfix
  obtain ⟨hElem, ⟨s, hs, hcP, _⟩, hcomm⟩ :=
    ElementaryCore.elementary_structure_of_hyperplaneSupport ρ hf P A pCore_isPGroup
      hcard le_normalizer_of_normal hfaith hfix hsupport
  let : IsElementaryAbelian 3 P := hElem
  let : (oddComplement G).Normal := by unfold oddComplement; infer_instance
  have hcQ := complement_coprime hcore
  have hPQ : ⁅P,oddComplement G⁆ = ⊥ := by
    have hd : Disjoint P (oddComplement G) := by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
      apply disjoint_of_coprime_natCard
      rw [hn]
      exact hcQ.coprime_dvd_right (by decide : 3 ∣ 6) |>.symm.pow_left n
    exact le_bot_iff.mp ((commutator_le_inf P (oddComplement G)).trans hd.le_bot)
  have hQA : ⁅oddComplement G,A⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (complement_centralizes ρ hf hA hr hcore)
  have hcomp : fixedSpace ρ P ≤ fixedSpace ρ A :=
    (subspaceCommutator_eq_bot_iff _ _ _).mp
      (source_lemma_D_2_14_fixed_complement_of_odd_complement ρ hf hA hcard
        (oddComplement G) hElem hcP hs hfaith hfix hcomm hcQ hPQ hQA
        (fitting_eq_three_sup_complement (G := G) ▸ hmoved))
  have hodd : Odd (Nat.card P) := hcP ▸ (by decide : Odd 3).pow
  have hspan := localMoved_fixed_complement ρ P A hodd hcomp
  have hσ : Function.Injective σ :=
    subrepresentation_faithful_of_fixed_complement (ρ.comp L.subtype)
      (hf.comp L.subtype_injective) W hspan
  have hstar : A₀ ∈ QhatStar σ := fixed_complement_starred (ρ.comp L.subtype) W hspan
    (starred_subgroupOf ρ hA le_sup_right)
  have hcA : Nat.card A₀ = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show A ≤ L from le_sup_right)).toEquiv).trans hcard
  have hcore' : pCore 3 L = P₀ := local_threeCore P A pCore_isPGroup
    (IsElementaryAbelian.isPGroup 2 A)
  have hfaith' : A₀ ⊓ centralizer (P₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨ha.1, ?_⟩
    intro p hp
    exact congrArg Subtype.val (ha.2 ⟨p,(le_sup_left : P ≤ L) hp⟩ hp)
  have hfix' : P₀ ⊓ centralizer (A₀ : Set L) = ⊥ := by
    apply le_bot_iff.mp
    intro p hp
    apply Subtype.ext
    apply hfix.le
    refine ⟨hp.1, ?_⟩
    intro a ha
    exact congrArg Subtype.val (hp.2 ⟨a,(le_sup_right : A ≤ L) ha⟩ ha)
  refine ⟨hcomp, s, ⟨hσ, inferInstance, IsElementaryAbelian.subgroupOf le_sup_left,
    ?_, hs, hcA, hstar, ?_, hfaith', hfix', ?_, localMoved_full ρ P A hodd, ?_⟩⟩
  · exact (Nat.card_congr (subgroupOfEquivOfLe (show P ≤ L from le_sup_left)).toEquiv).trans hcP
  · rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  · apply Subgroup.map_injective L.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le le_sup_left,
      map_subgroupOf_eq_of_le le_sup_right, hcomm]
  · have hf' : pCore 3 L ⊓ centralizer (A₀ : Set L) = ⊥ := hcore'.symm ▸ hfix'
    have hh := source_lemma_D_2_14_hyperplaneSupport σ hσ hstar hcA hf'
    rw [hcore'] at hh
    exact hh

theorem actor_four_and_common_centralizer
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥) :
    Nat.card A = 4 ∧ pCore 3 G ⊓ centralizer (A : Set G) = ⊥ := by
  let P := pCore 3 G
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let α : A →* MulAut P := (MulAut.conjNormal : G →* MulAut P).comp A.subtype
  have hfaith := actor_faithful_three ρ hf hA hr hF hcore
  have hα : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply le_bot_iff.mp
    intro a ha
    apply Subtype.ext
    apply hfaith.le
    refine ⟨a.property, ?_⟩
    intro p hp
    have he := congrArg (fun β : MulAut P => (β ⟨p,hp⟩ : G)) ha
    change (a : G) * p * (a : G)⁻¹ = p at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hcyc (a : A) (ha : a ≠ 1) : IsCyclic (α a).fixedSubgroup := by
    let C := P ⊓ centralizer ({(a : G)} : Set G)
    have hao : orderOf (a : G) = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
      (fun he => ha (Subtype.ext he))
    have han : (a : G) ∉ centralizer (P : Set G) := by
      intro hc
      exact ha (Subtype.ext (hfaith.le ⟨a.property,hc⟩))
    let : IsCyclic C := cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
      (by decide : Odd 3) f honto (hH.stronglyQuasithin 3 (by decide) (by decide))
      P pCore_isPGroup a hao han C (pCore_isPGroup.to_le inf_le_left) inf_le_right
    let j : (α a).fixedSubgroup →* C :=
      { toFun x := ⟨x.val.val, x.val.property, by
          apply mem_centralizer_singleton_iff.mpr
          have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
          change (a : G) * (x.val : G) * (a : G)⁻¹ = (x.val : G) at he
          exact (mul_inv_eq_iff_eq_mul.mp he).symm⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
    exact isCyclic_of_injective j (fun x y h => by
      have he : (j x : G) = (j y : G) := congrArg (fun c : C => (c : G)) h
      exact Subtype.ext (Subtype.ext he))
  have hlarge : 2 < Nat.card A := by
    rw [hA.1.2.1.card_eq_two_pow_rank]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) hr
  obtain ⟨hc,hfix⟩ := ElementaryTwoCyclicFixed.card_eq_four_and_common_fixed_eq_one
    pCore_isPGroup α hα hcyc hlarge
  refine ⟨hc, le_bot_iff.mp ?_⟩
  intro p hp
  exact congrArg Subtype.val (hfix (⟨p,hp.1⟩ : P) (fun a => by
    apply Subtype.ext
    change (a : G) * p * (a : G)⁻¹ = p
    rw [hp.2 a a.property, mul_inv_cancel_right]))

/-- The actual noncyclic source actor constructs the reduced configuration
on PA and its original moved module. -/
theorem source_reduced
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    ∃ s : ℕ, Reduced (localMoved ρ (pCore 3 G) A).toRepresentation
      ((pCore 3 G).subgroupOf (pCore 3 G ⊔ A)) (A.subgroupOf (pCore 3 G ⊔ A)) s := by
  obtain ⟨hcard,hfix⟩ := actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore
  exact (fixed_complement_and_reduced_of_four ρ hf hA hF hcore hmoved hcard hfix).2

theorem source_configurations
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    ∃ s : ℕ, ∃ d : SupportFactors (localMoved ρ (pCore 3 G) A).toRepresentation
      ((pCore 3 G).subgroupOf (pCore 3 G ⊔ A)) s,
      d.Alternatives (A.subgroupOf (pCore 3 G ⊔ A)) ∧
      fixedCodim (localMoved ρ (pCore 3 G) A).toRepresentation
        (A.subgroupOf (pCore 3 G ⊔ A)) = 3 ∧
      cubicRatio (localMoved ρ (pCore 3 G) A).toRepresentation = 3 / 2 := by
  obtain ⟨s,hs⟩ := source_reduced ρ hH f honto hf hA hr hF hcore hmoved
  exact ⟨s, hs.configurations _⟩

/-- D.2.14(6) and D.2.19 on the original representation. -/
theorem source_ratio_and_noncyclic
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A)
    (hF : generalizedFitting G = fittingSubgroup G) (hcore : pCore 2 G = ⊥)
    (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 ∧
      ∀ B ∈ QhatStar ρ, 1 < rank B := by
  obtain ⟨hcard,hfix⟩ := actor_four_and_common_centralizer ρ hH f honto hf hA hr hF hcore
  obtain ⟨hcomp,s,hs⟩ :=
    fixed_complement_and_reduced_of_four ρ hf hA hF hcore hmoved hcard hfix
  let P := pCore 3 G
  let L := P ⊔ A
  let W := localMoved ρ P A
  let A₀ := A.subgroupOf L
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
    exact hn ▸ (by decide : Odd 3).pow
  have hspan := localMoved_fixed_complement ρ P A hodd hcomp
  have hcodim : fixedCodim W.toRepresentation A₀ = fixedCodim ρ A := by
    rw [← fixedCodim_subgroupOf ρ (show A ≤ L from le_sup_right)]
    apply (fixedCodim_subrepresentation_eq_iff (ρ.comp L.subtype) W A₀).mpr
    apply top_unique
    rw [← hspan]
    exact sup_le_sup_left (fixedSpace_antitone _ le_top) _
  obtain ⟨d,hd,hc,hratio⟩ := hs.configurations _
  have hrho : cubicRatio ρ = 3 / 2 := by
    calc
      _ = actionRatio ρ A := hA.1.2.2.2.symm
      _ = actionRatio W.toRepresentation A₀ := by
        rw [actionRatio, actionRatio, hcodim,
          show rank A₀ = rank A from rank_subgroupOf (show A ≤ L from le_sup_right)]
      _ = cubicRatio W.toRepresentation := hs.starred.1.2.2.2
      _ = 3 / 2 := hratio
  refine ⟨hcodim ▸ hc, hrho, ?_⟩
  intro B hB
  have hp := hB.1.2.1.rank_pos
  by_contra hn
  have he : rank B = 1 := by omega
  rcases QhatStar.ratio_one_or_two_of_rank_one ρ hf hB he with h | h <;>
    rw [hrho] at h <;>
    have hreal := congrArg ENNReal.toReal h <;> norm_num at hreal

/-- Application to a faithful solvable action, as in the selected normalizer
quotient in the original Section 15.1 argument. -/
theorem solvable_source_ratio_and_noncyclic [Group.IsSolvable G]
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : 1 < rank A) (hcore : pCore 2 G = ⊥)
    (hmoved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤) :
    fixedCodim ρ A = 3 ∧ cubicRatio ρ = 3 / 2 ∧
      ∀ B ∈ QhatStar ρ, 1 < rank B :=
  source_ratio_and_noncyclic ρ hH f honto hf hA hr
    (generalizedFitting_eq_fitting_of_solvable G) hcore hmoved

end CFSG.Quasithin.ChapterD.SourceReduction
