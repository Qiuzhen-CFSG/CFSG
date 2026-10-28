module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourFaithfulExclusion
public import Theory.Representation.BinaryOffender.KernelQuotient
public import Theory.Representation.BinaryOffender.QuasisimpleImage
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.Quasithin.NormalTwoQuotient

/-!
# A rank-one quadratic actor on the residual PSL₃(4)

A quadratic actor with fixed codimension at most twice its rank cannot
supplement a normal PSL₃(4) subgroup if it meets the component centralizer
trivially. An irreducible section detecting the component retains the actor
faithfully; its kernel is a two-group, so the SQTK bound survives the passage
to the faithful image. The PSL₃(4) chief-action exclusion gives a contradiction.

For an actor of rank one, the centralizer intersection is either trivial or
the whole actor. Consequently such an actor with fixed codimension at most
two centralizes the component. The Chapter 12 application uses the opposite
image in the original centralizer-span action. It does not assume that the
whole span-action group has strongly quasithin quotients.

Source: Aschbacher--Smith B.4.2--5 and 5.1.23, printed pp.86--87,645--646,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory CFSG.Quasithin
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {κ : GroupClass.{u}}

private theorem exclude_supplement
    (ρ : Representation (ZMod 2) G V) (L A : Subgroup G) [L.Normal]
    (hsq : IsSQTK κ G) (hm : ClassicalGroup.IsPSL L 3 4)
    (hgen : L ⊔ A = ⊤) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (L : Set G) = ⊥) (hn : ¬ L ≤ ρ.ker) : False := by
  obtain ⟨hqs,hz,_⟩ := ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm
  let : IsQuasisimple L := hqs
  let : IsSimpleGroup (L ⧸ center L) := hqs.simple
  let : IsSimpleGroup L :=
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm).isSimpleGroup
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨U,N,hi,hnN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect L hn
  let σ := N.quotientRepresentation
  let Q := KernelQuotient.Actor σ
  let π := KernelQuotient.projection σ
  let τ := KernelQuotient.action σ
  have hπ : Function.Surjective π := KernelQuotient.projection_surjective σ
  have hcomp : τ.comp π = σ := rfl
  have hLne : L.map π ≠ ⊥ := by
    intro hb
    apply hnN
    have hh := (map_eq_bot_iff L).mp hb
    intro x hx
    exact LinearMap.ext (fun v => by
      have hv := congrArg (fun q => τ q v) (show π x = 1 from hh hx)
      change σ x v = (τ 1) v at hv
      simpa only [map_one, Module.End.one_apply] using hv)
  have hLc : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal,hqs⟩
  have hcent := hLc.centralizer_comap_of_map_ne_bot π hLne
  have hAf : Function.Injective (π.comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    have hc : (a : G) ∈ centralizer (L : Set G) := by
      rw [← hcent]
      change π a ∈ centralizer (L.map π : Set Q)
      rw [show π a = 1 from ha]
      exact one_mem _
    exact mem_bot.mp (hAC ▸ (show (a : G) ∈ A ⊓ centralizer (L : Set G) from ⟨a.property,hc⟩))
  have hLf : Function.Injective (π.comp L.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π.comp L.subtype).ker inferInstance with hb | ht
    · exact hb
    · exfalso
      apply hLne
      apply (map_eq_bot_iff L).mpr
      intro l hl
      exact show (⟨l,hl⟩ : L) ∈ (π.comp L.subtype).ker from ht ▸ mem_top _
  have hker : IsPGroup 2 π.ker := π.kernel_isPGroup_of_normal_supplement L A
    (IsElementaryAbelian.isPGroup 2 A) hgen (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr hLf]
      exact IsPGroup.of_bot)
  have hsqQ : IsSQTK κ Q := by
    refine ⟨?_,hsq.isKGroup.of_surjective π hπ⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have hk : IsPGroup 2 (actionHom σ).ker := by
      exact hker.of_equiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _))
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ hk).trans
      (hsq.stronglyQuasithin p hp ho)
  let eL : L ≃* L.map π := MulEquiv.ofBijective (π.subgroupMap L)
    ⟨fun x y he => hLf (congrArg Subtype.val he),π.subgroupMap_surjective L⟩
  let eA : A ≃* A.map π := MulEquiv.ofBijective (π.subgroupMap A)
    ⟨fun x y he => hAf (congrArg Subtype.val he),π.subgroupMap_surjective A⟩
  have hmQ : ClassicalGroup.IsPSL (L.map π) 3 4 := hm.of_mulEquiv eL.symm
  let : (L.map π).Normal := Normal.map inferInstance π hπ
  have hquot : IsPGroup 2 (Q ⧸ L.map π) :=
    quotient_isPGroup_of_sup_eq_top (A.map π) (L.map π)
      ((IsElementaryAbelian.isPGroup 2 A).map π) (by
        rw [← Subgroup.map_sup, sup_comm A L, hgen, map_top_of_surjective _ hπ])
  have hiQ : IsIrreducible τ := (irreducible_comp_surjective_iff π hπ τ).mp hi
  let := hiQ
  have hcore : pCore 2 Q = ⊥ := QuadraticFourGroup.twoCore_eq_bot_of_faithful_irreducible
    τ (KernelQuotient.faithful σ)
  have hqN : IsQuadratic σ A := quadratic_of_equivariant_surjection U.toRepresentation σ
    N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ U hq)
  have hqQ : IsQuadratic τ (A.map π) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
    exact hqN a ha b hb v
  have hAQ : IsElementaryTwo (A.map π) := by
    refine ⟨?_,IsElementaryAbelian.map π⟩
    intro hb
    have hc := Nat.card_congr eA.toEquiv
    rw [hb] at hc
    exact hA.1 (Subgroup.eq_bot_of_card_eq A (by simpa using hc))
  have hr : rank (A.map π) = rank A := congrArg (Nat.log 2) (Nat.card_congr eA.toEquiv).symm
  have hdQ : fixedCodim τ (A.map π) ≤ 2 * rank (A.map π) := by
    rw [hr, ← fixedCodim_map_equivariant σ τ π (LinearEquiv.refl (ZMod 2) _)
      (fun _ _ => rfl)]
    have hdU := fixedCodim_subrepresentation_le ρ U A
    have hdN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    change fixedCodim N.quotientRepresentation A ≤ _
    omega
  exact not_le_of_gt (ChapterK.Linear.Recognition.PSL3FourExclusion.quadraticRatio_gt_two_of_irreducible
    hsqQ hmQ hquot hcore (KernelQuotient.faithful σ) hiQ)
      ((quadraticRatio_le_two_iff τ).mpr ⟨A.map π,hAQ,hqQ,hdQ⟩)

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape

/-- A faithful quadratic involution of fixed codimension at most two centralizes
this same normal PSL₃(4), without requiring irreducibility of the full module. -/
theorem rank_one_quadratic_centralizes_residual
    (ρ : Representation (ZMod 2) G V) (L A : Subgroup G) [L.Normal]
    (hLsq : IsSQTK κ L) (hkg : IsKGroup κ G) (hm : ClassicalGroup.IsPSL L 3 4)
    (hf : Function.Injective ρ) (hA : IsElementaryTwo A) (hr : rank A = 1)
    (hq : IsQuadratic ρ A) (hd : fixedCodim ρ A ≤ 2) :
    A ≤ centralizer (L : Set G) := by
  classical
  by_contra hnot
  have hcard : Nat.card A = 2 := by rw [hA.card_eq_two_pow_rank,hr]; rfl
  let : Fact (Nat.card A).Prime := ⟨hcard ▸ Nat.prime_two⟩
  have hAC : A ⊓ centralizer (L : Set G) = ⊥ := by
    rcases ((centralizer (L : Set G)).subgroupOf A).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply bot_unique
      rintro a ⟨ha,hc⟩
      have ha' : (⟨a,ha⟩ : A) ∈ (centralizer (L : Set G)).subgroupOf A := hc
      rw [hb,mem_bot] at ha'
      exact congrArg Subtype.val ha'
    · exact (hnot (fun a ha => show (⟨a,ha⟩ : A) ∈ (centralizer (L : Set G)).subgroupOf A
        from ht ▸ mem_top _)).elim
  let J := L ⊔ A
  let L' := L.subgroupOf J
  let A' := A.subgroupOf J
  let σ := ρ.comp J.subtype
  let eL : L' ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let eA : A' ≃* A := subgroupOfEquivOfLe (show A ≤ J from le_sup_right)
  let : IsElementaryAbelian 2 A := hA.2
  have hA' : IsElementaryTwo A' := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ J from le_sup_right)⟩
    intro hb
    have hc := Nat.card_congr eA.toEquiv
    rw [hb,hcard] at hc
    norm_num at hc
  have hq' : IsQuadratic σ A' := fun a ha b hb v => hq a ha b hb v
  have hd' : fixedCodim σ A' ≤ 2 * rank A' := by
    have hcod := fixedCodim_map_equivariant σ ρ J.subtype
      (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl) A'
    rw [map_subgroupOf_eq_of_le (show A ≤ J from le_sup_right)] at hcod
    have hr' : rank A' = rank A := congrArg (Nat.log 2) (Nat.card_congr eA.toEquiv)
    rw [hcod,hr',hr,Nat.mul_one]
    exact hd
  have hgen : L' ⊔ A' = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left) (show A ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hsq : IsSQTK κ J := by
    refine ⟨?_,hkg.subgroup J⟩
    have hLsq' : IsSQTK κ L' := (IsSQTK.equiv eL).mpr hLsq
    have hquot : IsPGroup 2 (J ⧸ L') := quotient_isPGroup_of_sup_eq_top A' L'
      hA'.2.isPGroup ((sup_comm A' L').trans hgen)
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_le_of_normal_two_quotient L' hquot p ho).trans
      (hLsq'.stronglyQuasithin p hp ho)
  have hAC' : A' ⊓ centralizer (L' : Set J) = ⊥ := by
    apply bot_unique
    rintro a ⟨ha,hc⟩
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hAC]
    refine ⟨ha,mem_centralizer_iff.mpr (fun l hl => ?_)⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp hc
      (⟨l,show l ∈ J from (show L ≤ J from le_sup_left) hl⟩ : J) hl)
  have hn : ¬ L' ≤ σ.ker := by
    intro hh
    have hb : L' = ⊥ := bot_unique (hh.trans
      ((MonoidHom.ker_eq_bot_iff σ).mpr (hf.comp J.subtype_injective)).le)
    have hm' := hm.of_mulEquiv eL
    let := (ChapterK.Linear.Recognition.PSL3FourExclusion.model_facts hm').1
    let : IsSimpleGroup (L' ⧸ center L') := IsQuasisimple.simple
    let : Nontrivial L' := (QuotientGroup.mk'_surjective (center L')).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L').mp inferInstance hb
  exact exclude_supplement σ L' A' hsq (hm.of_mulEquiv eL) hgen hA' hq' hd' hAC' hn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
