module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.NormalizerPaired
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Mathlib.Algebra.CharP.CharAndCard
public import Theory.Representation.PerfectInvolutionExtension.Inner

/-!
# Exclusion of the irreducible component-normalizer chief action

In the two allowed PSL₂ rows, an automorphism fixing a Sylow two-subgroup
pointwise is inner. Apply this to the actual quotient component and the
marked central involution. Irreducibility of its literal normalizer makes
all component constituents nontrivial, hence of binary degree at least
three. Rank-two displacement preserves each constituent. The proved inner
involution lemma therefore places the marked involution in the component.
Its commutation with the original exchanger also places it in the other
component, contradicting their trivial intersection.

The source application retains the quotient map and the original involution.
The preceding reduction has already excluded the exchanged-constituent
branch using the same nonzero H-fixed source-plane vector and its moving
parabolic. Combining both branches proves general partner-core containment.
Only preceding source geometry, residual and quotient premises remain;
qt-e-152-chosen-action-contradiction discharges them in final assembly.

Source: Aschbacher–Smith 15.2.12(2)(iii) and 15.2.27(2), printed p.1119;
Clifford theory, Isaacs, Theorem 6.5; PSL₂ Sylow fixers as in GLS III 2.6.5(e).
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X] [Nontrivial X]

/-- Both allowed component models have inner pointwise Sylow fixers. -/
theorem pair_model_sylow_fixer_inner
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL X 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL X 2 p)
    (P : Sylow 2 X) (α : MulAut X) (hfix : ∀ x ∈ P, α x = x) :
    ∃ k : X, α = MulAut.conj k := by
  have transport {Y : Type} [Group Y] (e : X ≃* Y)
      (hY : ∀ (Q : Sylow 2 Y) (β : MulAut Y), (∀ y ∈ Q, β y = y) →
        ∃ y, β = MulAut.conj y) : ∃ k : X, α = MulAut.conj k := by
    apply (MulAut.congr_inner_iff e α).mp
    apply hY (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    rintro _ ⟨x,hx,rfl⟩
    change e (α (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hfix x hx]
  rcases hm with ⟨n,_,F,_,_,hF,⟨e⟩⟩ | ⟨p,hp,ho,F,_,_,hF,⟨e⟩⟩
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    apply transport e
    intro Q β hb
    obtain ⟨x,_,hx⟩ := Theory.PSL2.aut_fixing_sylow_inner Q β hb
    exact ⟨x,hx⟩
  · let : Fact p.Prime := ⟨hp⟩
    let : Fintype F := Fintype.ofFinite F
    let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let : Nontrivial PSL(2,F) := e.symm.surjective.nontrivial
    have hlarge : 3 < p := by
      rw [←hF]
      exact Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF.symm ▸ ho) (Group.IsPerfect.not_isSolvable _)
    let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
    apply transport (e.trans (GorensteinWalter.psl2RingEquiv eF))
    intro Q β hb
    obtain ⟨x,_,hx⟩ := Theory.PSL2.primeField_sylow_fixed_inner ho hlarge Q β hb
    exact ⟨x,hx⟩

end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- A rank-two central involution cannot act on an irreducible component normalizer of this pair. -/
theorem false_of_irreducible_pair_normalizer
    (σ : Representation (ZMod 2) D W) (hf : Function.Injective σ)
    (A : Subgroup D) (hA : IsComponent D A) [IsSimpleGroup A]
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL A 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL A 2 p)
    (S : Sylow 2 D) (a t : D) (haI : a ∈ normalizer (A : Set D))
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) (ht : t ∈ S)
    (htI : t ∉ normalizer (A : Set D))
    (hc : ∀ s ∈ S, Commute a s)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (σ a - 1)) ≤ 2)
    (hirr : IsIrreducible (σ.comp (normalizer (A : Set D)).subtype)) : False := by
  let I := normalizer (A : Set D)
  let K := A.subgroupOf I
  let e : K ≃* A := subgroupOfEquivOfLe A.le_normalizer
  let : K.Normal := normal_subgroupOf_of_le_normalizer (le_refl I)
  let := hA.2
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : IsSimpleGroup K := e.isSimpleGroup
  have hz : center K = ⊥ := (inferInstance : (center K).Normal).eq_bot_or_eq_top.resolve_right
    (fun hh => Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp hh))
  have hK : K ≠ ⊥ := (nontrivial_iff_ne_bot K).mp inferInstance
  let aI : I := ⟨a,haI⟩
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.1
  have hinner : ∃ k : A, A.normalizerMonoidHom aI = MulAut.conj k := by
    apply pair_model_sylow_fixer_inner hm P
    intro x hx
    have hxS : (x : D) ∈ S := by
      change x ∈ (P : Subgroup A) at hx
      rw [hP] at hx
      exact hx
    apply Subtype.ext
    change a * x * a⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (hc x hxS).eq
  have hinnerK : ∃ k : K, MulAut.conjNormal (H := K) aI = MulAut.conj k := by
    apply (MulAut.congr_inner_iff e _).mp
    have he : MulAut.congr e (MulAut.conjNormal (H := K) aI) = A.normalizerMonoidHom aI := by
      ext x
      rfl
    rw [he]
    exact hinner
  have haK : aI ∈ K := PerfectInvolutionExtension.inner_square_one_mem_of_small_displacement
    (σ.comp I.subtype) hirr (hf.comp I.subtype_injective) K hK hz aI
      (Subtype.ext ha2) hr hinnerK
  have haA : a ∈ A := haK
  have haB : a ∈ A.conjBy t := by
    have he : MulAut.conj t a = a := mul_inv_eq_iff_eq_mul.mpr (hc t ht).eq.symm
    exact he ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom haA
  have hne : A ≠ A.conjBy t := fun he => htI (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hcomm := hA.commutator_eq_bot_of_ne (hA.map_conj t) hne
  have hzA : center A = ⊥ := (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
    (fun hh => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp hh))
  have haz : (⟨a,haA⟩ : A) ∈ center A := mem_center_iff.mpr fun x =>
    Subtype.ext (((commutator_eq_bot_iff_le_centralizer.mp hcomm x.property) a haB).symm)
  exact ha1 (congrArg (fun x : A => (x : D)) (mem_bot.mp (hzA ▸ haz)))
end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition

namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open NoncentralChiefRefinement PartnerChiefRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Exclude the irreducible restriction to the literal component normalizer. -/
theorem source_chosen_false_of_irreducible_partner_normalizer
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (C : Subgroup G) (t : G) (hC : C ∈ Chapter1.cComponentsIn Mc)
    (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (C : Set G))
    (he : partnerSpan H Mc = C ⊔ C.conjBy t)
    (hm : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p)
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 L)
    let I := normalizer (((C.subgroupOf L).map q : Subgroup (L ⧸ pCore 2 L)) : Set _)
    ∀ (σ : Representation (ZMod 2) (L ⧸ pCore 2 L) W),
      PartnerChiefQuotientProperties T V L σ →
      ∀ a : L, orderOf (q a) = 2 →
      (∀ s ∈ (T : Subgroup G).subgroupOf L, Commute (q a) (q s)) →
      Module.finrank (ZMod 2) (LinearMap.range (σ (q a) - 1)) = 2 →
      q a ∈ I → IsIrreducible (σ.comp I.subtype) → False := by
  dsimp only
  intro σ hp a ho hc hr haI hirr
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let tL : L := ⟨t,(show (T : Subgroup G) ≤ L from le_sup_right) ht⟩
  let A := (C.subgroupOf L).map q
  change orderOf (q a) = 2 at ho
  obtain ⟨hA,hsA,_,_,htI⟩ := source_chosen_pair_normalizer_data hg C t hC ht htn he hm
  change IsComponent (L ⧸ pCore 2 L) A at hA
  let : IsSimpleGroup A := hsA
  have hTM := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  have hCL : C ≤ L := (show C ≤ partnerSpan H Mc from he ▸ le_sup_left).trans le_sup_left
  have hCc : (C.subgroupOf L).IsCComponent := hC.2.subgroupOf_of_le hCL hLM
  let eC := subgroupOfEquivOfLe hCL
  let eQ : A ≃* (C ⧸ pCore 2 C) := (cComponentTwoCoreQuotientEquiv hCc).symm.trans
    (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC))
  have hmA : (∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL A 2 (2 ^ n)) ∨
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL A 2 p := by
    rcases hm with ⟨n,hn,F,_,_,hF,⟨e⟩⟩ | ⟨p,hp,ho,F,_,_,hF,⟨e⟩⟩
    · exact Or.inl ⟨n,hn,F,inferInstance,inferInstance,hF,⟨eQ.trans e⟩⟩
    · exact Or.inr ⟨p,hp,ho,F,inferInstance,inferInstance,hF,⟨eQ.trans e⟩⟩
  obtain ⟨hf,_,_,_,_,S,hS,_⟩ := hp
  have htS : q tL ∈ S := by
    change q tL ∈ (S : Subgroup _)
    rw [hS]
    exact mem_map_of_mem q ht
  have hcent : ∀ s ∈ S, Commute (q a) s := by
    intro s hs
    change s ∈ (S : Subgroup _) at hs
    rw [hS] at hs
    obtain ⟨b,hb,rfl⟩ := hs
    exact hc b hb
  exact false_of_irreducible_pair_normalizer σ hf A hA hmA S (q a) (q tL) haI
    (by simpa only [ho] using pow_orderOf_eq_one (q a))
    (fun hh => by simp [hh] at ho) htS htI hcent hr.le hirr

/-- Original 15.2.27(2): the actual chosen module lies in the partner two-core. -/
theorem source_chosen_partner_core
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) : V ≤ twoCoreIn Mc := by
  by_contra hn
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨C,t,ht,hCL,hC,htn,he,hset,hm,B,U,hBU,hU,hB,hσ⟩ :=
    source_chosen_noncore_partner_irreducible_chief h hg hMc hZ hquotient hres hs hn hplane
  have hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hBU hp
  obtain ⟨σ,hσeq,hprop,a,ha,ho,hacent,hr,w,hw,hfix,hHfix,hi,haI,hirr⟩ := hσ
  exact source_chosen_false_of_irreducible_partner_normalizer h hg C t hC ht htn he hm
    (W := Additive (Section B U)) σ hprop a ho hacent hr haI hirr

end CFSG.Quasithin.Chapter15.Section02
