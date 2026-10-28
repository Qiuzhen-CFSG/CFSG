module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeSection
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeProduct
/-!
# Two quintet-kernel copies on the original M22-code pair core

The inclusion of B/U and its original inverse conjugate generate the literal
P/U. The five-dimensional marking and the order 2^10 identify this section with
two copies of the five-dimensional quintet kernel. The residual acts diagonally because its
commutators with I lie in its two-core. All coordinates retain the original
quotient maps and selected conjugator.

Source: Aschbacher--Smith 8.2.8(4--5), printed pp.718--719,
refs/quasithin.pdf. Native code attribution: LICENSES/ATLAS.txt.
-/
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Atlas.Codes
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE HermitianSource Offenders.Parabolic.Construction Normalizer.SmallOvergroups
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G]

/-- The original ten-space as two quintet-kernel copies, with the source
conjugation and residual action explicitly marked. -/
@[expose] def M22CodePairAction (R I V U : Subgroup G) (i : I)
    (fq : R →* MathieuCode.M22Quintet.Q) : Prop :=
  let W := MathieuCode.M22Quintet.K
  let B := V ⊓ I.pCoreIn 2
  let Y := R ⊔ I
  ∃ hYP : Y ≤ normalizer (I.pCoreIn 2 : Set G),
    ∃ hYU : Y ≤ normalizer (U : Set G),
      ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
        ∃ hBU : (U.subgroupOf B).Normal, letI := hBU
          ∃ eB : (B ⧸ U.subgroupOf B) ≃* W,
            ∃ r : R →* alternatingGroup (Fin 5),
              ∃ eP : W × W ≃* (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)),
                let q := QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl)
                  (show B ≤ I.pCoreIn 2 from inf_le_right)
                let f := sectionAction Y (I.pCoreIn 2) U hYP hYU
                Function.Surjective r ∧ r.ker = pCore 2 R ∧
                (∀ x, (r x).val = MathieuCode.M22Quintet.CocodeTransfer.NaturalQuotient.q (fq x)) ∧
                (∀ x y, eP (x,y) = q (eB.symm x) * f (inclusion le_sup_right i⁻¹) (q (eB.symm y))) ∧
                ∀ (x : R) u v, f (inclusion le_sup_left x) (eP (u,v)) =
                  eP ((MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x)
                      (Additive.ofMul u)).toMul,
                    (MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x)
                      (Additive.ofMul v)).toMul)


/-- Two-conjugate generation makes the natural section coordinates into
a diagonal A5 action on all of the original P/U. -/
theorem m22_code_pair_action (R I V U : Subgroup G) (i : I)
    (h : M22CodePairProductAction R I V U)
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hn : M22FiveSection R (V ⊓ I.pCoreIn 2) U fq)
    (hgen : (V ⊓ I.pCoreIn 2) ⊔ (V ⊓ I.pCoreIn 2).map
      (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) : M22CodePairAction R I V U i fq := by
  obtain ⟨hYP,hYU,hUP,hEl,hcard,hker,hcore,hR,hI,hRB,hBU,heq,eY,heY⟩ := h
  let := hUP
  let := hBU
  let := hEl
  obtain ⟨_,_,_,r,eB,hrsur,hrker,hrval,hnat,_⟩ := hn
  let W := MathieuCode.M22Quintet.K
  let B := V ⊓ I.pCoreIn 2
  let P := I.pCoreIn 2
  let Y := R ⊔ I
  let q : (B ⧸ U.subgroupOf B) →* (P ⧸ U.subgroupOf P) :=
    QuotientGroup.quotientMapSubgroupOfOfLe (show U ≤ U from le_rfl) inf_le_right
  let f := sectionAction Y P U hYP hYU
  let a : Y := inclusion le_sup_right i⁻¹
  let c := f a
  let d : W →* (P ⧸ U.subgroupOf P) := q.comp eB.symm.toMonoidHom
  let k : W × W →* (P ⧸ U.subgroupOf P) := {
    toFun := fun x => d x.1 * c (d x.2)
    map_one' := by simp
    map_mul' := by intro x y; simp only [Prod.fst_mul,Prod.snd_mul,map_mul]; ac_rfl }
  have hs : Function.Surjective k := by
    let Z : Subgroup P := k.range.comap (QuotientGroup.mk' (U.subgroupOf P))
    let ZG := Z.map P.subtype
    have hb : B ≤ ZG := by
      intro b hb
      refine ⟨⟨b,hb.2⟩,?_,rfl⟩
      change QuotientGroup.mk' (U.subgroupOf P) ⟨b,hb.2⟩ ∈ k.range
      refine ⟨(eB (QuotientGroup.mk' (U.subgroupOf B) ⟨b,hb⟩),1),?_⟩
      change d (eB (QuotientGroup.mk' (U.subgroupOf B) ⟨b,hb⟩)) * c (d 1) = _
      simp only [map_one,mul_one]
      change q (eB.symm (eB _)) = _
      rw [eB.symm_apply_apply]
      rfl
    have hb' : B.map (MulAut.conj i.val⁻¹).toMonoidHom ≤ ZG := by
      rintro _ ⟨b,hb,rfl⟩
      let p : P := ⟨b,hb.2⟩
      let p' := P.normalizerMonoidHom (inclusion hYP a) p
      refine ⟨p',?_,rfl⟩
      change QuotientGroup.mk' (U.subgroupOf P) p' ∈ k.range
      refine ⟨(1,eB (QuotientGroup.mk' (U.subgroupOf B) ⟨b,hb⟩)),?_⟩
      change d 1 * c (d (eB (QuotientGroup.mk' (U.subgroupOf B) ⟨b,hb⟩))) = _
      simp only [map_one,one_mul]
      change c (q (eB.symm (eB _))) = _
      rw [eB.symm_apply_apply]
      rfl
    have hp : P ≤ ZG := by
      change I.pCoreIn 2 ≤ ZG
      rw [←hgen]
      exact sup_le hb hb'
    intro v
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf P) v
    obtain ⟨p',hp',he⟩ := hp p.property
    have hpp : p' = p := Subtype.ext he
    exact hpp ▸ hp'
  have hW : Nat.card W = 2^5 := by
    change Nat.card (Additive MathieuCode.M22Quintet.K) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      Sporadic.Mathieu.M22ChapterH.Quintet.kernel_finrank]
  have hbij : Function.Bijective k := hs.bijective_of_nat_card_le (by
    rw [Nat.card_prod,hW]
    exact hcard.ge)
  let eP : W × W ≃* (P ⧸ U.subgroupOf P) := MulEquiv.ofBijective k hbij
  have hfirst (x : R) (v : W) : f (inclusion le_sup_left x) (d v) =
      d ((MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x) (Additive.ofMul v)).toMul) := by
    have hh : sectionAction R B U hRB (le_sup_left.trans hYU) x (eB.symm v) =
        eB.symm ((MathieuCode.NormalizedShadowRows.M22CodeSection.fiveAction (r x) (Additive.ofMul v)).toMul) := by
      apply eB.injective
      apply Additive.ofMul.injective
      rw [hnat,eB.apply_symm_apply,eB.apply_symm_apply]
      rfl
    change f (inclusion le_sup_left x) (q (eB.symm v)) = q (eB.symm _)
    rw [←hh]
    exact (heq x (eB.symm v)).symm
  have hcommute (r : R) : Commute (f (inclusion le_sup_left r)) c := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    apply MonoidHom.mem_ker.mp
    rw [hker]
    have hm : (⁅(r : G),(i⁻¹ : I).val⁆ : G) ∈ Y.pCoreIn 2 := by
      rw [hcore]
      exact mem_sup_right (hcomm (commutator_mem_commutator r.property (I.inv_mem i.property)))
    obtain ⟨t,ht,he⟩ := hm
    have he' : t = ⁅inclusion (show R ≤ Y from le_sup_left) r,a⁆ := Subtype.ext he
    exact he' ▸ ht
  refine ⟨hYP,hYU,hUP,hBU,eB,r,eP,hrsur,hrker,hrval,fun _ _ => rfl,?_⟩
  intro r x y
  change f (inclusion le_sup_left r) (d x * c (d y)) = _
  rw [map_mul,hfirst]
  have hc : f (inclusion le_sup_left r) (c (d y)) = c (f (inclusion le_sup_left r) (d y)) :=
    congrArg (fun z : MulAut (P ⧸ U.subgroupOf P) => z (d y)) (hcommute r).eq
  rw [hc,hfirst]
  rfl
/-- The actual selected two-conjugate pair supplies the two-copy generation
used by the natural diagonal action on P/U. -/
theorem selected_m22_code_pair_action [Finite G]
    {V H M I R U : Subgroup G} {T : Sylow 2 G} [IsElementaryAbelian 2 V]
    {i : I} {S : Sylow 2 I} (s : Selected H T M V I 1 i S)
    (h : M22CodePairProductAction R I V U)
    {fq : R →* MathieuCode.M22Quintet.Q}
    (hn : M22FiveSection R (V ⊓ I.pCoreIn 2) U fq)
    (hcomm : ⁅R,I⁆ ≤ R.pCoreIn 2) : M22CodePairAction R I V U i fq := by
  have hIP : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hPi : (I.pCoreIn 2).map (MulAut.conj i.val⁻¹).toMonoidHom = I.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hIP (I.inv_mem i.property))
  apply m22_code_pair_action R I V U i h hn ?_ hcomm
  rw [map_inf _ _ _ (MulAut.conj i.val⁻¹).injective,hPi]
  exact (selected_one_core_product s).symm
end
end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
