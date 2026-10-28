module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.FourSource
public import Theory.SpecificGroups.PSL3Two.Parabolics.SquareSolvable

/-!
# The full binary linear-three exchanged closure

The original H-image in Mc/O₂(Mc) is solvable, contains the image of T,
and has order divisible by nine because its two-core quotient has order
72. Its intersection with the normal PSL₃(2) square is therefore a product
of two parabolics. Preserving this product excludes diagram automorphisms
on either coordinate. Faithful conjugation gives an embedding in
PSL₃(2) wr C₂; the original inverse exchanger makes the square proper,
so the embedding fills the whole wreath group.

The source theorem applies this to the literal relative C-component and
original exchanged-factor setup. The final reduction leaves only the
PSL₂(16) full outer image in 14.6.14; it uses no p=3 conclusion from
14.6.15. The remaining full image, strict-closure normalizers and suitable
application belong to qt-e-suitable-odd-normalizer. The earlier primitive
and exchanged-factor inputs retain qt-e-quintic-recognition and
qt-e-14612-singleton; final suitable-choice assembly belongs to
qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.14(3), printed p.1033, with the inverse
conjugation convention of the original component product.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
local notation "L3" => Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W3" => RegularWreathProduct L3 (Multiplicative (ZMod 2))

omit [Finite G] in
/-- The marked inverse exchanger ensures that the closure square is proper
in the ambient quotient. -/
theorem marked_exchanged_square_ne_top
    {Mc K L : Subgroup G} {s : Mc} {D : Type*} [Group D] [Nontrivial D]
    (ha : MarkedExchangedWreath Mc K L s D) :
    (K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≠ ⊤ := by
  obtain ⟨e,k,hl,hr,_⟩ := ha
  intro htop
  let N := (K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let g : N := ⟨q s⁻¹,by
    change q s⁻¹ ∈ (K.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
    rw [htop]
    exact mem_top _⟩
  obtain ⟨u,hu⟩ := exists_ne (1 : D)
  let x := e.symm u
  have he : e x = u := e.apply_symm_apply u
  have hh : k.symm (1,u) = g * k.symm (u,1) * g⁻¹ := by
    apply Subtype.ext
    change (k.symm (1,u) : Mc ⧸ pCore 2 Mc) =
      q s⁻¹ * (k.symm (u,1) : Mc ⧸ pCore 2 Mc) * (q s⁻¹)⁻¹
    rw [←he,hl x]
    exact hr x
  have h := congrArg (fun y => (k y).2) hh
  simp only [map_mul,map_inv,k.apply_symm_apply,Prod.snd_mul,Prod.snd_inv,mul_one,mul_inv_cancel] at h
  exact hu h

/-- The original solvable H supplies the two parabolics and excludes both
diagram coordinates, forcing the full literal PSL₃(2) wreath quotient. -/
theorem linear_three_closure_full_quotient
    (T : Sylow 2 G) {H Mc K L : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hHsol : Group.IsSolvable H)
    (hcard : Nat.card (H ⧸ pCore 2 H) = 72)
    (hlayer : StrictClosureLayer Mc K) {s : Mc}
    (ha : MarkedExchangedWreath Mc K L s L3) : Nonempty ((Mc ⧸ pCore 2 Mc) ≃* W3) := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  have hproper := marked_exchanged_square_ne_top ha
  obtain ⟨_e,k,_hl,_hr,_ρ,_hi,_hin,_hact⟩ := ha
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let N := (K.subgroupOf Mc).map q
  let B := (H.subgroupOf Mc).map q
  have hN : N = generalizedFitting (Mc ⧸ pCore 2 Mc) := hlayer.image_eq_generalizedFitting
  let : N.Normal := hN.symm ▸ inferInstance
  let ep := Matrix.PSL3Two.equiv.symm
  let k' := k.trans (ep.prodCongr ep)
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
  let : IsQuasisimple Matrix.PSL3Two.SL := {
    simple := ((QuotientGroup.quotientMulEquivOfEq Matrix.PSL3Two.center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  have hc := AutomorphismSquare.square_layer_centralizer N k' Matrix.PSL3Two.center_eq_bot hN
  let P := (T.subtype (hTH.trans hHMc)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  have hPB : (P : Subgroup (Mc ⧸ pCore 2 Mc)) ≤ B := map_mono (subgroupOf_mono Mc hTH)
  obtain ⟨hquot,hgen⟩ := AutomorphismSquare.square_layer_two_extension N k'
    Matrix.PSL3Two.center_eq_bot hN Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup P
  let h := subgroupOfEquivOfLe hHMc
  let := hHsol
  let : Group.IsSolvable (H.subgroupOf Mc) :=
    Group.isSolvable_of_isSolvable_injective (f := h.toMonoidHom) h.injective
  have hs : Group.IsSolvable B := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let f := q.subgroupMap (H.subgroupOf Mc)
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = (pCore 2 Mc).comap (H.subgroupOf Mc).subtype by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      rfl]
    exact pCore_isPGroup.comap_subtype
  let eh := QuotientGroup.congr _ _ h (pCore_map_iso 2 h)
  let eqB := f.pCoreQuotientEquiv (q.subgroupMap_surjective _) hk
  have hbcard : Nat.card (B ⧸ pCore 2 B) = 72 := by
    rw [←Nat.card_congr eqB.toEquiv,Nat.card_congr eh.toEquiv]
    exact hcard
  have h9 : 9 ∣ Nat.card B := (show 9 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hbcard]; decide).trans
    (card_dvd_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 B)))
  obtain ⟨eW⟩ := Matrix.PSL3Two.SquareParabolic.full_wreath_of_solvable_overgroup
    N B k' hc hquot P hgen hPB hs h9 hproper
  exact ⟨eW.trans (RegularWreathProduct.congr Matrix.PSL3Two.equiv (MulEquiv.refl _))⟩


open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.14(3) in the PSL₃(2) row. The actual exchanged
component and its inverse conjugate are retained. -/
theorem source_linear_three_closure_alternative
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    (hb : ClassicalGroup.IsPSL ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* W3) ∧
      SourceClosureAlternatives (T : Subgroup G) Mc H 3 := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let eA := eF.trans (Atlas.fieldEquivPSL 3 ef)
  let ec : XiQuotient L ≃* (L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hL))).symm.trans (cComponentTwoCoreQuotientEquiv hcomp)
  let := hq
  let : IsQuasisimple L3 := IsQuasisimple.of_mulEquiv (ec.trans eA)
  have ho : IsPGroup 2 (MulAut.Outer L3) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr Matrix.PSL3Two.equiv)
  obtain ⟨_,s,_hs,_hsn,_hprod,ha⟩ := exchanged_closure_wreath_action hTMc hL hcomp
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
    hm.1 hlayer eA Matrix.PSL3Two.Automorphisms.center_psl_eq_bot ho
  have he := linear_three_closure_full_quotient T hH.1.2 hHMc (primitiveResidual_isSolvable H hprim)
    (by simpa using OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 3 H0 H1 H2 d)
    hlayer ha
  exact ⟨he,Or.inr (Or.inr (Or.inl ⟨rfl,⟨L,hL,hcomp,hm.1⟩,Or.inr he⟩))⟩

/-- Only the PSL₂(16) full outer image remains in the original closure
classification. This reduction does not assume the later p=3 theorem. -/
theorem source_closure_alternatives_or_sixteen
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p ∨
      (p = 5 ∧ ∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
        IsQuasisimple (XiQuotient L) ∧
        StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        ClassicalGroup.IsPSL
          ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16 ∧
        Mc = residualClosure H Mc ⊔ (T : Subgroup G) ∧
        ExchangedWreathRows (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc)) := by
  rcases source_closure_alternatives_or_sixteen_or_linear_three
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with
    hc | ⟨L,hL,hcomp,hq,hm,hmodels,hgen,ha,hr,hr3,hlayer⟩
  · exact Or.inl hc
  · rcases hmodels with ⟨hp,hb⟩ | ⟨hp,hb⟩
    · exact Or.inr ⟨hp,L,hL,hcomp,hq,hm,hb,hgen,ha,hr,hr3,hlayer⟩
    · subst p
      exact Or.inl (source_linear_three_closure_alternative
        hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d
        L hL hcomp hq hm hlayer hb).2

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
