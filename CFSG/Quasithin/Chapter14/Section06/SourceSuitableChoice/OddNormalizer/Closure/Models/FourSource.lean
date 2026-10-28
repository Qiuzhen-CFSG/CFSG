module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.FourFull
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.SourceWreathAction
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Alternatives.Dimensions

/-!
# The full four-element-field closure alternative

Restrict the original quotient Mc → Mc/O₂(Mc) to the actual outside H.
Its two-group kernel preserves the quotient by O₂, so the exchanged
14.6.12 factors give order 72 for the image modulo its two-core. The normal
A₅ square and solvable Sylow control then force the whole S₅ wreath group.
This proves the PSL₂(4) row of original 14.6.14(3), including its literal
quotient isomorphism and the component product with inverse conjugation.

The final theorem applies this to the original maximal-prime source setup.
Only the PSL₂(16) and PSL₃(2) full outer images remain in the exchanged
classification. It retains their marked actions, both residual identities,
full generalized-Fitting layer, and Mc = Kz T. Their full-image proofs,
the strict-closure normalizers and original 14.6.14--16 assembly remain
with qt-e-suitable-odd-normalizer. The earlier primitive and exchanged-factor
inputs retain qt-e-quintic-recognition and qt-e-14612-singleton; the final
suitable-involution choice belongs to qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.12 and 14.6.14(3), printed pp.1031,1033.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
local notation "A5" => alternatingGroup (Fin 5)
local notation "W5" => RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))

/-- The marked four-element-field action fills the full S₅ wreath quotient.
Solvability and the order 72 come from the original H. -/
theorem four_closure_full_quotient
    (T : Sylow 2 G) {H Mc K L : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hHsol : Group.IsSolvable H)
    (hcard : Nat.card (H ⧸ pCore 2 H) = 72)
    (hlayer : StrictClosureLayer Mc K) {s : Mc}
    (ha : MarkedExchangedWreath Mc K L s A5) : Nonempty ((Mc ⧸ pCore 2 Mc) ≃* W5) := by
  obtain ⟨_e,k,_hl,_hr,_ρ,_hi,_hin,_hact⟩ := ha
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let N := (K.subgroupOf Mc).map q
  let B := (H.subgroupOf Mc).map q
  have hN : N = generalizedFitting (Mc ⧸ pCore 2 Mc) := hlayer.image_eq_generalizedFitting
  let : N.Normal := hN.symm ▸ inferInstance
  have hc : centralizer (N : Set (Mc ⧸ pCore 2 Mc)) = ⊥ :=
    AutomorphismSquare.square_layer_centralizer N k
      (alternatingGroup.center_eq_bot (by simp)) hN
  let P := (T.subtype (hTH.trans hHMc)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  have hPB : (P : Subgroup (Mc ⧸ pCore 2 Mc)) ≤ B :=
    map_mono (subgroupOf_mono Mc hTH)
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
  exact a5_square_full_automorphism N B k hc P hPB hs hbcard

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

/-- Original 14.6.14(3) in the PSL₂(4) row, including the full literal wreath
isomorphism. Neither a full-action nor a normalizer premise is added. -/
theorem source_four_closure_alternative
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    (hb : ClassicalGroup.IsPSL ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 4) :
    Nonempty ((Mc ⧸ pCore 2 Mc) ≃* W5) ∧
      SourceClosureAlternatives (T : Subgroup G) Mc H 3 := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  obtain ⟨eb⟩ := binary_component_equiv (m := 2) hb
  let eA := eb.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5
  let ec : XiQuotient L ≃* (L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hL))).symm.trans (cComponentTwoCoreQuotientEquiv hcomp)
  let := hq
  let : IsQuasisimple A5 := IsQuasisimple.of_mulEquiv (ec.trans eA)
  obtain ⟨_,s,_hs,_hsn,_hprod,ha⟩ := exchanged_closure_wreath_action hTMc hL hcomp
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
    hm.1 hlayer eA (alternatingGroup.center_eq_bot (by simp)) Theory.AlternatingFive.outer_isPGroup_two
  have he := four_closure_full_quotient T hH.1.2 hHMc (primitiveResidual_isSolvable H hprim)
    (by simpa using OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 3 H0 H1 H2 d)
    hlayer ha
  exact ⟨he,Or.inr (Or.inr (Or.inl ⟨rfl,⟨L,hL,hcomp,hm.1⟩,Or.inl he⟩))⟩

/-- The faithful source reduction now closes the PSL₂(4) row. Only the
PSL₂(16) and PSL₃(2) full outer images remain. -/
theorem source_closure_alternatives_or_sixteen_or_linear_three
    (p : ℕ) (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H p)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M p) :
    SourceClosureAlternatives (T : Subgroup G) Mc H p ∨
      (∃ L : Subgroup G, L ≤ Mc ∧ (L.subgroupOf Mc).IsCComponent ∧
        IsQuasisimple (XiQuotient L) ∧
        StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        ((p = 5 ∧ ClassicalGroup.IsPSL
            ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16) ∨
          (p = 3 ∧ ClassicalGroup.IsPSL
            ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2)) ∧
        Mc = residualClosure H Mc ⊔ (T : Subgroup G) ∧
        ExchangedWreathRows (T : Subgroup G) Mc (residualClosure H Mc) L p ∧
        residualClosure H Mc = (primeToResidual p Mc).map Mc.subtype ∧
        residualClosure H Mc = (primeToResidual 3 Mc).map Mc.subtype ∧
        StrictClosureLayer Mc (residualClosure H Mc)) := by
  rcases source_closure_alternatives_or_marked_wreath_actions
      hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax with
    hc | ⟨L,hL,hcomp,hq,hm,hgen,ha,hr,hr3,hlayer⟩
  · exact Or.inl hc
  · rcases source_strict_exchanged_component_models
        hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 hprim d hmax L hcomp hm with
      ⟨hp,hb⟩ | hmodels
    · subst p
      exact Or.inl (source_four_closure_alternative
        hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d
        L hL hcomp hq hm hlayer hb).2
    · exact Or.inr ⟨L,hL,hcomp,hq,hm,hmodels,hgen,ha,hr,hr3,hlayer⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
