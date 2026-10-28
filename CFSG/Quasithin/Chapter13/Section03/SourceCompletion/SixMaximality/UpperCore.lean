module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourcePairCentralizerBound
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.SylowIndexTwoExtension
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action

/-!
# Small faithful upper quotients in the original normal A₆ branch

The already proved original core decomposition gives Q = V × C, with
|V| = 16 and |C| ≤ 2. Thus Q is elementary abelian of order at most 32.
An upper local component I is T-invariant; its intrinsic two-core is a
normal two-subgroup of LT and hence lies in Q. The actual faithful-local
hypothesis gives F*(I) = O₂(I), so conjugation embeds I/O₂(I) into the
automorphisms of that elementary core and therefore into GL₅(2).

The original A₆ section survives passage through the solvable two-core,
so 360 divides |I/O₂(I)|. A core of order at most eight would instead
embed the quotient in GL₃(2), of order 168; therefore |O₂(I)| is 16 or 32.
The original natural action extends from LT to six letters with Sylow
kernel Q, giving |T| ≤ 512. Restricting and quotienting Sylow subgroups
then gives a quotient Sylow bound of 32.

These are specialized inputs to the remaining upper-model inspection in
13.3.2 for the actual normal A₆ consumer of 13.5.15. They use its original
F.9.1 hypotheses, with no assumed maximality for L or normalization of V
by I. Source: Aschbacher–Smith 13.3.2, pp.884–885, and 13.5.15(4,7),
pp.920–921; the strengthened bounds use the proved original core split.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperCore
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- The literal original core is an elementary group of order at most 32. -/
theorem original_core_elementary_bound :
    IsElementaryAbelian 2 (D.LT.pCoreIn 2) ∧ Nat.card (D.LT.pCoreIn 2) ≤ 32 := by
  obtain ⟨g,_,hK,_,_,hQ,hdis,hidx,hC⟩ :=
    SourcePairCentralizerBound.exists_original_core_dichotomy_source d h e hseed hn hU
  let C := (D.T : Subgroup G) ⊓ centralizer (K D g.val : Set G)
  change D.LT.pCoreIn 2 = D.V ⊔ C at hQ
  change C = ⊥ ∨ Nat.card C = 2 at hC
  let : IsElementaryAbelian 2 D.V := h.elementary
  have he : IsElementaryAbelian 2 C := by
    rcases hC with hz | hc
    · rw [hz]
      refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
      exact (Group.exponent_dvd_nat_card (G := (⊥ : Subgroup G))).trans (by simp)
    · let : IsCyclic C := isCyclic_of_prime_card hc
      exact {
        toIsMulCommutative := inferInstance
        exponent_dvd_p := by
          rw [← hc]
          exact Group.exponent_dvd_nat_card }
  let := he
  have hCV : C ≤ centralizer (D.V : Set G) := by
    exact (show C ≤ D.LT.pCoreIn 2 from hQ ▸ le_sup_right).trans
      (h.sylow_centralizer.symm.le.trans inf_le_right)
  have hb : IsElementaryAbelian 2 (D.LT.pCoreIn 2) := by
    rw [hQ]
    exact IsElementaryAbelian.sup_of_le_centralizer hCV
  have hc : Nat.card C ≤ 2 := by
    rcases hC with hz | hc
    · rw [hz,card_bot]; norm_num
    · omega
  have hV : Nat.card D.V = 16 := ReturningPlane.module_card d
  have hm := relIndex_mul_card_of_le (show D.V ≤ D.LT.pCoreIn 2 from hQ ▸ le_sup_left)
  change D.V.relIndex (D.LT.pCoreIn 2) = Nat.card C at hidx
  rw [hidx,hV] at hm
  exact ⟨hb,by omega⟩


omit h e hseed hn hU in
/-- T-normalization makes the upper component core a normal two-subgroup of LT. -/
theorem upper_core_le_original {I : Subgroup G}
    (hI : I ∈ Chapter1.L G (D.T : Subgroup G)) (hLI : D.L ≤ I) :
    I.pCoreIn 2 ≤ D.LT.pCoreIn 2 := by
  have hL := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff D.T D.L).mp
    d.counterexample.local_component).1
  have hTI := Chapter1.Section02.Adequate.local_chain_normalizes
    hL hI hLI d.normalizes_L
  have hnorm : I ⊔ (D.T : Subgroup G) ≤ normalizer (I.pCoreIn 2 : Set G) :=
    (sup_le I.le_normalizer hTI).trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcoreIT : I.pCoreIn 2 ≤ (I ⊔ (D.T : Subgroup G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
      ((pCoreIn_le 2 I).trans le_sup_left) hnorm
  have hcoreT : I.pCoreIn 2 ≤ (D.T : Subgroup G) :=
    hcoreIT.trans ((pCoreIn_le_sylow _ (D.T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right))
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
    (hcoreT.trans le_sup_right) ((sup_le_sup_right hLI _).trans hnorm)

/-- The upper intrinsic core inherits the original elementary order bound. -/
theorem upper_core_elementary_bound {I : Subgroup G}
    (hI : I ∈ Chapter1.L G (D.T : Subgroup G)) (hLI : D.L ≤ I) :
    IsElementaryAbelian 2 (pCore 2 I) ∧ Nat.card (pCore 2 I) ≤ 32 := by
  obtain ⟨he,hc⟩ := original_core_elementary_bound d h e hseed hn hU
  let := he
  let : IsElementaryAbelian 2 (I.pCoreIn 2) :=
    IsElementaryAbelian.of_le (upper_core_le_original d hI hLI)
  let c : pCore 2 I ≃* I.pCoreIn 2 :=
    (pCore 2 I).equivMapOfInjective I.subtype I.subtype_injective
  have hp : IsElementaryAbelian 2 (pCore 2 I) := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun x y => c.injective (by
      simp only [map_mul,mul_comm]))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => c.injective (by
      simpa only [map_pow,map_one] using
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 (I.pCoreIn 2)) (c x))) }
  exact ⟨hp,(Nat.card_congr c.toEquiv).le.trans
    ((card_le_of_le (upper_core_le_original d hI hLI)).trans hc)⟩

omit d h e hseed hn hU in
private theorem quotient_embedding_of_elementary_core {I : Type*} [Group I] [Finite I]
    (hf : generalizedFitting I = pCore 2 I) [IsElementaryAbelian 2 (pCore 2 I)]
    {n : ℕ} (hc : Nat.card (pCore 2 I) ≤ 2 ^ n) :
    ∃ f : (I ⧸ pCore 2 I) →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2),
      Function.Injective f := by
  let N := pCore 2 I
  let i : I →* normalizer (N : Set I) := (MonoidHom.id I).codRestrict _ (by
    intro x
    rw [normalizer_eq_top]
    trivial)
  let a := N.normalizerMonoidHom.comp i
  have hk : a.ker = N := by
    change N.normalizerMonoidHom.ker.comap i = N
    rw [normalizerMonoidHom_ker]
    ext x
    change x ∈ centralizer (N : Set I) ↔ x ∈ N
    exact ⟨fun hx => ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hf) hx,
      fun hx => N.le_centralizer hx⟩
  let eqv : (I ⧸ N) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange a)
  obtain ⟨b,hb⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := n) N hc
  exact ⟨b.comp (a.range.subtype.comp eqv.toMonoidHom),
    hb.comp (a.range.subtype_injective.comp eqv.injective)⟩

/-- Faithful conjugation on the actual intrinsic core supplies a binary five-space embedding. -/
theorem upper_quotient_binary_five_embedding {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) :
    ∃ f : (I ⧸ pCore 2 I) →* Matrix.GeneralLinearGroup (Fin 5) (ZMod 2),
      Function.Injective f := by
  obtain ⟨he,hc⟩ := upper_core_elementary_bound d h e hseed hn hU hI.maximal_faithful.1.1 hLI
  let := he
  exact quotient_embedding_of_elementary_core hI.maximal_faithful.2.1.2.2 hc

/-- The upper quotient order divides the proved order of GL₅(2). -/
theorem upper_quotient_card_dvd {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) : Nat.card (I ⧸ pCore 2 I) ∣ 9999360 := by
  obtain ⟨f,hf⟩ := upper_quotient_binary_five_embedding d h e hseed hn hU hI hLI
  have hd := card_dvd_of_injective f hf
  have hc : Nat.card (Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ,ZMod.card]
  rwa [hc] at hd


omit d h hseed hn hU in
/-- The original A₆ section persists through the upper solvable two-core. -/
theorem six_dvd_upper_quotient {I : Subgroup G} (hLI : D.L ≤ I) :
    360 ∣ Nat.card (I ⧸ pCore 2 I) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
  let : Group.IsNilpotent (pCore 2 I) := pCore_isPGroup.isNilpotent
  let m : Group.SolvableKernelModel I (I ⧸ pCore 2 I) := {
    kernel := pCore 2 I
    normal := inferInstance
    solvable := inferInstance
    quotientEquiv := MulEquiv.refl _ }
  let eL := subgroupOfEquivOfLe hLI
  let f : D.L.subgroupOf I →* alternatingGroup (Fin 6) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 D.L)).comp eL.toMonoidHom)
  have hf : Function.Surjective f :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp eL.surjective)
  obtain ⟨W,g,hg⟩ := m.simple_section (Group.IsPerfect.not_isSolvable _) _ f hf
  have hd := (card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [hcard] at hd
  exact hd

/-- The faithful upper component has an elementary core of order sixteen or thirty-two. -/
theorem upper_core_card {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) : Nat.card (pCore 2 I) = 16 ∨ Nat.card (pCore 2 I) = 32 := by
  obtain ⟨he,hc⟩ := upper_core_elementary_bound d h e hseed hn hU hI.maximal_faithful.1.1 hLI
  let := he
  have hsmall : ¬ Nat.card (pCore 2 I) ≤ 8 := by
    intro hs
    obtain ⟨f,hf⟩ := quotient_embedding_of_elementary_core
      hI.maximal_faithful.2.1.2.2 (n := 3) hs
    have hd := (six_dvd_upper_quotient e hLI).trans (card_dvd_of_injective f hf)
    have hg : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
      rw [Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ,ZMod.card]
    rw [hg] at hd
    norm_num at hd
  obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 I).exists_card_eq
  have hcmap : Nat.card (I.pCoreIn 2) = Nat.card (pCore 2 I) := card_map_of_injective I.subtype_injective
  rw [hcmap] at hk
  have hk5 : k ≤ 5 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact hk ▸ hc
  rw [hk] at hsmall ⊢
  interval_cases k <;> norm_num at *

omit e hseed hn hU in
/-- The actual six-letter Sylow action has kernel the original two-core. -/
theorem original_sylow_card_le_mul_core :
    Nat.card D.T ≤ 16 * Nat.card (D.LT.pCoreIn 2) := by
  let := h.elementary
  let aV : Additive D.V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    d.coordinate.toAdditiveLeft.toLinearEquiv (ZMod.map_smul _)
  obtain ⟨f,_,_,hf⟩ := Section08.TransvectionQuotients.FiveSeed.BarMarking.natural_extension
    D.LT D.L D.V le_sup_left (sup_le D.L.le_normalizer d.normalizes_L) d.normalizes_V
    (SourceSixBlock.actor d) (SourceSixBlock.actor_surjective d) aV
    (fun l v => d.conjugation l v.toMul)
  let a := f.comp (inclusion (show (D.T : Subgroup G) ≤ D.LT from le_sup_right))
  have hk : a.ker = (D.LT.pCoreIn 2).subgroupOf (D.T : Subgroup G) := by
    ext t
    change inclusion (show (D.T : Subgroup G) ≤ D.LT from le_sup_right) t ∈ f.ker ↔
      (t : G) ∈ D.LT.pCoreIn 2
    rw [hf]
    change (t : G) ∈ centralizer (D.V : Set G) ↔ (t : G) ∈ D.LT.pCoreIn 2
    exact ⟨fun ht => h.sylow_centralizer.le ⟨t.property,ht⟩,
      fun ht => (h.sylow_centralizer.ge ht).2⟩
  have hr : IsPGroup 2 a.range :=
    D.T.isPGroup'.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  obtain ⟨S,hS⟩ := hr.exists_le_sylow
  have hSc : Nat.card S = 16 := by
    rw [S.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have har : Nat.card a.range ≤ 16 := (card_le_of_le hS).trans_eq hSc
  have hkc : Nat.card a.ker = Nat.card (D.LT.pCoreIn 2) := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe
      (h.sylow_centralizer.symm.le.trans inf_le_left)).toEquiv
  have hm := card_eq_card_quotient_mul_card_subgroup a.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv,hkc] at hm
  calc
    Nat.card D.T = Nat.card a.range * Nat.card (D.LT.pCoreIn 2) := hm
    _ ≤ 16 * Nat.card (D.LT.pCoreIn 2) := Nat.mul_le_mul_right _ har

/-- The original Sylow group has order at most 512, without maximality of L. -/
theorem original_sylow_card_le : Nat.card D.T ≤ 512 :=
  (original_sylow_card_le_mul_core d h).trans
    (Nat.mul_le_mul_left 16 (original_core_elementary_bound d h e hseed hn hU).2)

omit e hseed hn hU in
/-- Once the original core equals the natural module, the Sylow order is at most 256. -/
theorem original_sylow_card_le_of_core_eq_module (hQ : D.LT.pCoreIn 2 = D.V) :
    Nat.card D.T ≤ 256 := by
  have hb := original_sylow_card_le_mul_core d h
  rwa [hQ,ReturningPlane.module_card d] at hb


/-- Every Sylow two-subgroup of the literal upper quotient has order at most 32. -/
theorem upper_quotient_sylow_card_le {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (S : Sylow 2 (I ⧸ pCore 2 I)) : Nat.card S ≤ 32 := by
  obtain ⟨P,rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective (pCore 2 I)) 2 S
  let q := QuotientGroup.mk' (pCore 2 I)
  have hm := relIndex_mul_card_of_le (pCore_isPGroup.le_sylow_of_normal P)
  have hi := relIndex_ker (P : Subgroup I) q
  rw [QuotientGroup.ker_mk'] at hi
  rw [hi] at hm
  have hP : Nat.card P ≤ Nat.card D.T := by
    have hb := card_le_sylow_two (P.isPGroup'.map I.subtype) D.T
    rwa [card_map_of_injective I.subtype_injective] at hb
  have hb := hP.trans (original_sylow_card_le d h e hseed hn hU)
  have hc := upper_core_card d h e hseed hn hU hI hLI
  change Nat.card ((P : Subgroup I).map q) ≤ 32
  rcases hc with hc | hc <;> rw [hc] at hm <;> omega

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperCore
