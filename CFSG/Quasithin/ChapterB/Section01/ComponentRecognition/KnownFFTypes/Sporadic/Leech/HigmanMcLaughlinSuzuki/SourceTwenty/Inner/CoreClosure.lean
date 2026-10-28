module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.Inner.Inputs
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
public import Theory.ElementaryAbelian.ExtraspecialAbelianBound
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Order five in an HS centralizer-conjugate closure

The actual core of the centralizer of `coreInvolution` is (Q₈ * Q₈) * C₄.
An elementary subgroup E of this core has order at most eight: adjoining the
central cyclic factor D gives an abelian subgroup F, whose intersection with
the extraspecial subgroup B of order 32 contains Z(B). The extraspecial
pairing bound gives |F ∩ B| ≤ 8, hence |F| ≤ 16. Since |E ∩ D| ≤ 2,
the product formula then gives |E| ≤ 8.

A rank-four actor therefore has nontrivial image in the actual S₅ quotient.
Its normal closure inside the centralizer has image containing A₅, so five
divides the order of that closure. Cauchy's theorem produces an element of
order five in the closure itself. Its ambient image lies in the literal
`centralizerConjugateClosure`; no complement to the core is asserted.
Conjugacy transports the full centralizer extension to every required t.

This discharges `Inner.CoreClosureFive`, the group input consumed by
`Inner.rank_four_bound`. Source: Guralnick--Malle, *Classification of
2F-modules, I*, Proposition 5.1, HS paragraph, preprint pp.16--17;
Aschbacher--Smith K.4, printed p.457. The centralizer structure is the proved
16.1.5(10) / GLS3 Table 5.3m model, with its embedded factors and quotient.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner
open Subgroup Representation.BinaryOffender
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims

private theorem core_shape_elementary_card_le {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsQuaternionSquareCyclicFourProduct Q)
    (E : Subgroup Q) (hE : IsElementaryAbelian 2 E) : Nat.card E ≤ 8 := by
  classical
  let := hE
  obtain ⟨B, D, ⟨d⟩, ⟨eD⟩, hBD, hc, hs⟩ := hQ
  have hDcomm : IsMulCommutative D :=
    ⟨⟨fun x y => eD.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
  let := hDcomm
  have hDZ : D ≤ center Q := by
    intro z hz
    have hgen : B ⊔ D ≤ centralizer ({z} : Set Q) := by
      apply sup_le
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr (hc b hb z hz)
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hDcomm.is_comm.comm (⟨y, hy⟩ : D) ⟨z, hz⟩))
    exact mem_center_iff.mpr fun x =>
      mem_centralizer_singleton_iff.mp (hgen (hs ▸ mem_top x))
  have hBnormal : (⊤ : Subgroup Q) ≤ normalizer (B : Set Q) := by
    rw [← hs]
    exact sup_le B.le_normalizer ((show D ≤ centralizer (B : Set Q) from
      fun z hz b hb => hc b hb z hz).trans (centralizer_le_normalizer _))
  have hDC : D ≤ centralizer (E : Set Q) := by
    intro z hz x _
    exact mem_center_iff.mp (hDZ hz) x
  let F := E ⊔ D
  have hFcomm : IsMulCommutative F := by
    apply le_centralizer_iff_isMulCommutative.mp
    exact sup_le
      (le_centralizer_iff.mpr (sup_le E.le_centralizer hDC))
      (le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hDC) D.le_centralizer))
  let := hFcomm
  have hcenterBD : center B = D.subgroupOf B := by
    symm
    apply eq_of_le_of_card_ge
    · intro z hz
      exact mem_center_iff.mpr fun b => Subtype.ext (hc b b.property z hz)
    · rw [d.center_card, ← inf_subgroupOf_left D B]
      rw [Nat.card_congr (subgroupOfEquivOfLe
        (show B ⊓ D ≤ B from inf_le_left)).toEquiv]
      exact hBD.ge
  let K := F.subgroupOf B
  have hKcomm : IsMulCommutative K :=
    F.comap_injective_isMulCommutative B.subtype_injective
  let := hKcomm
  let := d.extraspecial
  have hZK : center B ≤ K := by
    rw [hcenterBD]
    intro x hx
    exact (show D ≤ F from le_sup_right) hx
  have hKbound := extraspecial_two_abelian_card_sq_le K hZK
  rw [d.card] at hKbound
  have hKB : Nat.card (B ⊓ F : Subgroup Q) ≤ 8 := by
    have he : Nat.card K = Nat.card (B ⊓ F : Subgroup Q) := by
      change Nat.card (F.subgroupOf B) = _
      rw [← inf_subgroupOf_left F B]
      exact Nat.card_congr (subgroupOfEquivOfLe
        (show B ⊓ F ≤ B from inf_le_left)).toEquiv
    rw [he] at hKbound
    nlinarith
  have hQcard : Nat.card Q = 64 := HSInner.shape_card ⟨B, D, ⟨d⟩, ⟨eD⟩, hBD, hc, hs⟩
  have hFcard : Nat.card F ≤ 16 := by
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes B F
      (le_top.trans hBnormal)
    have hsup : Nat.card (B ⊔ F : Subgroup Q) ≤ 64 :=
      hQcard ▸ (B ⊔ F).card_le_card_group
    rw [d.card] at hprod
    nlinarith
  have hED : Nat.card (D ⊓ E : Subgroup Q) ≤ 2 := by
    let R := {x : C4 // x ^ 2 = 1}
    have hR : Nat.card R = 2 := by rw [Nat.card_eq_fintype_card]; decide
    let f : (D ⊓ E : Subgroup Q) → R := fun x => ⟨eD ⟨x, x.property.1⟩, by
      rw [← map_pow]
      have hx : (⟨x, x.property.1⟩ : D) ^ 2 = 1 :=
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : Q) x.property.2)
      rw [hx, map_one]⟩
    have hf : Function.Injective f := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : D => (z : Q))
        (eD.injective (congrArg Subtype.val hxy)))
    exact hR ▸ Nat.card_le_card_of_injective f hf
  have hDcard : Nat.card D = 4 := by
    rw [Nat.card_congr eD.toEquiv]
    simp [C4]
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes D E
    ((le_centralizer_iff.mp hDC).trans (centralizer_le_normalizer _))
  rw [hDcard, sup_comm D E] at hprod
  change 4 * Nat.card E = Nat.card (D ⊓ E : Subgroup Q) * Nat.card F at hprod
  nlinarith

private theorem normalClosure_five {C : Type*} [Group C] [Finite C]
    (Q : Subgroup C) [Q.Normal] (e : C ⧸ Q ≃* S5)
    (A : Subgroup C) (hAQ : ¬ A ≤ Q) :
    ∃ x ∈ normalClosure (A : Set C), orderOf x = 5 := by
  let f : C →* S5 := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective Q)
  let N := normalClosure (A : Set C)
  let M := N.map f
  let : M.Normal := Subgroup.Normal.map inferInstance f hf
  have hM : M ≠ ⊥ := by
    intro hM
    apply hAQ
    intro a ha
    have hfa : f a ∈ M := mem_map_of_mem f (subset_normalClosure ha)
    have hfa1 : f a = 1 := mem_bot.mp (hM ▸ hfa)
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hfa1.trans e.map_one.symm)
  have hAlt : alternatingGroup (Fin 5) ≤ M :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((nontrivial_iff_ne_bot _).mpr hM)
  have hAltCard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hdiv : 5 ∣ Nat.card N := by
    exact dvd_trans (by decide : 5 ∣ 60)
      (dvd_trans (hAltCard ▸ card_dvd_of_le hAlt) (N.card_map_dvd f))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 hdiv
  exact ⟨x, x.property, (orderOf_injective N.subtype N.subtype_injective x).trans hx⟩

private theorem normalClosure_le_centralizerClosure {G : Type*} [Group G]
    (A : Subgroup G) (t : G) :
    (normalClosure (A.subgroupOf (centralizer ({t} : Set G)) :
      Set (centralizer ({t} : Set G)))).map (centralizer ({t} : Set G)).subtype ≤
      centralizerConjugateClosure A t := by
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hax
  change (c : G) * (a : G) * (c : G)⁻¹ ∈ centralizerConjugateClosure A t
  apply (le_iSup (fun c : centralizer ({t} : Set G) =>
    A.map (MulAut.conj (c : G)).toMonoidHom) c)
  exact mem_map_of_mem (MulAut.conj (c : G)).toMonoidHom ha

/-- Every rank-four elementary actor containing a core-class involution generates,
under its full centralizer, a subgroup with an actual element of order five. -/
theorem coreClosureFive : CoreClosureFive := by
  let : Finite HS := _root_.Sporadic.LeechRelated.HS.carrierFinite
  intro A hA hr t ht hc
  let := hA.2
  let C := centralizer ({t} : Set HS)
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hA.2.toIsMulCommutative.is_comm.comm
        (⟨a, ha⟩ : A) ⟨t, ht⟩))
  obtain ⟨ef⟩ := HSInner.fixed_equiv_centralizer_of_isConj hc
  let ec : C ≃* centralizer ({coreInvolution} : Set HS) :=
    (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj t)).symm.trans ef
  have hC : IsHSCoreExtension C :=
    HSInner.coreExtension_transport ec.symm HSInner.centralizer_coreExtension
  obtain ⟨Q, hQ, hshape, ⟨eQ⟩⟩ := hC
  let := hQ
  let E := A.subgroupOf C
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hAC
  have hEcard : Nat.card E = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv,
      hA.card_eq_two_pow_rank, hr]
    norm_num
  have hEQ : ¬ E ≤ Q := by
    intro h
    let := hE
    have hb := core_shape_elementary_card_le hshape (E.subgroupOf Q)
      (IsElementaryAbelian.subgroupOf h)
    rw [Nat.card_congr (subgroupOfEquivOfLe h).toEquiv, hEcard] at hb
    omega
  obtain ⟨x, hx, ho⟩ := normalClosure_five Q eQ E hEQ
  refine ⟨x.val, ?_, ?_⟩
  · exact normalClosure_le_centralizerClosure A t (mem_map_of_mem C.subtype hx)
  · exact (orderOf_injective C.subtype C.subtype_injective x).trans ho

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Inner
