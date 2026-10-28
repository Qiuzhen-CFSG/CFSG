module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.RankTwo
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueChiefInterval
/-!
# The unique noncentral partner chief factor

The saturated chief section contains V intersect O₂(Mc), and its lower
endpoint meets that intersection in the central seed Z. Hence the marked
actor fixes each chief section between Z and the lower endpoint and each
section above the upper endpoint. Every nontrivial irreducible binary
action of the partner join has kernel O₂ of that join, so these fixed
sections are central. Refine the three outer strata and use equivariant
Jordan–Hölder to obtain exactly one noncentral factor in every chief
series on the literal partner two-core.

The source specialization constructs the saturated section and its actor;
it assumes no chief count, action model, or partner-core containment.
The earlier quotient and structural alternatives have the same producers
as RankTwo, and their final discharge remains with the Section 15.2 owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
15.2.27(2), printed p.1119.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

private theorem central_chief_of_actor
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∀ (A B : NormalNode L), A ⋖ B → IsPGroup 2 B.val →
      ∀ a : L, a ∉ pCore 2 L →
      (∀ b ∈ B.val, ⁅a,b⁆ ∈ A.val) → IsCentral A B := by
  dsimp only
  intro A B hc hp a ha hfix
  let := chief_elementary A B hc hp
  let ρ := binarySectionRepresentation A B
  let := binarySection_irreducible A B hc
  by_contra hnc
  have hnρ : ∃ g, ρ g ≠ 1 := by
    by_contra! hh
    exact hnc ((binarySection_trivial_iff A B).mp (MonoidHom.ext hh))
  have hk := source_chosen_partner_irreducible_kernel h hg hquotient hres hs hn ρ hnρ
  apply ha
  rw [←hk]
  change ρ a = 1
  ext x
  obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x.toMul
  change sectionAction A B a x.toMul = x.toMul
  rw [←hb,sectionAction_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change a * (b : _) * a⁻¹ / (b : _) ∈ A.val
  simpa only [commutatorElement_def,div_eq_mul_inv] using hfix b b.property

/-- Saturation and an actor outside the two-core force the literal chief count. -/
theorem source_chosen_partner_unique_chief_of_saturation
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∀ (B U : NormalNode L), B ⋖ U →
      U.val.map L.subtype ≤ twoCoreIn Mc →
      centralInvolutions T ≤ B.val.map L.subtype →
      V ⊓ twoCoreIn Mc ≤ U.val.map L.subtype →
      (V ⊓ twoCoreIn Mc) ⊓ B.val.map L.subtype = centralInvolutions T →
      (¬ IsCentral B U) →
      (∃ a : L, (a : G) ∈ V ∧ a ∉ pCore 2 L) →
      ∀ s : ChiefSeries L, s.head = ⊥ →
        s.last.val = (twoCoreIn Mc).subgroupOf L → s.noncentralTwoCount = 1 := by
  dsimp only
  intro B U hc hU hB hCU hker hnc ha s hs0 hs1
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  obtain ⟨a,ha,hao⟩ := ha
  have hTM : (T : Subgroup G) ≤ Mc := hg.outside.1.1.2.trans hg.in_partner
  have hKM : partnerSpan H Mc ≤ Mc :=
    conjugateSpanBy_le_self ((map_subtype_le _).trans hg.in_partner)
  have hLM : L ≤ Mc := sup_le hKM hTM
  let Q := (twoCoreIn Mc).subgroupOf L
  have hNQ : Mc ≤ normalizer (twoCoreIn Mc : Set G) := by
    simpa only [twoCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      (pCore 2 Mc).le_normalizer_map Mc.subtype
  let : Q.Normal := normal_subgroupOf_of_le_normalizer (hLM.trans hNQ)
  have hpQ : IsPGroup 2 Q := (isPGroup_pCoreIn 2 Mc).comap_subtype
  let Z := (centralInvolutions T).subgroupOf L
  have hLZ : L ≤ centralizer (centralInvolutions T : Set G) := hLM.trans hMc.le
  let : Z.Normal := normal_subgroupOf_of_le_normalizer
    (hLZ.trans (Subgroup.centralizer_le_normalizer _))
  let ZN : NormalNode L := ⟨Z,inferInstanceAs Z.Normal⟩
  have hz : IsCentral (⊥ : NormalNode L) ZN := by
    rw [isCentral_iff_commutator_le]
    apply (commutator_top_left_eq_bot_iff_le_center.mpr ?_).le
    intro z hz
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext ((hLZ x.property z hz).symm)
  have hZU : ZN ≤ B := by
    intro z hz
    exact (mem_map_iff_mem L.subtype_injective).mp (hB hz)
  have hUQ : U.val ≤ Q := map_le_iff_le_comap.mp hU
  have hlo (C D : NormalNode L) (hZC : ZN ≤ C) (hDB : D ≤ B) (hCD : C ⋖ D) :
      IsCentral C D := by
    apply central_chief_of_actor h hg hquotient hres hs hn C D hCD
      (hpQ.to_le ((show D.val ≤ B.val from hDB).trans
        ((show B.val ≤ U.val from hc.le).trans hUQ))) a hao
    intro b hb
    apply hZC
    change (⁅a,b⁆ : L).val ∈ centralInvolutions T
    rw [←hker]
    refine ⟨?_,?_⟩
    · exact source_chosen_partner_core_commutator_le h hg
        (commutator_mem_commutator ha (hU (mem_map_of_mem L.subtype (hc.le (hDB hb)))))
    · have hbcomm : ⁅a,b⁆ ∈ B.val := by
        apply hDB
        simpa only [commutatorElement_def] using
          D.val.mul_mem (D.property.conj_mem b hb a) (D.val.inv_mem hb)
      exact mem_map_of_mem L.subtype hbcomm
  have hhi (C D : NormalNode L) (hUC : U ≤ C) (hDQ : D.val ≤ Q) (hCD : C ⋖ D) :
      IsCentral C D := by
    apply central_chief_of_actor h hg hquotient hres hs hn C D hCD
      (hpQ.to_le hDQ) a hao
    intro b hb
    apply hUC
    apply (mem_map_iff_mem L.subtype_injective).mp
    exact hCU (source_chosen_partner_core_commutator_le h hg
      (commutator_mem_commutator ha (hDQ hb)))
  let ss : SeriesOn Q := ⟨s,hs0,Subtype.ext hs1⟩
  rw [←ss.noncentralCount_eq_twoCount hpQ]
  exact ss.noncentralCount_eq_one_of_central_chief_intervals
    hpQ ZN B U hz hZU hc hnc hUQ hlo hhi

/-- In the noncore branch, every chief series on the actual partner two-core
has exactly one noncentral factor, with no extra recognition premise. -/
theorem source_chosen_partner_unique_noncentral_chief
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hn : ¬ V ≤ twoCoreIn Mc) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    ∀ s : ChiefSeries L, s.head = ⊥ →
      s.last.val = (twoCoreIn Mc).subgroupOf L → s.noncentralTwoCount = 1 := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ := source_chosen_partner_saturated_chief
    h hg hMc hZ hquotient hres hs hn
  let hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,he,_,⟨a,ha,ho,_,hr⟩,_,_,hCU,hker,_⟩ := hσ
  have hao : a ∉ pCore 2 L := by
    intro ha
    have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    rw [hqa,orderOf_one] at ho
    contradiction
  have hnc : ¬ IsCentral B U := by
    intro hcen
    have hid := (binarySection_trivial_iff B U).mpr hcen
    have haid : σ (q a) = 1 := by
      have heq := congrArg (fun r : Representation (ZMod 2) L (Additive (Section B U)) => r a) he
      change σ (q a) = _ at heq
      rw [hid] at heq
      exact heq
    rw [haid,sub_self,LinearMap.range_zero] at hr
    simp at hr
  exact source_chosen_partner_unique_chief_of_saturation h hg hMc hquotient hres hs hn
    B U hc hU hB hCU hker hnc ⟨a,ha,hao⟩

end CFSG.Quasithin.Chapter15.Section02
