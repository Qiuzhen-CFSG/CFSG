module
public import Stellmacher.SectionNine.NineSevenResidualTwoArc
public import Stellmacher.SectionNine.NineTenSecondCoreIntersectionAction
public import Theory.GroupTheory.NormalClosureIntersectionNoncentral
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Nontrivial action of the first residual-core intersection

At any neighbor of the retained first vertex, the actual first residual
two-core normally generates the neighboring residual by (7.6)(b). Suppose
the neighboring core acts nontrivially on a subgroup I normal in that
stabilizer, and its commutator with the residual supplements its centralizer
of I. Then the first residual-core intersection with that neighboring core
also acts nontrivially on I.

Transport (7.6)(b) by an element fixing the first vertex. Its first residual
core is preserved. The neighboring core normalizes this group because it
lies in the first stabilizer. Restriction to the actual neighboring
stabilizer now satisfies the general normal-closure intersection theorem;
injective inclusion returns its nonzero commutator to the ambient group.

This is the inference immediately before Stellmacher (9.10)(10), printed
p.58. The final specialization applies the proved second-core action packet
to the literal first/third module intersection at distance five, assuming
only the actual terminal classification (6). Its index four excludes
central action. No replacement critical path or extraction is selected.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_residual_core_intersection_noncentral
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (middle : ctx.Γ.Vertex)
    (hmiddle : middle ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (I : Subgroup G) (hIP : I ≤ GAt ctx.Γ middle)
    (hPI : GAt ctx.Γ middle ≤ Subgroup.normalizer (I : Set G))
    (hgen : QAt ctx.Γ middle =
      ⁅QAt ctx.Γ middle,EAt ctx.Γ middle⁆ ⊔
        (QAt ctx.Γ middle ⊓ Subgroup.centralizer (I : Set G)))
    (hnoncentral : ¬ QAt ctx.Γ middle ≤ Subgroup.centralizer (I : Set G)) :
    ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ⊓ QAt ctx.Γ middle,I⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ middle
  let Q := QAt Γ middle
  let E := EAt Γ middle
  let Pf := GAt Γ cp.firstStep
  let Ef := EAt Γ cp.firstStep
  let R := twoCoreIn Ef
  have hQP : Q ≤ P := by
    change Γ.twoCoreAt middle ≤ Γ.stabilizer middle
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hEP : E ≤ P := by
    change Γ.twoResidualAt middle ≤ Γ.stabilizer middle
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hEf : Ef = twoResidualIn Pf := Γ.twoResidualAt_def _
  have hEfPf : Ef ≤ Pf := hEf ▸ twoResidualIn_le Pf
  have hRPf : R ≤ Pf := (twoCoreIn_le Ef).trans hEfPf
  have hPfR : Pf ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRPf).mp
      (twoCoreIn_normal_of_normal Ef Pf hEfPf (hEf ▸ twoResidualIn_normal Pf))
  have hRfirst : R ≤ QAt Γ cp.firstStep := by
    change twoCoreIn (Γ.twoResidualAt cp.firstStep) ≤ Γ.twoCoreAt cp.firstStep
    rw [Γ.twoResidualAt_def, Γ.twoCoreAt_def, residual_core_eq_inter_core]
    exact inf_le_right
  have hfirstP : QAt Γ cp.firstStep ≤ P :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core cp.firstStep middle hmiddle default).2.2
  have hRP : R ≤ P := hRfirst.trans hfirstP
  have hQPf : Q ≤ Pf :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core middle cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hmiddle))) default).2.2
  have hQR : Q ≤ Subgroup.normalizer (R : Set G) := hQPf.trans hPfR
  let D := Subgroup.normalClosure (R.subgroupOf P : Set P)
  let Dambient := D.map P.subtype
  have hRD : R ≤ Dambient := by
    intro r hr
    exact Subgroup.mem_map_of_mem P.subtype
      (Subgroup.subset_normalClosure (show (⟨r,hRP hr⟩ : P) ∈ R.subgroupOf P from hr))
  have hPD : P ≤ Subgroup.normalizer (Dambient : Set G) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro p hp x ⟨d,hd,rfl⟩
    exact Subgroup.mem_map_of_mem P.subtype
      ((inferInstance : D.Normal).conj_mem d hd ⟨p,hp⟩)
  obtain ⟨mover,hmove⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) hmiddle
  let f := (MulAut.conj (mover:G)⁻¹).toMonoidHom
  have hGmap : (GAt Γ cp.a).map f = P := by
    change conjugateBy (stabilizer Γ cp.a) (mover:G)⁻¹ = stabilizer Γ middle
    rw [← stabilizer_act,hmove]
  have hRmap : R.map f = R :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPfR (Pf.inv_mem mover.property))
  have hEmap : (EAt Γ cp.a).map f = E := by
    change (Γ.twoResidualAt cp.a).map f = Γ.twoResidualAt middle
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def]
    change (twoResidualIn (GAt Γ cp.a)).map f = twoResidualIn P
    rw [← twoResidualIn_map_equiv, hGmap]
  have hclosure : conjugateClosure R (GAt Γ cp.a) ≤ Dambient.comap f := by
    rw [conjugateClosure,Subgroup.closure_le]
    rintro x ⟨a,r,rfl⟩
    change f ((a:G) * (r:G) * (a:G)⁻¹) ∈ Dambient
    rw [map_mul,map_mul,map_inv]
    have ha : f a ∈ P := hGmap ▸ Subgroup.mem_map_of_mem f a.property
    have hr : f r ∈ R := hRmap.le (Subgroup.mem_map_of_mem f r.property)
    exact Subgroup.le_normalizer_iff.mp hPD _ ha _ (hRD hr)
  have hED : E ≤ Dambient := by
    rw [← hEmap]
    apply Subgroup.map_le_iff_le_comap.mpr
    exact (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.2.trans hclosure
  have hEnative : E.subgroupOf P ≤ D := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hEP]
    exact hED
  have hQnative : Q.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt middle).subgroupOf P = pCore 2 P
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  let _ : (Q.subgroupOf P).Normal := hQnative ▸ inferInstance
  let _ : (I.subgroupOf P).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hPI
  have hQRnative : Q.subgroupOf P ≤ Subgroup.normalizer (R.subgroupOf P : Set P) := by
    apply Subgroup.le_normalizer_iff.mpr
    intro q hq r hr
    change (q:G) * (r:G) * (q:G)⁻¹ ∈ R
    exact Subgroup.le_normalizer_iff.mp hQR q hq r hr
  have hCmap : (Q.subgroupOf P ⊓ Subgroup.centralizer
      (I.subgroupOf P : Set P)).map P.subtype = Q ⊓ Subgroup.centralizer (I : Set G) := by
    change (subgroupCentralizerIn (Q.subgroupOf P) (I.subgroupOf P)).map P.subtype =
      subgroupCentralizerIn Q I
    rw [subgroupCentralizerIn_subgroupOf_eq P Q I hIP]
    exact Subgroup.map_subgroupOf_eq_of_le
      (show subgroupCentralizerIn Q I ≤ P from inf_le_left.trans hQP)
  have hgennative : Q.subgroupOf P = ⁅Q.subgroupOf P,E.subgroupOf P⁆ ⊔
      (Q.subgroupOf P ⊓ Subgroup.centralizer (I.subgroupOf P : Set P)) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_commutator,Subgroup.map_subgroupOf_eq_of_le hQP,
      Subgroup.map_subgroupOf_eq_of_le hEP,hCmap]
    exact hgen
  have hQnoncentral : ¬ Q.subgroupOf P ≤ Subgroup.centralizer (I.subgroupOf P : Set P) := by
    intro hle
    apply hnoncentral
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp
      (hle (show (⟨q,hQP hq⟩:P) ∈ Q.subgroupOf P from hq))
        ⟨i,hIP hi⟩ hi)
  have hnonzero := Subgroup.commutator_intersection_ne_bot_of_normalClosure_supplement
    (Q.subgroupOf P) (R.subgroupOf P) (I.subgroupOf P) (E.subgroupOf P)
      hQRnative hEnative hgennative hQnoncentral
  intro hzero
  apply hnonzero
  apply Subgroup.map_injective P.subtype_injective
  rw [Subgroup.map_bot,Subgroup.map_commutator,Subgroup.map_inf _ _ _ P.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hQP,Subgroup.map_subgroupOf_eq_of_le hRP,
    Subgroup.map_subgroupOf_eq_of_le hIP,hzero]

public theorem nine_ten_five_residual_core_intersection_noncentral
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    let third := ctx.criticalPath.path ⟨3, by omega⟩
    ⁅twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep) ⊓ QAt ctx.Γ second,
      VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third⁆ ≠ ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length=5 := hb
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let I := VAt Γ cp.firstStep ⊓ VAt Γ third
  let Q := QAt Γ second
  have hleft : Γ.adjacent second cp.firstStep := by
    have hedge := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hright : Γ.adjacent second third := cp.path_adj ⟨2,by omega⟩
  have hdistinct : cp.firstStep≠third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
  have horbit : IsConjugateVertex Γ cp.a second := ⟨mover,hmover⟩
  obtain ⟨_,_,_,_,hIQ,hPI⟩ := nine_ten_two_step_wreath_classification ctx (by omega)
    hcard hmodel hinter horbit hleft hright hdistinct
  obtain ⟨hindex,hgen⟩ := nine_ten_second_core_intersection_action ctx hb hcard hmodel hinter
  have hQP : Q ≤ GAt Γ second := by
    change Γ.twoCoreAt second ≤ Γ.stabilizer second
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hnoncentral : ¬ Q ≤ Subgroup.centralizer (I : Set G) := by
    intro hle
    have heq : Q ⊓ Subgroup.centralizer (I : Set G) = Q := inf_eq_left.mpr hle
    change Nat.card Q = 4 * Nat.card (Q ⊓ Subgroup.centralizer (I : Set G) : Subgroup G) at hindex
    rw [heq] at hindex
    have hpos : 0 < Nat.card Q := Nat.card_pos
    omega
  exact nine_ten_residual_core_intersection_noncentral ctx.toLocalContext second
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft)) I
      (hIQ.trans hQP) hPI hgen hnoncentral

end Stellmacher.SectionNine
