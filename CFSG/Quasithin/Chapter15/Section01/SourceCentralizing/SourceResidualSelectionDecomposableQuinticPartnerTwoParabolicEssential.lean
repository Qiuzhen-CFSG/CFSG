module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoParabolicMaximal
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SeedOffender

/-!
# The E-generated essential action on the actual moving parabolic

The residual movement of E produces an essential irreducible action in its
actual P-span. That span is a normal elementary subgroup of the full V-span.
The same minimum maximum quadratic actor from the two-chief equality is a
sharp offender on this irreducible section. Its seed remains an element of E.
-/

public section
open scoped IsMulCommutative ENNReal
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open NoncentralChiefRefinement NoncentralChiefRefinement.BinaryFlag
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter3 Representation.EssentialResidualQuotient
variable {G : Type*} [Group G] [Finite G]

section Coordinates
variable {H : Type*} [Group H] [Finite H]
 (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

omit [IsElementaryAbelian 2 U] in
private theorem exists_series_containing {A B : NormalNode H}
    (hab : A ⋖ B) (hBU : B.val ≤ U) :
    ∃ s : SeriesOn U, ∃ i : Fin s.series.length,
      s.lower i = A ∧ s.upper i = B := by
  obtain ⟨s,hs0,hsl⟩ := exists_chiefSeries (⊥ : NormalNode H) A bot_le
  have hstep : s.last ⋖ B := hsl ▸ hab
  let s' : ChiefSeries H := s.snoc B hstep
  obtain ⟨t,ht0,htl⟩ := exists_chiefSeries B ⟨U,inferInstanceAs U.Normal⟩ hBU
  have hst : s'.last = t.head := (RelSeries.last_snoc s B hstep).trans ht0.symm
  let d : SeriesOn U := {
    series := s'.smash t hst
    head_eq := by simpa only [s',RelSeries.head_smash,RelSeries.head_snoc] using hs0
    last_eq := (RelSeries.last_smash hst).trans htl }
  refine ⟨d,(Fin.last s.length).castAdd t.length,?_,?_⟩
  · exact (RelSeries.smash_castAdd (p := s') (q := t) hst (Fin.last s.length)).trans
      ((RelSeries.snoc_castSucc s B hstep (Fin.last s.length)).trans hsl)
  · exact (RelSeries.smash_succ_castAdd (p := s') (q := t) hst (Fin.last s.length)).trans
      (RelSeries.last_snoc s B hstep)

private def baseMap : Map (⟨U,inferInstanceAs U.Normal⟩ : NormalNode H) (normalRepresentation U) where
  hom := {
    toFun := fun u => Multiplicative.ofAdd (Additive.ofMul u)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  equivariant _ _ := rfl

private theorem nested_irreducible_coordinates
    (F : Subgroup H) [F.Normal] [IsElementaryAbelian 2 F] (hFU : F≤U)
    (W : Subrepresentation (normalRepresentation F))
    (P : Subrepresentation W.quotientRepresentation) [Representation.IsIrreducible P.toRepresentation]
    (hn : ∃ h v, P.toRepresentation h v ≠ v) :
    ∃ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i ∧
      ∃ e : Additive (s.Factor i) ≃ₗ[ZMod 2] P.toSubmodule,
        ∀ h v, e (s.factorRepresentation i h v) = P.toRepresentation h (e v) := by
  let q := (baseMap F).onQuotient W
  have hq : Function.Surjective q.hom :=
    (baseMap F).onQuotient_surjective W (fun x => ⟨x.toAdd.toMul,rfl⟩)
  let c := q.submoduleCoordinates P hq
  have hc := c.covBy (q.preimage_mono bot_le) hn
  have hpre : (q.preimage P).val≤F := q.preimage_le P
  obtain ⟨s,i,hi,hj⟩ := exists_series_containing U hc (hpre.trans hFU)
  let d : SectionCoordinates (s.lower i) (s.upper i) P.toRepresentation 1 := by
    rw [hi,hj]
    exact c
  have hnc : ¬ s.Central i := d.not_isCentral (by decide) hn
  let f : Additive (s.Factor i) ≃+ P.toSubmodule := {
    toFun := fun v => (d.equiv v.toMul).toAdd 0
    invFun := fun v => Additive.ofMul (d.equiv.symm (Multiplicative.ofAdd (fun _ => v)))
    left_inv := by
      intro v
      apply Additive.toMul.injective
      apply d.equiv.injective
      change d.equiv (d.equiv.symm (Multiplicative.ofAdd
        (fun _ => (d.equiv v.toMul).toAdd 0))) = d.equiv v.toMul
      rw [d.equiv.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      funext j
      exact congrArg (d.equiv v.toMul).toAdd (Subsingleton.elim 0 j)
    right_inv := by intro v; exact congrArg (fun x => x.toAdd 0) (d.equiv.apply_symm_apply _)
    map_add' := by intro v w; exact congrArg (fun x => x.toAdd 0) (d.equiv.map_mul v.toMul w.toMul) }
  let e : Additive (s.Factor i) ≃ₗ[ZMod 2] P.toSubmodule :=
    { f with map_smul' := ZMod.map_smul f }
  exact ⟨s,i,hnc,e,fun h v => d.equivariant h v.toMul 0⟩
end Coordinates

private theorem essential_seed_from_movement (P E : Subgroup G)
    [IsElementaryAbelian 2 ((conjugateSpan P E).subgroupOf P)]
    (S : Sylow 2 P) (hEP : E≤P)
    (hSN : (S:Subgroup P).map P.subtype≤normalizer (E:Set G))
    (hp : ChapterB.IsMinimalParabolicOver S ⊤)
    (hm : ¬(pResidual 2 P).map P.subtype≤centralizer (E:Set G)) :
    Nonempty (EssentialSeedAction P E S hEP) := by
  let F := (conjugateSpan P E).subgroupOf P
  let ρ := normalRepresentation F
  have hFP : conjugateSpan P E≤P := by
    rw [conjugateSpan_eq]
    exact conjugateSpanBy_le_self hEP
  have hmove : moved ρ (pResidual 2 P)≠⊥ := by
    apply moved_ne_bot_of_not_le_ker
    rw [MultipleFactors.normalRepresentation_ker]
    intro hh
    apply hm
    rintro _ ⟨r,hr,rfl⟩ e he
    exact congrArg P.subtype (hh hr ⟨e,hEP he⟩ (le_conjugateSpan P E he))
  obtain ⟨W,hW,hmax,hi,he,hfixed,hSylow⟩ := exists_residual_quotient ρ hmove
  have hWtop : W≠⊤ := fun hh=>hW (hh ▸ le_top)
  obtain ⟨q,hqSeed,hqne,hqS⟩ := exists_nonzero_fixed_seed W.quotientRepresentation S
    (quotientSeed P E W) (quotientSeed_stable P E S hSN W)
    (quotientSeed_ne_bot P E hEP W hWtop)
  have hqsocle := hSylow S hqS
  obtain ⟨u,huSeed,huq⟩ := hqSeed
  let v:E := ⟨(u.toMul.val:G),huSeed⟩
  have huv : spanSeedVector P E hEP v=u := rfl
  refine ⟨{
    kernel:=W
    seed:=v
    avoids:=hW
    maximal:=hmax
    irreducible:=hi
    essential:=he
    residual_fixed:=hfixed
    seed_mem:=?_
    seed_nonzero:=?_
    seed_sylow_fixed:=?_
    seed_centralizer_fixed:=?_
    original_minimal:=hp }⟩
  · rw [huv,huq]
    exact hqsocle
  · rw [huv,huq]
    exact hqne
  · rw [huv,huq]
    exact hqS
  · intro x hx
    apply quotientSeed_fixed_by_centralizer P E W x hx
    exact ⟨_,v.property,rfl⟩

set_option maxHeartbeats 800000 in
/-- The original full span supplies one minimum quadratic maximum actor,
with the balanced global ranks and a sharp offender on an actual essential
action generated from the moving fixed subgroup E. -/
theorem PreparedChosenModule.outside_minimalParabolic_fixed_essential_actor
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V P : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T:Subgroup G)≤centralizer (localModule T M:Set G))
    (h : PreparedChosenModule T M V)
    (hP : P∈Chapter1.HOver G (T:Set G))
    (hp : ChapterB.IsMinimalParabolicOver T P) (hout : ¬P≤M)
    (hVP : V≤P.pCoreIn 2)
    (hmove : ¬(pResidual 2 P).map P.subtype≤centralizer (thompsonFixed T V:Set G)) :
    let E := thompsonFixed T V
    let U := (conjugateSpan P V).subgroupOf P
    let F := (conjugateSpan P E).subgroupOf P
    let S := T.subtype hP.2
    ∃ (heU : IsElementaryAbelian 2 U) (heF : IsElementaryAbelian 2 F) (hEP : E≤P),
      letI := heU
      letI := heF
      ∃ A∈elementaryAbelianMaxSubgroups (S:Subgroup P),
        ¬A≤pCore 2 P ∧ IsQuadratic (normalRepresentation U) A ∧
        (∀ B∈elementaryAbelianMaxSubgroups (S:Subgroup P),
          ¬B≤pCore 2 P → (pCore 2 P).relIndex A≤(pCore 2 P).relIndex B) ∧
        U≤pCore 2 P ∧ A⊓centralizer (U:Set P)≤pCore 2 P ∧
        2*Nat.log 2 ((pCore 2 P).relIndex A)=fixedCodim (normalRepresentation U) A ∧
        fixedCodim (normalRepresentation U) A=
          2*Nat.log 2 ((centralizer (U:Set P)).relIndex (A⊓pCore 2 P)) ∧
        U⊓centralizer (A:Set P)=U⊓centralizer (A⊓pCore 2 P:Set P) ∧
        ∃ a : EssentialSeedAction P E S hEP,
          IsOffender a.imageRepresentation (A.map a.projection) ∧
          rank (A.map a.projection)=fixedCodim a.imageRepresentation (A.map a.projection) := by
  let d := h.outside_minimalParabolic_qrc hG T hempty hM hJ hP hp hout
  let := h.elementary
  have hq : quadraticRatio (imageRepresentation (chosenNormalizer T M V) V d.module_normalized)=2 :=
    (chosenNormalizer_quadraticRatio_eq T hM.1.2 h.normalized).trans h.quadratic_ratio
  have hn := source_notFF_of_ratio_two d hq
  let he := source_elementary_span_of_notFF d hVP hn
  let := he
  let E := thompsonFixed T V
  let U := (conjugateSpan P V).subgroupOf P
  let F := (conjugateSpan P E).subgroupOf P
  let S := T.subtype hP.2
  have hUP : conjugateSpan P V≤P := (span_le_right_core d hVP).trans (twoCore_le P)
  let heU : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUP
  let := heU
  have hFU : F≤U := by
    intro f hf
    have hh : conjugateSpan P E≤conjugateSpan P V := by
      rw [conjugateSpan_eq,conjugateSpan_eq]
      exact conjugateSpanBy_mono (show E≤V from inf_le_left) le_rfl
    exact hh hf
  let heF : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le hFU
  let := heF
  have hEP : E≤P := (show E≤V from inf_le_left).trans (hVP.trans (pCoreIn_le 2 P))
  have hS : (S:Subgroup P).map P.subtype=(T:Subgroup G) := map_subgroupOf_eq_of_le hP.2
  have hip := source_intrinsic_minimalParabolic_of_notFF d h.nontrivial hn S hS
  have hSN : (S:Subgroup P).map P.subtype≤normalizer (E:Set G) := by
    rw [hS]
    obtain ⟨ht,hn,_⟩ := h.thompsonFixed_escape_join_residual T hM
    exact ht.trans hn
  obtain ⟨a⟩ := essential_seed_from_movement P E S hEP hSN hip hmove
  obtain ⟨A,hA,hAQ,hquad,hmin⟩ := source_quadratic_minimal_max_actor d h.nontrivial hVP hn S hS
  have hkernel : A⊓centralizer (U:Set P)≤pCore 2 P :=
    (inf_le_inf_right _ hA.1).trans (source_span_centralizer_sylow_le_core d h.nontrivial hVP hn S hS)
  have hnc : ¬A≤centralizer (U:Set P) := fun ha=>hAQ ((le_inf le_rfl ha).trans hkernel)
  have heq (s:SeriesOn U) := source_sqtk_multiple_equalities d h.nontrivial hVP
    (Chapter3.sqtk_of_mem_H hG hP.1) hq S hS s
    (by have hc := (h.outside_minimalParabolic_two_chiefs hG T hempty hM hJ hP hp hout hVP).2 s; omega)
    A hA hquad hnc
  have hff (s:SeriesOn U) (i:Fin s.series.length) (hi:¬s.Central i) :
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) ∧
      rank (actionSubgroup (s.factorRepresentation i) A)=
        fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A) := by
    let : IsElementaryAbelian 2 A := hA.2.1
    have hk := MultipleFactors.source_chief_sylow_kernel U S hip s i hi A hA.1
    have hnA : ¬A≤(s.factorRepresentation i).ker := by
      intro hh
      have hx : A⊓(s.factorRepresentation i).ker=A := inf_eq_left.mpr hh
      rw [hx] at hk
      exact hAQ (hk.le.trans inf_le_right)
    have hidx : (s.factorRepresentation i).ker.relIndex A=(pCore 2 P).relIndex A := by
      rw [←inf_relIndex_left,hk,inf_relIndex_left]
    have hh : rank (actionSubgroup (s.factorRepresentation i) A)=
        fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
          (actionSubgroup (s.factorRepresentation i) A) := by
      rw [rank_actionSubgroup_eq_log_relIndex,fixedCodim_actionSubgroup,hidx]
      exact (heq s).2.2.2.2.1 i hi
    exact ⟨⟨elementary_actionSubgroup _ hnA,hh.ge⟩,hh⟩
  let := a.irreducible
  have hna : ∃ g v, a.representation g v≠v := by
    by_contra! hh
    apply a.projection_kernel_ne_top
    apply top_unique
    intro g _
    exact (actionHom_eq_one_iff a.representation g).mpr (hh g)
  obtain ⟨s,i,hi,e,hee⟩ := nested_irreducible_coordinates U F hFU a.kernel a.socle hna
  have hsharp := sharp_image_offender_of_equivariant a.representation (s.factorRepresentation i)
    e (fun g v=>(hee g v).symm) (hff s i hi).1 (hff s i hi).2
  have hUQ : U≤pCore 2 P := by
    intro u hu
    obtain ⟨x,hx,hxu⟩ := span_le_right_core d hVP hu
    exact P.subtype_injective hxu ▸ hx
  exact ⟨heU,heF,hEP,A,hA,hAQ,hquad,hmin,hUQ,hkernel,
    (heq s).2.1,(heq s).2.2.1,(heq s).2.2.2.1,a,hsharp⟩

end CFSG.Quasithin.Chapter15.Section01
