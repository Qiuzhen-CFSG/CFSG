module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.RepeatedPrefixes
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryRecombination
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ExtensionClauses
/-!
# The complete reducible binary B.5.1 source branch

Semisimplicity gives a complement to the actual maximal chief-flag term.
Strict dimension induction makes that proper term a repeated natural module;
the literal last chief quotient identifies the complement as natural. The
proved recombination theorem gives a repeated sum or the natural-plus-dual
exception. Its ratio premise follows from earlier B.4.2 on that same chief
factor, and the flag budget supplies the required multiplicity bound.

The original consumer proves G=L and every local source hypothesis, narrows
the induction to the actual moved dimension, transports the resulting chart
back to the original component, and constructs all six source conclusions.
The only recursive premise classifies strictly smaller-dimensional modules.

Source: Aschbacher--Smith B.5.1, printed pp.101--103, cases (A)--(C).
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups ENNReal
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
private theorem ratio_le_actionEquiv {H X : Type*} [Group H]
    [AddCommGroup X] [Module (ZMod 2) X] {σ : Representation (ZMod 2) H X}
    (e : ActionEquiv ρ σ) : quadraticRatio σ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA,hq⟩
  have hAm : IsElementaryTwo (A.map e.groupEquiv.toMonoidHom) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 A := hA.2
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro hh
    apply hA.1
    apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
    simpa only [Subgroup.map_bot] using hh
  have hqm : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ w
    obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
    have hh := congrArg e.linearEquiv (hq a ha b hb v)
    change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
      σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
    simpa only [e.intertwines,map_sub] using hh
  have hr : actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
    unfold actionRatio
    rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
      rank_map_injective _ e.groupEquiv.injective]
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom) (iInf_le_of_le ⟨hAm,hqm⟩ hr.le)

/-- A complement has the marked action of the actual top chief quotient. -/
theorem natural_complement_of_top_section (U W : Subrepresentation ρ)
    (hc : IsCompl U.toSubmodule W.toSubmodule) (F : BinaryField) {d : ℕ}
    (hn : IsLinearNatural (sectionRepresentation ρ U ⊤) F d) :
    IsLinearNatural W.toRepresentation F d := by
  let N := sectionLower ρ U ⊤
  let f : W.toSubmodule →ₗ[ZMod 2] ((⊤ : Subrepresentation ρ).toSubmodule ⧸ N.toSubmodule) :=
    N.toSubmodule.mkQ.comp (Submodule.topEquiv.symm.toLinearMap.comp W.toSubmodule.subtype)
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hc.disjoint (x.val-y.val)
    · exact (Submodule.Quotient.eq N.toSubmodule).mp he
    · exact W.toSubmodule.sub_mem x.property y.property
  have hs : Function.Surjective f := by
    intro q
    obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective q
    have hv : v.val ∈ U.toSubmodule ⊔ W.toSubmodule := hc.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨w,hw⟩,?_⟩
    apply (Submodule.Quotient.eq N.toSubmodule).mpr
    change w-v.val ∈ U.toSubmodule
    rw [← he]
    simpa only [sub_add_eq_sub_sub,sub_self,zero_sub,sub_sub_cancel_left] using U.toSubmodule.neg_mem hu
  obtain ⟨a⟩ := hn
  exact ⟨⟨a.groupEquiv,(LinearEquiv.ofBijective f ⟨hi,hs⟩).trans a.linearEquiv,
    fun g v => a.intertwines g (f v)⟩⟩

/-- Recombine the complete original binary flag, with the ratio premise discharged. -/
theorem binary_source_flag_recombined [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤)
    (hsemi : IsSemisimpleRepresentation ρ) :
    (IsRepeatedLinearNatural ρ BinaryField.two d f.length ∧ f.length ≤ d-1) ∨
      IsNaturalPlusDual ρ d := by
  classical
  let := hsemi
  have hgen : generalizedFitting G ⊔ A = ⊤ := by rw [hwhole,top_sup_eq]
  obtain ⟨hindices,_⟩ := binary_source_flag_pure ρ hK earlier hsq hf hcore hd mark f A hA hgen hm
  have hlen : 1 < f.length := by
    have hh := f.multiple
    rwa [hindices,Finset.card_range] at hh
  let i := f.length-1
  have hi0 : 0 < i := by omega
  have hil : i < f.length := by omega
  have hlast : i+1 = f.length := by omega
  have hi : i ∈ f.noncentral := hindices ▸ Finset.mem_range.mpr hil
  obtain ⟨hU,_⟩ := binary_source_flag_repeated ρ hK earlier ih hsq hwhole hf hcore hd mark f A hA hm hi0 hil
  let U := f.chain i
  obtain ⟨W,hW⟩ := exists_isCompl U
  have hc : IsCompl U.toSubmodule W.toSubmodule := by
    let e : Subrepresentation ρ ≃o Submodule (MonoidAlgebra (ZMod 2) G) ρ.asModule :=
      Subrepresentation.subrepresentationSubmoduleOrderIso
    have hs := congrArg (fun P : Submodule (MonoidAlgebra (ZMod 2) G) ρ.asModule => P.restrictScalars (ZMod 2))
      ((e.isCompl_iff.mp hW).sup_eq_top)
    rw [Submodule.restrictScalars_sup] at hs
    exact ⟨disjoint_iff.mpr (congrArg Subrepresentation.toSubmodule hW.inf_eq_bot),
      codisjoint_iff.mpr hs⟩
  let τ := sectionRepresentation ρ (f.chain i) (f.chain (i+1))
  obtain ⟨a⟩ := (binary_flag_natural ρ hK earlier hsq hf hcore hd mark f A hA hgen i hi).2
  have hnτ : IsLinearNatural τ BinaryField.two d := by
    let g := ((MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv).symm
    exact ⟨⟨g.trans a.groupEquiv,a.linearEquiv,fun x v => a.intertwines (g x) v⟩⟩
  have hnQ : IsLinearNatural (sectionRepresentation ρ U ⊤) BinaryField.two d := by
    change IsLinearNatural (sectionRepresentation ρ (f.chain i) (f.chain (i+1))) BinaryField.two d at hnτ
    rwa [hlast,f.top] at hnτ
  have hnW := natural_complement_of_top_section ρ U W hc BinaryField.two hnQ
  have hb := f.estimates ρ hf inferInstance hcore A hA
  have hlo := binary_flag_ratio_lower ρ hK earlier hsq hcore hd mark f hi ((hb.2.2.1 i hi).2.le)
  rw [image_ratio_of_faithful τ (binary_flag_factor_faithful ρ hd mark f hi)] at hlo
  obtain ⟨b⟩ := hnτ
  have hquarter : (1/4 : ℝ≥0∞) ≤ quadraticRatio (linearNatural BinaryField.two d) := by
    have hbase : (1/4 : ℝ≥0∞) ≤ 1/(d-1 : ℕ) := by rcases hd with rfl | rfl <;> norm_num
    exact (hbase.trans hlo).trans (ratio_le_actionEquiv _ (ExtensionConsequences.actionSymm b))
  have hff : IsFFModule ρ := ⟨A,hA.1.isOffender ρ⟩
  rcases BinaryRecombination.binary_recombine_repeated ρ hff U W hc hd hi0 hU hnW hquarter with hn | ⟨_,hn⟩
  · left
    rw [hlast] at hn
    exact ⟨hn,binary_source_flag_length ρ hK earlier hsq hf hcore hd mark f A hA hindices⟩
  · exact Or.inr hn

private theorem coinvariants_top_of_actionEquiv
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) H X} (e : ActionEquiv ρ σ)
    (hm : Coinvariants.ker ρ = ⊤) : Coinvariants.ker σ = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := e.linearEquiv.surjective v
  have he : Coinvariants.ker ρ ≤ (Coinvariants.ker σ).comap e.linearEquiv.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,w⟩,rfl⟩
    change e.linearEquiv (ρ g w - w) ∈ Coinvariants.ker σ
    rw [map_sub,e.intertwines]
    exact Coinvariants.sub_mem_ker (e.groupEquiv g) (e.linearEquiv w)
  exact he (hm ▸ Submodule.mem_top)

/-- The strict induction yields the genuine binary action alternatives on [V,L]. -/
theorem binary_reducible_action [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2)) :
    ∃ s : MovedSection ρ L, L = generalizedFitting G ∧
      SourceInduction.ProjectiveLine.QuasisimpleActionCase ρ L s := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  have hL := binary_reducible_whole ρ hK earlier h hnot hd mark
  have hfit := binary_source_fitting ρ h hd mark
  obtain ⟨s,A,hA,f,hindices,hn,hpure⟩ := binary_moved_pure_flag ρ hK earlier h hnot hd mark
  let μ := s.space.toRepresentation
  let H := L ⊔ A
  let σ : Representation (ZMod 2) H s.space.toSubmodule := μ.comp H.subtype
  have hH : H = ⊤ := by change L ⊔ A = ⊤; rw [hL,top_sup_eq]
  have hμ := moved_source_hypothesis ρ h s hfit
  have hl := local_source_hypothesis μ L h.sqtk hfit h.twoCore hμ.faithful hA.1
  have hfitH : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore (hA.1.1.2.isPGroup 2 A)
  have hwhole : generalizedFitting H = ⊤ := by
    simp only [hfitH,hL,Subgroup.top_subgroupOf]
  let : IsQuasisimple (generalizedFitting H) := hfitH.symm ▸ hl.quasisimple
  have hsq : IsSQTK K (generalizedFitting H) := hfitH.symm ▸ hl.sqtk
  let E : ActionEquiv ((⊤ : Subrepresentation σ).toRepresentation.comp (generalizedFitting H).subtype) σ :=
    ⟨(MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv,Submodule.topEquiv,fun _ _ => rfl⟩
  have ht := hpure f.length le_rfl
  rw [f.top] at ht
  have hm : Coinvariants.ker σ = ⊤ := coinvariants_top_of_actionEquiv _ E ht.1
  have hz : σ.invariants = ⊥ := ExtensionConsequences.invariants_of_equiv
    (ExtensionConsequences.actionSymm E) ht.2
  have hff : IsFFModule σ :=
    ⟨A.subgroupOf H,((hA.1.subgroupOf μ le_sup_right).isOffender _)⟩
  have ihU : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) s.space.toSubmodule) := by
    intro D _ _ X _ _ _ τ C hdX hs
    exact ih D X τ C (hdX.trans_le (Submodule.finrank_le _)) hs
  have hsem := binary_semisimple_of_natural_flag σ ihU hsq hwhole hl.twoCore hm hz hff
    f hindices hd (fun i hi => (hn i hi).2.2)
  let E' : ActionEquiv σ (σ.comp (generalizedFitting H).subtype) :=
    ⟨((MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv).symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hmF := coinvariants_top_of_actionEquiv σ E' hm
  let markH := (MulEquiv.subgroupCongr hfitH).trans
    ((subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).trans mark)
  have hAH : A ≤ H := le_sup_right
  have hmin : IsMinimalBestOffender σ (A.subgroupOf H) := by
    refine ⟨hA.1.subgroupOf μ hAH, ?_⟩
    intro B hB hBA
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH]
    apply hA.2 _ (hB.map_subtype μ)
    refine ⟨(map_mono hBA.1).trans_eq (map_subgroupOf_eq_of_le hAH), ?_⟩
    have hw := hBA.2
    rw [weight_comp_map μ H.subtype H.subtype_injective,
      weight_comp_map μ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hAH] at hw
    exact hw
  have hrec := binary_source_flag_recombined σ hK earlier ihU hsq hwhole hl.faithful
    hl.twoCore hd markH f (A.subgroupOf H) hmin hmF hsem
  let c : L ≃* H := ((MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv).trans
    ((MulEquiv.subgroupCongr hH).trans Subgroup.topEquiv).symm
  refine ⟨s,hfit.symm,?_⟩
  rcases hrec with ⟨⟨a⟩,hbound⟩ | ⟨a⟩
  · have hr : 0 < f.length := by
      have hh := f.multiple
      rw [hindices,Finset.card_range] at hh
      omega
    exact .repeatedNatural d f.length hd hr hbound hL
      ⟨⟨c.trans a.groupEquiv,a.linearEquiv,fun g v => a.intertwines (c g) v⟩⟩
  · obtain ⟨a⟩ := a
    exact .naturalDual d hd hL
      ⟨⟨c.trans a.groupEquiv,a.linearEquiv,fun g v => a.intertwines (c g) v⟩⟩

/-- All six B.5.1 clauses in the reducible SL4(2)/SL5(2) source branch. -/
theorem binary_reducible_conclusion [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (hroot : NonbinaryG2RootPairInput)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L))
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : L ≃* SL(d,ZMod 2)) :
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) := by
  obtain ⟨s,hfit,hcase⟩ := binary_reducible_action ρ hK earlier ih h hnot hd mark
  exact ⟨conclusion_of_action hroot h s hfit hcase⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
