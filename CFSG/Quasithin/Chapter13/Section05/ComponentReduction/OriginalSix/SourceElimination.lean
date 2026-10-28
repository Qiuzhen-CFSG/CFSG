module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.ChiefCatalogue
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SixFalse
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.SourceHypothesis
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.G2FixedFour
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.CubicFixed
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.EightExclusion
/-!
# Excluding the original nonabelian ordinary-A₆ seed closure

The actual selected configuration has one of three natural central quotients.
For S₆ the same chief series has count three and even count. For A₈ an
original point stabilizer lifts a rank-two cubic subgroup into the plane
centralizer, whose source rank is at most one. For G₂(2)′ the natural
quadratic cover supplies an order-four element fixed by a cubic subgroup;
the original pair layers force that element into an elementary abelian group.

The final applications construct F.9, component selection and the complete
chief catalogue from the original escaping subgroup. Taking that subgroup
to be the point normalizer proves that its seed closure is abelian. If this
closure were nonabelian, the chosen-module TI theorem would itself force
the point normalizer outside the maximal local, so no subgroup-choice or
recognition premise remains.
Source: Aschbacher–Smith13.5.21–25, printed pp.923–925.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h
private theorem symmetric_six_quotient_false
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus:Set G)≤M⊓normalizer (D.V:Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁≤K)
    (hn : (starImage D.H K).Normal)
    (f : Catalogue.actor D K≃*Equiv.Perm (Fin 6))
    (fV : CentralQuotient.Space D h K≃ₗ[ZMod 2]
      Theory.SpecificGroups.SymmetricSix.NaturalModule)
    (hfV : ∀b:Catalogue.actor D K,∀u,
      fV (CentralQuotient.representation D h K hn b.val u)=
        BinaryDuadModule.naturalAction (f b) (fV u)) : False := by
  let q := Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv
  let w := fV.trans q.symm
  apply symmetric_six_source_false d h e hU h1221 hc K s hLK f w
  intro b u
  apply q.injective
  change q (q.symm (fV (CentralQuotient.projection D h K
      (Action.starRepresentation D h b.val u)))) = _
  rw [q.apply_symm_apply,
    Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv_equivariant,
    Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply]
  change fV (CentralQuotient.projection D h K
    (Action.starRepresentation D h b.val u)) =
      BinaryDuadModule.naturalAction (f b)
        (q (q.symm (fV (CentralQuotient.projection D h K u))))
  rw [q.apply_symm_apply, ←CentralQuotient.representation_mk D h K hn, hfV]
/-- The original G₂ natural case contradicts the literal second-layer exponent. -/
theorem g2_source_false
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus:Set G)≤M⊓normalizer (D.V:Set G))
    (K : Subgroup G) (s : Selected D K) (hLK : D.L₁≤K)
    (hn : (starImage D.H K).Normal)
    (f : Catalogue.actor D K≃*commutator (Atlas.G2.Model (ZMod 2)))
    (fV : CentralQuotient.Space D h K≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (hfV : ∀b:Catalogue.actor D K,∀u,
      fV (CentralQuotient.representation D h K hn b.val u)=
        g2DerivedNatural (ZMod 2) (f b) (fV u)) : False := by
  obtain ⟨A,hAL,hA⟩ := CubicParity.exists_cubic d h e
  obtain ⟨j,hjU,hj,hjA⟩ :=
    g2_cubic_fixed_order_four d h e hU h1221 hc K s hLK hn f fV hfV A hAL hA
  have ht := (g2_source_conclusions d h e hU h1221 hc K s hLK hn f fV hfV).2.2.2.2
  exact CubicFixed.order_four_cubic_fixed_false d h e ht hU A hAL hA j hjU hj hjA
/-- Every natural alternative of the original selected configuration is excluded. -/
theorem source_configuration_false
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus:Set G)≤M⊓normalizer (D.V:Set G))
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl) : False := by
  obtain ⟨_,_,hLK,_⟩ := source_component_structure d h e hU K s c
  obtain ⟨_,_,hn,_,_,hnat,_⟩ :=
    source_central_quotient_of_configuration d h e hU h1221 hc K s c
  rcases hnat with ⟨f,fV,_,hfV⟩ | ⟨f,fV,_,hfV⟩ | ⟨f,fV,_,hfV⟩
  · exact symmetric_six_quotient_false d h e hU h1221 hc K s hLK hn f fV hfV
  · apply alternating_eight_source_false d h e hU h1221 hc K s c f fV
    intro b u
    change fV (CentralQuotient.projection D h K
      (Action.starRepresentation D h b.val u)) = _
    rw [←CentralQuotient.representation_mk D h K hn]
    exact hfV b (CentralQuotient.projection D h K u)
  · exact g2_source_false d h e hU h1221 hc K s hLK hn f fV hfV

omit h [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- An actual escaping subgroup in the ordinary-A₆ source family cannot have
nonabelian seed closure. F.9 and its complete configuration are constructed here. -/
theorem source_nonabelian_false
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M)
    (hU : ¬IsMulCommutative D.UH) : False := by
  let h := source_hypothesis d e h1221 hH hU
  let : (D.V₁.subgroupOf D.UH).Normal := Action.point_normal D h
  let : IsElementaryAbelian 2 (Action.ModuleGroup D) := Action.quotient_elementary D h
  have hc := AmbientSource.source_parabolic_centralizer d e h1221
    (source_point_plane_noncentral d D.H (d.first_normalizer ▸ hH.2.1) hU)
  obtain ⟨K,s,c⟩ := exists_source_configuration d h e hU h1221 hc
  let := componentCentralizer_normal s h
    (selected_star_local_normalization s h d.counterexample.qtke (selected_H_mem h))
  exact source_configuration_false d h e hU h1221 hc K s c

omit h [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- Every actual escaping ordinary-A₆ source subgroup has abelian seed closure. -/
theorem source_closure_abelian
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T D.Gz M) :
    IsMulCommutative D.UH := by
  by_contra hU
  exact source_nonabelian_false d e h1221 hH hU
omit h [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
private theorem point_normalizer_mem_Hz_of_nonabelian
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hU : ¬IsMulCommutative (conjugateSpanBy D.Vplus D.Gz)) :
    D.Gz ∈ Section08.Source.Hz D.L₁ D.T D.Gz M := by
  have hPV := d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)
  have hP : D.V₁≠⊥ := by
    intro he
    have hh := d.line_card
    rw [he,card_bot] at hh
    contradiction
  let : IsElementaryAbelian 2 D.V := d.chosen.elementary
  let : IsElementaryAbelian 2 D.V₁ := IsElementaryAbelian.of_le hPV
  have hcore : D.V₁≤D.Gz.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.V₁)
      (d.first_normalizer ▸ D.V₁.le_normalizer) (d.first_normalizer ▸ le_rfl)
  refine ⟨⟨?_,sup_le ?_ (d.first_normalizer ▸ d.line_stable)⟩,le_rfl,?_⟩
  · intro he
    exact hP (bot_unique (he ▸ hcore))
  · exact (map_subtype_le _).trans inf_le_right
  · intro hGM
    have hc : D.V⊓centralizer (D.L:Set G)=⊥ := by
      have hh := congrArg (Subgroup.map D.V.subtype)
        (Section07.ModelExclusions.NaturalModels.centralizer_bot d)
      change ((centralizer (D.L:Set G)).subgroupOf D.V).map D.V.subtype=
        (⊥:Subgroup D.V).map D.V.subtype at hh
      rwa [subgroupOf_map_subtype,Subgroup.map_bot,inf_comm] at hh
    have hTI := d.chosen.ti_of_centralizer_eq_bot h1221
      (fun X _ _=>ChapterA.Section02.theoremA_knownSimple (G:=X))
      (fun X _ _=>ChapterA.Section02.theoremC_knownSimple (G:=X)) hc
    have hGN : D.Gz≤normalizer (D.V:Set G) :=
      (le_inf (hGM.trans d.local_normalizer.le) d.first_normalizer.le).trans
        (inf_normalizer_le_of_trivial_intersections hTI hP hPV)
    have hUV : conjugateSpanBy D.Vplus D.Gz≤D.V := conjugateSpanBy_le d.seed_le hGN
    exact hU (le_centralizer_iff_isMulCommutative.mp
      (hUV.trans ((le_centralizer D.V).trans (centralizer_le hUV))))

omit h [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The seed closure under the actual point normalizer is abelian. The
nonabelian hypothesis itself supplies the escaping source subgroup. -/
theorem source_point_seed_abelian
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L) :
    IsMulCommutative (conjugateSpanBy D.Vplus D.Gz) := by
  by_contra hU
  have hH := point_normalizer_mem_Hz_of_nonabelian d h1221 hU
  exact source_nonabelian_false (D:={D with H:=D.Gz}) d e h1221 hH hU
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
