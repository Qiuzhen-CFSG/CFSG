module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ParabolicApplication
public import Theory.Representation.BinaryPermutationEightCover.Dimension
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.SpecificGroups.SymmetricEight.CentralPairResidual

/-!
# The original A₅ source orders in the A₈ branch

The augmentation core surjects onto the whole original module. Its
Sylow-central involution has displacement rank at least three, whereas the
original seed has rank two. The whole module consequently has dimension six,
so the original central extension U_H has order128.

The literal local intersection with the selected A₈ component is a marked
even pair stabilizer. It contains the original local residual, hence has the
same embedded two-residual. Transporting the model residual's two-core and
then using the exact star quotient gives the original star core order32.

Source: Aschbacher–Smith13.5.23, printed p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open ComponentReduction Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ : Subgroup G} [IsElementaryAbelian 2 D.V]
  (d : Context D.T D.L D.V D.V₁ V₂ D.Vplus) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : D.H ∈ Section08.Source.Hz D.L₁ D.T
    (centralizer (D.V₁ : Set G)) (normalizer (D.L : Set G)))
  (hnot : ¬ ModelConclusion G 5)
  (hU : ¬ IsMulCommutative D.UH)
  (K : Subgroup G) (s : Selected D K) (hLK : D.L₁ ≤ K)
  (f : Catalogue.actor D K ≃* alternatingGroup (Fin 8))
  (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
  (hfV : ∀ b : Catalogue.actor D K, ∀ u,
    centralProjection D h fV (Action.starRepresentation D h b.val u) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (f b)
        (centralProjection D h fV u))
include d h hA312 hH hnot hU s hLK f hfV

/-- The whole original module has dimension six. -/
theorem alternating_eight_source_dimension : Module.finrank (ZMod 2) (Action.Space D)=6 := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  have hm:=source_local_component_commutator d h hA312 hH hnot K s
  obtain ⟨m,hmsur,hmeq,_⟩:=alternating_eight_core_quotient D h s d.hypothesis.qtke.properK
    hSQ hLK hm d.third_eq_commutator f fV hfV
  let B:=Catalogue.actor D K
  have hBK : B=starImage D.H K:=alternating_eight_actor_eq_component D h s hSQ hLK hm f
  have hn:=normal_in_H s h hSQ hLK hm
  let : (starImage D.H K).Normal:=hn.map (QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)
  let : B.Normal:=hBK ▸ inferInstance
  obtain ⟨R,hR⟩:=(starSylow D h).exists_subgroupOf_eq_of_normal B
  let S:=R.mapSurjective (f:=f.toMonoidHom) f.surjective
  have hvcard:=LocalGeometry.star_V_card_two h d.third_index hU
  have hvbot:starImage D.H D.V≠⊥:=by
    intro he
    rw [he,card_bot] at hvcard
    omega
  obtain ⟨v,hv,hv1⟩:=(Subgroup.bot_or_exists_ne_one _).resolve_left hvbot
  let vb:B:=⟨v,(show starImage D.H D.V≤B from le_sup_right) hv⟩
  have hvR:vb∈(R:Subgroup B):=by
    rw [hR]
    exact (map_mono (comap_mono h.V_le_T)) hv
  have hvS:f vb∈(S:Subgroup (alternatingGroup (Fin 8))):=mem_map_of_mem _ hvR
  have hvne:f vb≠1:=fun he=>hv1 (congrArg Subtype.val (f.injective (he.trans f.map_one.symm)))
  have hTC:=Fitting.star_centralizes_V D h d.third_index hU D.T h.T_normalizes_V
  have hSC:(S:Subgroup (alternatingGroup (Fin 8)))≤centralizer ({f vb}:Set (alternatingGroup (Fin 8))):=by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f a * f vb = f vb * f a
    rw [←map_mul,←map_mul]
    apply congrArg f
    apply Subtype.ext
    have haT:a.val∈starImage D.H D.T:=by
      rw [hR] at ha
      exact ha
    exact (hTC haT v hv).symm
  have hc:=Theory.SpecificGroups.SymmetricEight.CentralPair.central_in_sylow_conjugate S
    (f vb) hvS hvne hSC
  have hmodule:=local_seed_module_conditions d h hU
  have hdisp : LinearMap.range (Action.starRepresentation D h vb.val-LinearMap.id)≤Action.seedSpace D:=by
    rintro _ ⟨w,rfl⟩
    rw [←hmodule.1]
    exact Submodule.subset_span ⟨v,hv,w,Submodule.mem_top,rfl⟩
  have hr:Module.finrank (ZMod 2) (LinearMap.range (Action.starRepresentation D h vb.val-LinearMap.id))≤2:=by
    calc
      _ ≤ Module.finrank (ZMod 2) (Action.seedSpace D):=Submodule.finrank_mono hdisp
      _ = 2:=hmodule.2.2
  exact BinaryPermutation.EightCover.finrank_six_of_core_surjection m hmsur
    (centralProjection D h fV) (fV.surjective.comp (Submodule.mkQ_surjective _))
    (f vb) hc (Action.starRepresentation D h vb.val) (hmeq vb) hr

/-- Restoring the original central point doubles the module order. -/
theorem alternating_eight_source_UH_card : Nat.card D.UH=128 := by
  have hdim:=alternating_eight_source_dimension d h hA312 hH hnot hU K s hLK f fV hfV
  have hc : Nat.card (Action.ModuleGroup D)=64 := by
    change Nat.card (Action.Space D)=64
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,hdim]
    norm_num
  have hp : D.V₁≤D.UH:=h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hpC:Nat.card (D.V₁.subgroupOf D.UH)=2:=
    (Nat.card_congr (subgroupOfEquivOfLe hp).toEquiv).trans h.point_card
  have hh:=(D.V₁.subgroupOf D.UH).card_mul_index
  rw [hpC,index_eq_card] at hh
  change 2*Nat.card (Action.ModuleGroup D)=Nat.card D.UH at hh
  rw [hc] at hh
  omega

omit hfV [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)] in
/-- The original local residual has star two-core of order32. -/
theorem alternating_eight_source_localCore_card :
    Nat.card (starImage D.H (D.L₁.pCoreIn 2)) = 32 := by
  have hSQ := (Chapter1.Section02.uniqueness_local_quotient_sqtk
    d.hypothesis.qtke hH.1.1).stronglyQuasithin
  have hm := source_local_component_commutator d h hA312 hH hnot K s
  obtain ⟨g, hg⟩ := alternating_eight_pair_marking D h s hSQ hLK hm d.third_index hU f
  let B := Catalogue.actor D K
  let J := localStar D ⊓ B
  let P := Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer.subgroupOf
    (alternatingGroup (Fin 8))
  have hLB : starImage D.H D.L₁ ≤ B := (map_mono (comap_mono hLK)).trans le_sup_left
  have hr : (pResidual 2 J).map J.subtype = starImage D.H D.L₁ := by
    rw [embedded_pResidual_eq_of_le_of_residual_le 2 (show J ≤ localStar D from inf_le_left)]
    · exact localStar_twoResidual D h
    · rw [localStar_twoResidual D h]
      exact le_inf le_sup_left hLB
  let eJ : J ≃* (localStar D).subgroupOf B :=
    (((localStar D).subgroupOf B).equivMapOfInjective B.subtype B.subtype_injective |>.trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype (localStar D) B))).symm
  let e : J ≃* P := eJ.trans ((f.subgroupMap ((localStar D).subgroupOf B)).trans
    ((MulEquiv.subgroupCongr hg).trans ((MulAut.conj g).subgroupMap P).symm))
  let eR : pResidual 2 J ≃* pResidual 2 P :=
    (e.subgroupMap (pResidual 2 J)).trans
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))
  let eL : starImage D.H D.L₁ ≃* pResidual 2 P :=
    (((pResidual 2 J).equivMapOfInjective J.subtype J.subtype_injective).trans
      (MulEquiv.subgroupCongr hr)).symm.trans eR
  let eC : pCore 2 (starImage D.H D.L₁) ≃* pCore 2 (pResidual 2 P) :=
    (eL.subgroupMap (pCore 2 (starImage D.H D.L₁))).trans
      (MulEquiv.subgroupCongr (pCore_map_iso 2 eL))
  rw [starImage_twoCore D.H D.L₁ (le_sup_left.trans h.local_le),pCoreIn,
    card_map_of_injective (starImage D.H D.L₁).subtype_injective,
    Nat.card_congr eC.toEquiv]
  exact Theory.SpecificGroups.SymmetricEight.CentralPair.residual_twoCore_card
/-- The two literal source orders in the A₈ natural central quotient case. -/
theorem alternating_eight_source_orders :
    Nat.card D.UH = 128 ∧ Nat.card (starImage D.H (D.L₁.pCoreIn 2)) = 32 :=
  ⟨alternating_eight_source_UH_card d h hA312 hH hnot hU K s hLK f fV hfV,
    alternating_eight_source_localCore_card d h hA312 hH hnot hU K s hLK f⟩

end CFSG.Quasithin.Chapter13.Section05.A5Source
