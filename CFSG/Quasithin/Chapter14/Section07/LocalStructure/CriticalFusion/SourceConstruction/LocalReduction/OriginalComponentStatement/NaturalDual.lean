module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BorelGraph
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NativeSelection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.NaturalSections.NoFF.NativeSource
public import Theory.Representation.SL3FourNaturalDual.HomogeneousOrbit

/-!
# The original SL₃(4) natural-plus-dual module

The actual point cubic is the component center and is fixed-free on U_I/V₁.
Native B.5.1 excludes FF modules for the original graph extension. Its two
strict inequalities on a submodule and quotient, combined with the original
quadratic actor, force every nonzero moved submodule to be the whole section.
Native B.4.5 selects a natural constituent homogeneous under the actual Sylow
image. Its graph translate is disjoint; automorphism coverage shows that
these two constituents exhaust the orbit. Their embeddings give full binary
natural-plus-dual coordinates, retaining the component inclusion and center.

The quotient action is the literal original conjugation action. Inverting
the original inverter converts left conjugation to the right graph relation
used by the representation lemmas. No constituent, splitting or whole-module
recognition is assumed. SpecialLinearExclusion applies this to every original
component after constructing its C L₁ T reduction. Earlier structural inputs
remain explicit and are not inferred from same-group guarded hypotheses.

Source: Aschbacher–Smith 14.7.44, printed p.1062, using B.4.5, B.5.1,
F.9.18(4,7), refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.SL3FourNaturalDual
open CFSG CFSG.Quasithin
open Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved

universe w
private theorem graph_coordinates {D U : Type w} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U] [Module.Finite (ZMod 2) U] [Finite U]
    (ρ : Representation (ZMod 2) D U) (K P : Subgroup D) [K.Normal] [IsQuasisimple K]
    (hsq : IsSQTK KnownSimple.IsKnownSimple D) (eK : K ≃* SL)
    (hcore : pCore 2 D = ⊥) (hgen : K ⊔ P = ⊤) (hP : IsPGroup 2 P)
    (hf : Function.Injective ρ) (t : P) (c : Matrix.GeneralLinearGroup (Fin 3) F)
    (ht : ∀ g, (eK.symm g : D) * t = t * (eK.symm
      (Matrix.PSL3.OuterSolvable.linearConjSL F c
        (Matrix.SpecialLinearGroup.inverseTranspose g)) : D))
    (x : D) (hx : x ∈ (center K).map K.subtype)
    (hfree : ∀ v, ρ x v = v → v = 0)
    (A : Subgroup D) (hAP : A ≤ P) (hA : IsElementaryTwo A)
    (hq : IsQuadratic ρ A) (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : A ⊓ centralizer (K : Set D) = ⊥) :
    ∃ (e : K ≃* SL) (E : U ≃ₗ[ZMod 2] Representation.SL3FourNaturalDual.V),
      ∀ (k : K) v, E (ρ k v) = representation (e k) (E v) := by
  have hquot := quotient_isPGroup_of_sup_eq_top P K hP ((sup_comm _ _).trans hgen)
  have hm : subspaceCommutator ρ ⊤ K = ⊤ :=
    full_of_fixedFree K ρ x ((map_subtype_le _) hx) hfree
  have hsat (S : Subrepresentation ρ) (hS : S.toSubmodule ≠ ⊥)
      (hfull : subspaceCommutator ρ S.toSubmodule K = S.toSubmodule) :
      S.toSubmodule = ⊤ :=
    (NoFF.Native.moved_space ρ (hsq.subgroup K) eK hquot hcore t c ht x hx hfree
      S hS hfull A hA hc).trans hm
  obtain ⟨I,hI,_,e,⟨n⟩⟩ := NaturalRecognition.Native.quadratic_natural_constituent
    ρ K eK hsq hf x hx hfree A P hP hAP hA hq hc hAC
  let O := Homogeneous.orbitSubrepresentation ρ hI.normalizes hI.isIrrPlus hgen
  have hspan : Homogeneous.orbitSpan ρ P I = ⊤ := hsat O
    (Homogeneous.orbitSpan_ne_bot ρ hI.isIrrPlus)
    (Homogeneous.orbitSpan_full_commutator ρ hI.normalizes hI.isIrrPlus)
  have hirr : IsIrreducible ρ := by
    let : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr (hI.isIrrPlus.ne_bot ρ)
    let : Nontrivial U := Function.Injective.nontrivial I.subtype_injective
    rw [Representation.IsIrreducible,isSimpleOrder_iff]
    refine ⟨inferInstance,fun S => ?_⟩
    by_cases hS : S.toSubmodule = ⊥
    · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
    · right
      apply Subrepresentation.toSubmodule_injective
      apply hsat S hS
      have hfull := full_of_fixedFree K S.toRepresentation x ((map_subtype_le _) hx)
        (fun v hv => Subtype.ext (hfree v (congrArg Subtype.val hv)))
      have he := subspaceCommutator_map_embedding ρ S.toRepresentation (MonoidHom.id D)
        S.toSubmodule.subtype (fun _ _ => rfl) K ⊤
      simpa only [Subgroup.map_id,hfull,Submodule.map_top,Submodule.range_subtype] using he
  obtain ⟨c',ht'⟩ := Matrix.PSL3Even.GraphRemarking.graph_relation_trans K.subtype eK
    (eK.symm.trans e) t c ht
  have he : eK.trans (eK.symm.trans e) = e := by
    apply MulEquiv.ext
    intro k
    exact congrArg e (eK.symm_apply_apply k)
  rw [he] at ht'
  have hmove := graph_moves_natural_section ρ (K.subtype.comp e.symm.toMonoidHom)
    t I (n.lift hI.isIrrPlus.choose_spec.1) c'
    (n.lift_symm_equivariant hI.isIrrPlus.choose_spec.1) ht'
  have hdis := ((hI.isIrrPlus.eq_or_disjoint_conjugate_of_normal_restriction ρ hirr K
    (t : D)).resolve_left hmove).symm
  have hpair := HomogeneousOrbit.natural_orbit_span ρ hI e n t c' ht'
  have hcompl : IsCompl I (I.map (ρ t)) :=
    ⟨hdis,codisjoint_iff.mpr (hpair.symm.trans hspan)⟩
  let m := graphSumMarking ρ (K.subtype.comp e.symm.toMonoidHom) t I
    (n.lift hI.isIrrPlus.choose_spec.1) c' hcompl
    (n.lift_symm_equivariant hI.isIrrPlus.choose_spec.1) ht'
  refine ⟨e,m.coordinates,fun k v => ?_⟩
  have he : m.actor (e k) = k := congrArg Subtype.val (e.symm_apply_apply k)
  exact he ▸ m.equivariant (e k) v

open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The full original U_I/V₁ has natural-plus-dual coordinates for the literal
component image in I/O₂(I), with no module recognition premise. -/
theorem reduced_special_linearThree_four_coordinates
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* SL)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    let B := C.map (QuotientGroup.mk' (pCore 2 I))
    ∃ (eB : B ≃* SL)
      (E : Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)) ≃ₗ[ZMod 2]
        Representation.SL3FourNaturalDual.V),
      ∀ (k : B) v, E (a.representation k v) = representation (eB k) (E v) := by
  have hfield : Nat.card Representation.SL3FourNaturalDual.F = 2^2 := by
    rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]
    rfl
  obtain ⟨_,hAn,hAZ,_⟩ := local_even_special_linearThree_center_and_inverter
    d h hab structural previous faithful earlier I hI C hC hfield (by decide) e
  obtain ⟨_,hCN,t,g,m,hgraph⟩ := local_even_special_linearThree_graph
    d h hab structural previous faithful earlier I hI C hC hfield (by decide) (by decide) e
  let := hCN
  let := hAn
  let q := QuotientGroup.mk' (pCore 2 I)
  let B := C.map q
  let P := ((T : Subgroup G).subgroupOf I).map q
  let X := ((F.Li L 1).subgroupOf I).map q
  let : B.Normal := hCN.map q (QuotientGroup.mk'_surjective _)
  let ec := cComponentTwoCoreQuotientEquiv hC
  let : IsQuasisimple B :=
    (local_component_twoCore_isQuasisimple h hab structural previous faithful I hI C hC).of_mulEquiv ec
  have hBP : B ⊔ P = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hsup : B ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map q = ⊤ := by
    apply top_unique
    apply hBP.ge.trans
    apply sup_le_sup_left
    exact map_mono (show (T : Subgroup G).subgroupOf I ≤
      (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I from fun x hx => mem_sup_right hx)
  obtain ⟨hU,b,_,A,hAR,hA,hquad,hcod,hAC⟩ :=
    local_prime_supplement_quadratic_actor h hab structural previous I hI B hsup
  have heq := a.representation_eq b
  rw [←heq] at hquad hcod
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (F.Li L 1 ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hAP : A.map q ≤ P := map_mono (hAR.trans (show
    (F.Ri L 1).subgroupOf I ≤ (T : Subgroup G).subgroupOf I from fun x hx => hRT hx))
  have hX : Nat.card X = 3 :=
    local_point_star_card_of_normal h structural I (F.Li_one_le_of_mem_Hz hI) hAn
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 (by rw [hX])
  have hxne : x ≠ 1 := by intro he; simp [he] at hx
  have hxgen : zpowers (x : HStar I) = X := by
    have hh := congrArg (Subgroup.map X.subtype) (zpowers_eq_top_of_prime_card hX hxne)
    simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,
      Subgroup.coe_subtype] using hh
  have hfree : ∀ v, a.representation x v = v → v = 0 := by
    intro v hv
    have hvX := (mem_fixedSpace_zpowers_iff a.representation (x : HStar I) v).mpr hv
    rw [hxgen,local_point_fixedSpace_eq_bot h structural I
      (F.Li_one_le_of_mem_Hz hI) hAn a] at hvX
    exact hvX
  let e' := e.trans (MulAut.conj g)
  let eB : B ≃* SL := ec.symm.trans e'
  let tI : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let ts : P := ⟨(q tI)⁻¹,P.inv_mem (mem_map_of_mem q t.property.1)⟩
  have hact (z : C ⧸ pCore 2 C) :
      (ec (normalQuotientAction C (pCore 2 C) tI z) : HStar I) =
        q tI * (ec z : HStar I) * (q tI)⁻¹ := by
    obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C) z
    rw [normalQuotientAction_apply_mk]
    change q (tI*(c : I)*tI⁻¹) = q tI * q (c : I) * (q tI)⁻¹
    rw [map_mul,map_mul,map_inv]
  have ht : ∀ k, (eB.symm k : HStar I) * ts = ts * (eB.symm
      (Matrix.PSL3.OuterSolvable.linearConjSL Representation.SL3FourNaturalDual.F m
        (Matrix.SpecialLinearGroup.inverseTranspose k)) : HStar I) := by
    intro k
    have hg := MulEquiv.congr_fun hgraph k
    have hgr : Matrix.PSL3.OuterSolvable.graphSL Representation.SL3FourNaturalDual.F k =
        Matrix.SpecialLinearGroup.inverseTranspose k := by
      apply Subtype.ext
      exact (Matrix.adjugate_transpose k.val).symm
    change e' (normalQuotientAction C (pCore 2 C) tI (e'.symm k)) =
      Matrix.PSL3.OuterSolvable.linearConjSL Representation.SL3FourNaturalDual.F m
        (Matrix.PSL3.OuterSolvable.graphSL Representation.SL3FourNaturalDual.F k) at hg
    rw [hgr] at hg
    have hz := congrArg (fun z => (ec (e'.symm z) : HStar I)) hg
    rw [e'.symm_apply_apply,hact] at hz
    change (ec (e'.symm k) : HStar I) * (q tI)⁻¹ =
      (q tI)⁻¹ * (ec (e'.symm _) : HStar I)
    rw [←hz]
    group
  exact graph_coordinates a.representation B P (local_star_sqtk h I hI) eB
    (pCore_quotient_pCore_eq_bot 2) hBP (T.isPGroup'.comap_subtype.map q)
    a.faithful ts m ht x (hAZ ▸ x.property) hfree (A.map q) hAP hA hquad hcod hAC

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement
