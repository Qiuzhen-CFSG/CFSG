module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

/-!
# The original Borel residual fixes a nonzero quotient seed

Mark the actual Sylow normalizer in C/O₂(C) as the projective Borel, and
transport its lifted two-residual through the literal component image in
I/O₂(I). The outside-component Borel identity makes this lifted residual
centralize V. Seed separation retains its nonzero vectors in every proper
invariant quotient of the original local section.

Source: Aschbacher–Smith 14.7.41–42, printed pp.1061–1062.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam AlternatingSevenSource
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original outside linear-three Borel residual has a nonzero fixed
seed in every proper quotient, under an actual component marking. -/
theorem local_linear_borel_fixed_seed_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent)
    (hout : ¬ F.Li L 1 ≤ C.map I.subtype)
    {E : Type} [Field E] [Finite E] [CharP E 2]
    {n : ℕ} (hE : Nat.card E = 2 ^ n) (hn : 1 < n)
    (e : (C ⧸ pCore 2 C) ≃* PSL(3,E))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤) :
    let K := C.map (QuotientGroup.mk' (pCore 2 I))
    ∃ (e' : K ≃* PSL(3,E)) (B : Subgroup K),
      B.map e'.toMonoidHom = Representation.HigherFieldBorelFixedSpaces.twoResidualImage
        (Matrix.PSL3.LinearThree.borel E) ∧
      ∃ v : (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I))) ⧸ N.toSubmodule,
        v ≠ 0 ∧ ∀ b : B, N.quotientRepresentation b.val.val v = v := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let qC := QuotientGroup.mk' (pCore 2 C)
  let K := C.map q
  let r : C →* K := q.subgroupMap C
  let f := I.subtype.comp C.subtype
  let B₀ := componentSylowNormalizer T I C
  let B₁ := (pResidual 2 B₀).map B₀.subtype
  obtain ⟨P,_,hpre⟩ := componentSylowNormalizer_quotient I (F.sylow_le_of_mem_Hz hI) C
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))
  let J := normalizer (Q : Set (C ⧸ pCore 2 C))
  let J₀ := J.comap qC
  let R := (pResidual 2 J₀).map J₀.subtype
  have hR : R.map f = B₁ := by
    change ((pResidual 2 J₀).map J₀.subtype).map f = (pResidual 2 B₀).map B₀.subtype
    rw [map_embedded_pResidual,show J₀.map f = B₀ from hpre.symm]
  obtain ⟨e₀,he₀⟩ := RankTwo.exists_borel_marking (by omega : 0 < n) hE e Q
  let e' : K ≃* PSL(3,E) := (cComponentTwoCoreQuotientEquiv hC).symm.trans e₀
  let B := R.map r
  have hr : e'.toMonoidHom.comp r = e₀.toMonoidHom.comp qC := by
    ext c
    exact congrArg e₀ ((cComponentTwoCoreQuotientEquiv hC).symm_apply_apply (qC c))
  have hB : B.map e'.toMonoidHom = Representation.HigherFieldBorelFixedSpaces.twoResidualImage
      (Matrix.PSL3.LinearThree.borel E) := by
    change (R.map r).map e'.toMonoidHom = _
    rw [map_map,hr,←map_map]
    change (((pResidual 2 (J.comap qC)).map (J.comap qC).subtype).map qC).map
      e₀.toMonoidHom = _
    rw [map_embedded_pResidual,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      map_embedded_pResidual,he₀]
  have hcentral : B₁ ≤ centralizer (V : Set G) :=
    (component_borel_fixed_actions_at d h hab structural previous faithful earlier
      I hI C hout).1
  let c := localQuotientSection a
  let p := localQuotientProjection a N
  let W := (c.imageSpace V).map p.toLinearMap
  have hdim : Module.finrank (ZMod 2) W = 2 :=
    local_quotient_seed_finrank h hI c p (localQuotientProjection_ker_ne_top a N hN)
  have hW : W ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hdim
    omega
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨e',B,hB,v,hv0,?_⟩
  intro b
  obtain ⟨z,hz,hzb⟩ := b.property
  have hzB : f z ∈ B₁ := hR ▸ mem_map_of_mem f hz
  have hcomm : ⁅B₁,V⁆ ≤ F.Vi 1 :=
    (commutator_eq_bot_iff_le_centralizer.mpr hcentral).le.trans bot_le
  obtain ⟨w,hw,hww⟩ := hv
  have hfix : a.representation (q z.val) w = w :=
    c.fixed_on_imageSpace_of_commutator_le B₁ V hcomm z.val hzB w hw
  have hfixN := congrArg p hfix
  have hbq : q z.val = b.val.val := congrArg Subtype.val hzb
  change N.quotientRepresentation (q z.val) (p w) = p w at hfixN
  change p w = v at hww
  rwa [hbq,hww] at hfixN

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideProjectiveAt
