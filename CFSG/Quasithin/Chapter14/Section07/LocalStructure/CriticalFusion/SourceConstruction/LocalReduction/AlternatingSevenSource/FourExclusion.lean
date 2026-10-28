module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Four
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Placement
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Inverter
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.ResidualImage
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.FourExclusion.Parity

/-!
# Original rank-four exclusion in 14.7.50

The faithful four-dimensional quotient makes the whole local quotient A₇.
The original seed remains a plane. Its stabilizer is the literal even
four-plus-three partition stabilizer after an actual seven-letter conjugation;
solvability and 14.7.29 identify its preimage with the original intersection
with N_G(L). The original point inverter fixes the centralizer-residual
supplement, contradicting the common scalar action on the order-nine quotient.

Source: Aschbacher–Smith 14.7.50, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source WholeResidualAssembly
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.ComponentSieve.Seven
open FourThreeBranch.NaturalSelection FourExclusion
universe u v w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original partial inverter excludes an even four-plus-three local
intersection, through its literal two-kernel. -/
theorem local_even_fourThree_impossible_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (f : I →* Equiv.Perm (Fin 7)) (hk : IsPGroup 2 f.ker)
    (hmark : ((I ⊓ normalizer (L : Set G)).subgroupOf I).map f = Model.P) : False := by
  let J := I ⊓ normalizer (L : Set G)
  let B := (pResidual 2 J).map J.subtype
  let hBM : B ≤ normalizer (L : Set G) := (map_subtype_le _).trans inf_le_right
  let D := binaryBorelCentralResidual L B hBM
  obtain ⟨hgen,hAcard,hJA,t,htJ,htB,htD,hinv,hfix⟩ := local_partial_inverter_at h structural I hI
  obtain ⟨him,hcard,hcube⟩ := local_residual_quotient_of_even_partition I J inf_le_left f hk hmark
  have hBI : B ≤ I := (map_subtype_le _).trans inf_le_left
  let fB := f.comp (inclusion hBI)
  have hkB : IsPGroup 2 fB.ker := hk.comap_of_injective _ (inclusion_injective hBI)
  have hfB : fB.range ≤ fourThreeTheta := by
    rw [MonoidHom.range_comp,inclusion_range,him,Model.residual_eq_theta]
  let tI : I := ⟨t,htJ.1⟩
  have htP : f tI ∈ Model.P := hmark ▸
    mem_map_of_mem f (show tI ∈ J.subgroupOf I from htJ)
  apply no_even_partial_inverter B (F.Li L 1) D hgen hcard hcube hAcard
    ⟨t,htB⟩ (hJA htJ) htD hinv hfix fB hkB hfB (f tI) htP.1
    (Equiv.Perm.mem_alternatingGroup.mp htP.2)
  intro x
  change f (inclusion hBI (B.normalizerMonoidHom ⟨t,htB⟩ x)) =
    f tI * f (inclusion hBI x) * (f tI)⁻¹
  have he : inclusion hBI (B.normalizerMonoidHom ⟨t,htB⟩ x) =
      tI * inclusion hBI x * tI⁻¹ := Subtype.ext rfl
  rw [he,map_mul,map_mul,map_inv]

private def fourSection {I : Subgroup G} [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    BinaryConjugationSection I (F.UH I) (F.Vi 1)
      (a.representation.comp (QuotientGroup.mk' (pCore 2 I))) where
  section_le := a.le_local
  kernel_le := a.kernel_le
  normalized := a.normalizes
  coordinates := {
    toFun z := Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' ((F.Vi 1).subgroupOf (F.UH I)) z))
    map_one' := (QuotientGroup.mk' _).map_one
    map_mul' := (QuotientGroup.mk' _).map_mul }
  onto := QuotientGroup.mk'_surjective _
  kernel_eq := QuotientGroup.ker_mk' _
  equivariant i z := (a.conjugation i z).symm

/-- The rank-four case in 14.7.50 is impossible for each actual proper
quotient of the original local span. All marking and inverter data are
constructed from the original source hypotheses. -/
theorem local_four_quotient_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1))
    (N : Subrepresentation a.representation) (hN : N ≠ ⊤)
    (hd : Module.finrank (ZMod 2)
      (Additive ((F.UH I) ⧸ (F.Vi 1).subgroupOf (F.UH I)) ⧸ N.toSubmodule) = 4) : False := by
  obtain ⟨b,_⟩ := local_four_quotient_alternating_marking_at
    d h hab structural previous faithful earlier source47 I hI C hC e a N hN hd
  let q := QuotientGroup.mk' (pCore 2 I)
  let π := b.toMonoidHom.comp q
  let τ := N.quotientRepresentation.comp b.symm.toMonoidHom
  let c := fourSection a
  let p : Representation.IntertwiningMap (a.representation.comp q) (τ.comp π) := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' := by
      intro i
      apply LinearMap.ext
      intro z
      change N.toSubmodule.mkQ (a.representation (q i) z) =
        N.quotientRepresentation (b.symm (b (q i))) (N.toSubmodule.mkQ z)
      rw [b.symm_apply_apply]
      rfl }
  have hp : p.toLinearMap.ker ≠ ⊤ := by
    intro he
    apply hN
    apply Subrepresentation.toSubmodule_injective
    exact (Submodule.ker_mkQ N.toSubmodule).symm.trans he
  have hπ : IsPGroup 2 π.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hτ : Function.Injective τ := (local_proper_quotient_faithful_at
    d h hab structural previous faithful earlier source47 I hI C hC a N hN).comp b.symm.injective
  let E := (c.imageSpace V).map p.toLinearMap
  have hE : Module.finrank (ZMod 2) E = 2 := local_quotient_seed_finrank h hI c p hp
  obtain ⟨s,_hs,hplace⟩ := four_plane_partition_placement τ hτ hd E hE
  have hstab := local_four_seed_stabilizer_eq d h hab structural previous faithful earlier
    hI c τ π hπ p hp hτ hd
  let f₀ := (MulAut.conj s).toMonoidHom.comp (alternatingGroup (Fin 7)).subtype
  let f := f₀.comp π
  have hf₀ : Function.Injective f₀ := (MulAut.conj s).injective.comp Subtype.val_injective
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ hf₀]
    exact hπ
  have hfrange : f.range = alternatingGroup (Fin 7) := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (b.surjective.comp (QuotientGroup.mk'_surjective _)),←MonoidHom.range_eq_map]
    rw [MonoidHom.range_comp,range_subtype]
    exact normal_iff_map_conj_eq.mp (inferInstance : (alternatingGroup (Fin 7)).Normal) s
  let J := I ⊓ normalizer (L : Set G)
  have hJN : J.subgroupOf I = (normalizer (V : Set G)).subgroupOf I := by
    have hne : F.Vi 1 ≠ ⊥ := by
      intro hz
      have hh := F.card 1 (by decide)
      simp [hz] at hh
    have hnormal := structural.intersection_normalizer h.source h.chosen
      hne (F.le_seed 1) (le_rfl : F.H ≤ normalizer (F.Vi 1 : Set G))
    ext x
    constructor
    · intro hx
      have hx' : x.val ∈ F.H ⊓ normalizer (L : Set G) := ⟨hI.2.1 x.property,hx.2⟩
      rw [hnormal] at hx'
      exact hx'.2
    · intro hx
      exact ⟨x.property,h.seed_normalizer_le_at structural hx⟩
  have hpre : J.subgroupOf I = fourThreeStabilizer.comap f := by
    rw [hJN,←hstab,hplace]
    rfl
  have hmark : (J.subgroupOf I).map f = Model.P := by
    rw [hpre,Subgroup.map_comap_eq,hfrange]
    exact inf_comm _ _
  exact local_even_fourThree_impossible_at h structural I hI f hk hmark

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
