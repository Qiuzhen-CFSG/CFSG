module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalParametersModel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityOuterInvolution
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import GorensteinWalter.SL2ProjectiveCover
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityLocalParametersModel
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityWeylAction

/-!
# The genuine cubic coefficient of an original triality outer involution

The same right-parabolic comparison transports conjugation by the original
marked torus involution to an automorphism preserving both torus and positive
subgroup. The signed-root calculation recovers its cubic field coefficient
and reciprocal root scalars.

The coefficient is nontrivial. Indeed, if it were trivial, involutivity in
characteristic two would make the root scalar one. The actor would then fix
the whole root SL₂. Perfectness puts this SL₂ in O²(H), its two-core kernel
is trivial, and the actual right quotient marking makes its image surjective
onto O²(H)/O₂(O²(H)). The proved kernel of the original Sylow quotient action
would put the actor in S, a contradiction.

Thus the coefficient has order two, with no local-action or native-extension
premise. The Chapter 12 companion applies this to the literal chosen module.
The common coefficient on the central root, the whole positive-subgroup
identity, ambient Sylow placement, S=T and final recognition remain unproved.

Source: Aschbacher--Smith F.4.29, F.4.37--38, printed pp.289,293--294,
and 5.3.3, p.659 (`refs/quasithin.pdf`). Internal imports reuse the local
rank-one map and whole-overlap marking transports within this source family.
-/

public noncomputable section
open Subgroup Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.ElementaryCentralKernel
open Triality.Standard.OuterOdd.Coverage.ParameterRigidity
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.GroupTheory TrialityLocalParameters
variable {G : Type*} [Group G] [Finite G]

private theorem Preparation.triality_rankOne_quotient_surjective
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    ∃ j : SL(2,ExtensionField (binaryParameters m hm)) →* residual H,
      (∀ g, (j g).val=(e.right.symm (rankOneLocal (binaryParameters m hm) rfl .arms g)).val) ∧
      Function.Surjective ((QuotientGroup.mk' (pCore 2 (residual H))).comp j) := by
  let P := binaryParameters m hm
  let F := ExtensionField P
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hF : 3<Nat.card F := by
    rw [show Nat.card F=P.q^3 from card_extensionField P]
    have hq := Nat.pow_le_pow_left P.q_ge_two 3
    norm_num at hq
    omega
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hF
  let g : SL(2,F) →* Y := e.right.symm.toMonoidHom.comp (rankOneLocal P rfl .arms)
  let : Group.IsPerfect g.range := Group.IsPerfect.ofSurjective (MonoidHom.rangeRestrict_surjective g)
  have hg : ∀ x, (g x).val∈residual H := by
    intro x
    have hres : (solvableResidual Y).map Y.subtype=residual H := d.parabolic_residuals h hTH hp 1
    rw [←hres]
    exact mem_map_of_mem Y.subtype ((le_solvableResidual_of_isPerfect g.range) ⟨x,rfl⟩)
  let j : SL(2,F) →* residual H := (Y.subtype.comp g).codRestrict _ hg
  have hj : Function.Injective j := by
    intro x y hxy
    apply rankOne_injective P rfl .arms
    have he : (e.right.symm (rankOneLocal P rfl .arms x)).val=
        (e.right.symm (rankOneLocal P rfl .arms y)).val := congrArg (fun z : residual H => z.val) hxy
    have hh := e.right.symm.injective (Subtype.ext he)
    exact congrArg Subtype.val hh
  let q := QuotientGroup.mk' (pCore 2 (residual H))
  have hi : Function.Injective (q.comp j) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    apply le_bot_iff.mp
    calc
      _ ≤ pCore 2 SL(2,F) := le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective j hj⟩
      _ = ⊥ := Atlas.RankOneFieldAutomorphisms.sl_twoCore_eq_bot
  obtain ⟨l⟩ := (d.triality_local_structure h hTH hp m hm e).2.2.2.1
  let eQ : (residual H ⧸ pCore 2 (residual H)) ≃* SL(2,F) :=
    ((QuotientGroup.congr _ _ l (pCore_map_iso 2 l)).trans
      (localFactorArmsQuotientEquivPSL2 P rfl)).trans (Theory.PSL2.sl2QuotientEquiv F).symm
  have hs := Finite.surjective_of_injective (eQ.injective.comp hi)
  refine ⟨j,fun _ => rfl,?_⟩
  intro x
  obtain ⟨y,hy⟩ := hs (eQ x)
  exact ⟨y,eQ.injective hy⟩

/-- The literal right-parabolic marking gives scalar-semilinear formulas on
both cubic simple roots. An outer torus involution has coefficient of order two. -/
theorem Preparation.triality_outer_signed_root_action
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0<m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)
    (hD : D ≤ ChapterF.Source.commonBorel ![L,residual H] (sourceS L H))
    (hmark : ∀ b : (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 : Subgroup G),
        b.val∈D ↔ (e.middle b).val∈torus (binaryParameters m hm))
    (t : T) (ht2 : orderOf t=2) (htS : t.val∉sourceS L H)
    (htD : t.val∈normalizer (D : Set G)) :
    ∃ (c : (ExtensionField (binaryParameters m hm))ˣ)
      (σ : ExtensionField (binaryParameters m hm) ≃+* ExtensionField (binaryParameters m hm)),
      orderOf σ=2 ∧ c.val*σ c.val=1 ∧
      ∀ s r, t.val*(e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms r)).val*t.val⁻¹=
        (e.right.symm (rootInParabolic (binaryParameters m hm) rfl s .arms (signedScalar s c.val*σ r))).val := by
  let P := binaryParameters m hm
  let Y := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let f : parabolic P .arms →* G := Y.subtype.comp e.right.symm.toMonoidHom
  have hf : Function.Injective f := Y.subtype_injective.comp e.right.symm.injective
  have hS := d.triality_right_unipotent_image h hTH P rfl e
  have htY := source_parabolics_normalized h.sylow_normalizes hTH 1 t.property
  let b := MulAut.congr e.right (Y.normalizerMonoidHom ⟨t.val,htY⟩)
  have hb (x : parabolic P .arms) : f (b x)=t.val*f x*t.val⁻¹ := by
    change (e.right.symm (e.right (Y.normalizerMonoidHom ⟨t.val,htY⟩ (e.right.symm x)))).val=_
    rw [e.right.symm_apply_apply]
    rfl
  have hU : ((unipotent P).subgroupOf (parabolic P .arms)).map b.toMonoidHom=
      (unipotent P).subgroupOf (parabolic P .arms) := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      have hxS : f x∈sourceS L H := hS ▸ mem_map_of_mem f hx
      have hyS : f (b x)∈sourceS L H := by
        rw [hb]
        exact (mem_normalizer_iff.mp (sylow_normalizes_sourceS h.sylow_normalizes hTH t.property) _).mp hxS
      rw [←hS,mem_map_iff_mem hf] at hyS
      exact hyS
    · rw [card_map_of_injective b.injective]
  have hC := (ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hTH)).ge
  have hmr := (source_triality_torus_markings m hm e (hD.trans hC) hmark).2
  have hbD := torus_action_map (M := Carrier P) Y (parabolic P .arms)
    (torus P) e.right D t.val htY htD hmr
  have ht : t.val*t.val=1 := by
    have hh : t.val^2=1 := congrArg Subtype.val ((orderOf_eq_prime_iff.mp ht2).1)
    exact (pow_two t.val).symm.trans hh
  have hinv : Function.Involutive b := by
    intro x
    apply hf
    rw [hb,hb]
    calc
      t.val*(t.val*f x*t.val⁻¹)*t.val⁻¹ = (t.val*t.val)*f x*(t.val*t.val)⁻¹ := by group
      _ = f x := by rw [ht]; simp
  obtain ⟨c,σ,hσ,hc,ha⟩ := arms_involution_field_action m hm
    (d.triality_local_structure h hTH hp m hm e).2.1 b hbD hU hinv
  have hne : σ≠1 := by
    intro hσ1
    have hc1 : c.val=1 := by
      have hh : c.val^2=1 := by simpa only [hσ1,RingAut.one_apply,←pow_two] using hc
      exact (sq_eq_sq_iff_eq_or_eq_neg.mp (hh.trans (one_pow 2).symm)).elim id
        (fun h => h.trans (CharTwo.neg_eq 1))
    have hroots (s r) : b (rootInParabolic P rfl s .arms r)=rootInParabolic P rfl s .arms r := by
      simpa only [hσ1,RingAut.one_apply,hc1,signedScalar,inv_one,ite_self,one_mul] using ha s r
    have hfixed (x : SL(2,ExtensionField P)) : b (rankOneLocal P rfl .arms x)=rankOneLocal P rfl .arms x := by
      apply sl2_root_induction (fun x => b (rankOneLocal P rfl .arms x)=rankOneLocal P rfl .arms x) ?_ ?_ ?_ x
      · intro r
        change b (rankOneLocal P rfl .arms (signed true r))=rankOneLocal P rfl .arms (signed true r)
        rw [rankOneLocal_signed P rfl true .arms r]
        exact hroots true r
      · intro r
        change b (rankOneLocal P rfl .arms (signed false r))=rankOneLocal P rfl .arms (signed false r)
        rw [rankOneLocal_signed P rfl false .arms r]
        exact hroots false r
      · intro x y hx hy
        rw [map_mul,map_mul,hx,hy]
    obtain ⟨j,hj,hq⟩ := d.triality_rankOne_quotient_surjective h hTH hp m hm e
    have hja (x) : (residual H).normalizerMonoidHom
        ⟨t.val,hTH.trans (le_normalizer_residual H) t.property⟩ (j x)=j x := by
      apply Subtype.ext
      change t.val*(j x).val*t.val⁻¹=(j x).val
      rw [hj]
      exact (hb _).symm.trans (congrArg f (hfixed x))
    have hqa : pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H))
        (inclusion le_sup_right t)=1 := by
      ext x
      obtain ⟨y,rfl⟩ := hq x
      change pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H))
        (inclusion le_sup_right t) (QuotientGroup.mk' (pCore 2 (residual H)) (j y))=_
      rw [pCoreJoinAction_mk]
      exact congrArg (QuotientGroup.mk' (pCore 2 (residual H))) (hja y)
    obtain ⟨l⟩ := (d.triality_local_structure h hTH hp m hm e).2.2.2.1
    let eR := (QuotientGroup.congr _ _ l (pCore_map_iso 2 l)).trans
      (localFactorArmsQuotientEquivPSL2 P rfl)
    have hk : t∈(residualSylowFieldAction hTH eR).ker := by
      change Theory.PSL2.fieldProjection (ExtensionField P) (MulAut.congr eR
        (pCoreJoinAction 2 (hTH.trans (le_normalizer_residual H)) (inclusion le_sup_right t)))=1
      rw [hqa,map_one,map_one]
    rw [d.residual_sylow_field_kernel h hTH
      (d.triality_sourceS_le_factors h hTH hp m hm (Or.inr ⟨e⟩)) eR] at hk
    exact htS hk
  refine ⟨c,σ,orderOf_eq_prime hσ hne,hc,?_⟩
  intro s r
  exact (hb _).symm.trans (congrArg f (ha s r))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
