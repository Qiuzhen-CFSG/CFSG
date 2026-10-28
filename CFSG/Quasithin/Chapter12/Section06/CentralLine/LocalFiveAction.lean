module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalSource
public import Theory.SpecificGroups.Alternating.FiveExtensionAction
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
public import Theory.GroupTheory.PResidual.FiniteImage
public import CFSG.Quasithin.Chapter6.SourceDefs
public import Theory.SpecificGroups.Alternating.FiveResidualPlacement
public import Theory.SpecificGroups.Alternating.FiveComponentExtension
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# The original five-point action and Borel placement for 12.6.23

The literal quotient J/C_J(V_H) has trivial two-core by reducedness. A
marking of K/O₂(K), for the embedded K=O²(J), identifies its actual residual
image with A₅: the kernel cannot contain K, since K moves the original
Sylow-center seed. Its self-centralizing residual gives a faithful S₅ action
extending that same marking. From either source one- or two-copy A₅ model,
we embed a five-point core in the unchanged V_H. Every even quotient actor
lifts to K under this marking, so the same embedding is equivariant for it.

The H-star intersection B=J intersect M is a point-stabilizer preimage in
an auxiliary action of J/O₂(J). The image has only primes two and three;
comparison through the two-group kernel gives O²(B)=O^{3′}(B). Since the
original O^{3′}(M) is L, this proves B≤LT. Thus the selected conjugate of V
lies in O₂(B), whose image is even. The existing local contradiction now
applies with every quotient, summand, evenness and placement input supplied.
The auxiliary two-core quotient is used only for Borel placement: the module
action remains J/C_J(V_H), and no equality of these kernels is assumed.

This proves the local contradiction from the genuine one-or-two A₅ source
alternative. Its production from earlier 12.2.2/12.3.1 and rank-one source
inputs is connected in FixedSpaceSource; those earlier inputs retain their
existing owners. Source: Aschbacher–Smith, 12.6.23, printed pp.829–830,
using 12.3.2, p.807, and the original 12.6.1(5) residual calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine.LocalContradiction
namespace LocalFiveAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V J : Subgroup G}

/-- Reducedness is on the literal quotient by C_J(V_H). -/
theorem localQuotient_core_eq_bot
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    pCore 2 (LocalQuotient T J) = ⊥ := by
  have hr : IsPReduced 2 ((localSpan T J).subgroupOf J) :=
    Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_reduced H.source hJ
  let : ((localSpan T J).subgroupOf J).Normal := hr.normal
  have hk : (localConjugation T J).ker =
      centralizer ((localSpan T J).subgroupOf J : Set J) := by
    rw [localConjugation_ker]
    ext x
    constructor
    · intro hx y hy
      exact Subtype.ext (hx y hy)
    · intro hx y hy
      exact congrArg J.subtype (hx ⟨y,localSpan_le hJ.1.1.2 hy⟩ hy)
  let c := QuotientGroup.quotientMulEquivOfEq hk
  rw [←pCore_map_iso 2 c.symm,hr.quotient_pCore_eq_bot,Subgroup.map_bot]

/-- The marked residual quotient is the actual two-residual in the local
centralizer quotient, with its original quotient projection. -/
theorem exists_residual_marking
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hZ : centralizer (Z T : Set G) ≤ M L)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (e : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5)) :
    ∃ d : pResidual 2 (LocalQuotient T J) ≃* alternatingGroup (Fin 5),
      ∀ k : localResidual J,
        ∃ hk : localActorMap (T := T) (map_subtype_le (pResidual 2 J)) k ∈
            pResidual 2 (LocalQuotient T J),
          d ⟨localActorMap (T := T) (map_subtype_le (pResidual 2 J)) k,hk⟩ =
            e (QuotientGroup.mk' (pCore 2 (localResidual J)) k) := by
  let q := QuotientGroup.mk' (localConjugation T J).ker
  let R := localResidual J
  have hRJ : R ≤ J := map_subtype_le _
  let f : R →* LocalQuotient T J := localActorMap (T := T) hRJ
  have hkill : pCore 2 R ≤ f.ker := by
    intro k hk
    change q (inclusion hRJ k) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [localConjugation_ker]
    exact Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_core_centralizes H.source hJ
      (pCoreIn_mono_of_normalizes hRJ (Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual_normalized J)
        (mem_map_of_mem R.subtype hk))
  let b : (R ⧸ pCore 2 R) →* LocalQuotient T J := QuotientGroup.lift _ f hkill
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := e.isSimpleGroup
  have hbi : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff b).mp
    rcases (inferInstance : b.ker.Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exfalso
      apply Section04.SLThreeCommutatorSource.ConjugateExistence.localResidual_not_centralizes_seed
        H.chosen.sylow_normalizes_component hZ hJ
      intro k hk z hz
      have hb : b (QuotientGroup.mk' (pCore 2 R) ⟨k,hk⟩) = 1 := by
        exact show _ ∈ b.ker from he ▸ mem_top _
      have hf : f ⟨k,hk⟩ = 1 := hb
      have hc : k ∈ centralizer (localSpan T J : Set G) := by
        have hh : (inclusion hRJ ⟨k,hk⟩) ∈ (localConjugation T J).ker :=
          (QuotientGroup.eq_one_iff _).mp hf
        rwa [localConjugation_ker] at hh
      exact hc z (le_conjugateSpanBy _ _ hz)
  have hR : R.subgroupOf J = pResidual 2 J :=
    comap_map_eq_self_of_injective J.subtype_injective _
  have hfR : f.range = pResidual 2 (LocalQuotient T J) := by
    change (q.comp (inclusion hRJ)).range = _
    rw [MonoidHom.range_comp,inclusion_range,hR,map_pResidual_of_surjective 2 q
      (QuotientGroup.mk'_surjective _)]
  have hbR : b.range = pResidual 2 (LocalQuotient T J) := by
    rw [←hfR]
    apply le_antisymm
    · rintro y ⟨x,rfl⟩
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 R) x
      exact ⟨k,rfl⟩
    · rintro y ⟨k,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 R) k,rfl⟩
  let d := (MulEquiv.subgroupCongr hbR.symm).trans ((MonoidHom.ofInjective hbi).symm.trans e)
  refine ⟨d,fun k => ⟨hfR ▸ show f k ∈ f.range from ⟨k,rfl⟩,?_⟩⟩
  change e ((MonoidHom.ofInjective hbi).symm _) = e (QuotientGroup.mk' (pCore 2 R) k)
  congr 1
  apply (MonoidHom.ofInjective hbi).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The full original action quotient embeds on five letters. This marking
extends the given K/O₂(K) marking on each literal quotient image. -/
theorem exists_local_five_action
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hZ : centralizer (Z T : Set G) ≤ M L)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (e : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5)) :
    ∃ α : LocalQuotient T J →* Equiv.Perm (Fin 5), Function.Injective α ∧
      ∀ k : localResidual J,
        α (localActorMap (T := T) (map_subtype_le (pResidual 2 J)) k) =
          (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)).val := by
  obtain ⟨d,hd⟩ := exists_residual_marking H hZ hJ e
  let R := pResidual 2 (LocalQuotient T J)
  have hc : centralizer (R : Set (LocalQuotient T J)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hr : x ∈ R := centralizer_pResidual_le_of_pCore_eq_bot
      (localQuotient_core_eq_bot H hJ) hx
    have hz : (⟨x,hr⟩ : R) ∈ center R :=
      mem_center_iff.mpr (fun r => Subtype.ext (hx r r.property))
    have hh := MulEquivClass.apply_mem_center d hz
    change d ⟨x,hr⟩ ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 5)),mem_bot] at hh
    exact congrArg Subtype.val (d.injective (hh.trans d.map_one.symm))
  let α := Theory.SpecificGroups.Alternating.FiveExtensionAction.action R d
  refine ⟨α,Theory.SpecificGroups.Alternating.FiveExtensionAction.action_injective R d hc,?_⟩
  intro k
  obtain ⟨hk,hk'⟩ := hd k
  exact (Theory.SpecificGroups.Alternating.FiveExtensionAction.action_on_subgroup R d
    ⟨localActorMap (T := T) (map_subtype_le (pResidual 2 J)) k,hk⟩).trans
      (congrArg Subtype.val hk')

omit [Finite G] in
private theorem summand_from_conjugation_model
    [IsElementaryAbelian 2 (localSpan T J)]
    {W : Subgroup G} (hWU : W ≤ localSpan T J)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) X)
    (e : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5))
    (b : W ≃* Multiplicative X)
    (hb : ∀ (k : localResidual J) (w : W),
      ((b.symm (Multiplicative.ofAdd (ρ
        (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)) (b w).toAdd))) : G) =
          (k : G) * (w : G) * (k : G)⁻¹)
    (i : core (Fin 5) →ₗ[ZMod 2] X) (hi : Function.Injective i)
    (he : ∀ a v, i (coreRepresentation (Fin 5) (a : alternatingGroup (Fin 5)).val v) =
      ρ a (i v)) :
    ∃ j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T J), Function.Injective j ∧
      ∀ (k : localResidual J) v,
        j (coreRepresentation (Fin 5)
          (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)).val v) =
        seedRepresentation (localResidual J) (localSpan T J)
          ((map_subtype_le _).trans (normalizes_localSpan T J)) k (j v) := by
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWU
  let E : Additive W ≃ₗ[ZMod 2] X :=
    LinearEquiv.ofBijective (b.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) b.bijective
  let inc : Additive W →ₗ[ZMod 2] Additive (localSpan T J) :=
    (inclusion hWU).toAdditive.toZModLinearMap 2
  let j := inc.comp (E.symm.toLinearMap.comp i)
  refine ⟨j,(inclusion_injective hWU).comp (E.symm.injective.comp hi),?_⟩
  intro k v
  apply Additive.toMul.injective
  apply Subtype.ext
  have heinv (x : X) : (E.symm x).toMul = b.symm (Multiplicative.ofAdd x) := by
    apply b.injective
    rw [b.apply_symm_apply]
    exact E.apply_symm_apply x
  change ((E.symm (i (coreRepresentation (Fin 5)
      (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)).val v))).toMul : G) =
    (k : G) * ((E.symm (i v)).toMul : G) * (k : G)⁻¹
  rw [heinv,heinv]
  rw [he]
  simpa only [b.apply_symm_apply,toAdd_ofAdd] using
    hb k (b.symm (Multiplicative.ofAdd (i v)))

omit [Finite G] in
/-- The one- and two-copy source alternatives both contain an actual
five-point core, with the same residual quotient marking. -/
theorem exists_residual_summand
    [IsElementaryAbelian 2 (localSpan T J)]
    (hm : Chapter6.Source.IsOneOrTwoA5Modules (localResidual J)
      ⁅localSpan T J,localResidual J⁆) :
    ∃ e : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5),
      ∃ j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T J), Function.Injective j ∧
        ∀ (k : localResidual J) v,
          j (coreRepresentation (Fin 5)
            (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)).val v) =
          seedRepresentation (localResidual J) (localSpan T J)
            ((map_subtype_le _).trans (normalizes_localSpan T J)) k (j v) := by
  have hWU : ⁅localSpan T J,localResidual J⁆ ≤ localSpan T J :=
    le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le _).trans (normalizes_localSpan T J))
  let E := coreEquivNatural (Fin 5) (by decide)
  rcases hm with ⟨e,b,hb⟩ | ⟨e,b,hb⟩
  · refine ⟨e,?_⟩
    exact summand_from_conjugation_model hWU _ e b hb E.toLinearMap E.injective
      (fun a v => coreEquivNatural_equivariant (Fin 5) (by decide) a.val v)
  · let i : core (Fin 5) →ₗ[ZMod 2] (natural (Fin 5) × natural (Fin 5)) :=
      E.toLinearMap.prod 0
    have hi : Function.Injective i := by
      intro x y he
      exact E.injective (congrArg Prod.fst he)
    refine ⟨e,summand_from_conjugation_model hWU _ e b hb i hi ?_⟩
    intro a v
    apply Prod.ext
    · exact coreEquivNatural_equivariant (Fin 5) (by decide) a.val v
    · change (0 : natural (Fin 5)) = Chapter6.Source.a5Module a 0
      exact (map_zero _).symm

/-- The residual summand is equivariant for every even actor in the actual
local quotient. Injectivity and the retained marking lift that actor to K. -/
theorem exists_local_five_summand
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hZ : centralizer (Z T : Set G) ≤ M L)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    [IsElementaryAbelian 2 (localSpan T J)]
    (hm : Chapter6.Source.IsOneOrTwoA5Modules (localResidual J)
      ⁅localSpan T J,localResidual J⁆) :
    ∃ α : LocalQuotient T J →* Equiv.Perm (Fin 5), Function.Injective α ∧
      (∀ k : localResidual J, α (localActorMap (T := T)
        (map_subtype_le (pResidual 2 J)) k) ∈ alternatingGroup (Fin 5)) ∧
      ∃ j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T J), Function.Injective j ∧
        ∀ (a : J) v,
          α (QuotientGroup.mk' (localConjugation T J).ker a) ∈ alternatingGroup (Fin 5) →
          j (coreRepresentation (Fin 5)
            (α (QuotientGroup.mk' (localConjugation T J).ker a)) v) =
          seedRepresentation J (localSpan T J) (normalizes_localSpan T J) a (j v) := by
  obtain ⟨e,j,hj,he⟩ := exists_residual_summand hm
  obtain ⟨α,hα,hmark⟩ := exists_local_five_action H hZ hJ e
  refine ⟨α,hα,(fun k => (hmark k) ▸ (e (QuotientGroup.mk' _ k)).property),j,hj,?_⟩
  intro a v ha
  obtain ⟨k,hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ⟨α (QuotientGroup.mk' (localConjugation T J).ker a),ha⟩
  have hq : localActorMap (T := T) (map_subtype_le (pResidual 2 J)) k =
      QuotientGroup.mk' (localConjugation T J).ker a :=
    hα ((hmark k).trans (congrArg Subtype.val hk))
  have hc := congrArg (QuotientGroup.kerLift (localConjugation T J)) hq
  change localConjugation T J (inclusion (map_subtype_le (pResidual 2 J)) k) =
    localConjugation T J a at hc
  have hk' : (e (QuotientGroup.mk' (pCore 2 (localResidual J)) k)).val =
      α (QuotientGroup.mk' (localConjugation T J).ker a) := congrArg Subtype.val hk
  rw [←hk',he]
  apply Additive.toMul.injective
  exact congrArg (fun f : MulAut (localSpan T J) => f (j v).toMul) hc


/-- The genuine H-star Borel two-core acts through the original residual,
modulo O₂(J). The only identification is K/O₂(K)=A₅. -/
theorem local_borel_core_le_residual_join_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (e : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5)) :
    (J ⊓ M L).pCoreIn 2 ≤ localResidual J ⊔ J.pCoreIn 2 := by
  let B := J ⊓ M L
  have hTB : (T : Subgroup G) ≤ B := le_inf hJ.1.1.2 H.chosen.sylow_normalizes_component
  have hp : ∀ Y : Subgroup J, (T.subtype hJ.1.1.2 : Subgroup J) ≤ Y →
      Y ≠ ⊤ → Y ≤ B.subgroupOf J := by
    intro Y hSY hne
    have hTY : (T : Subgroup G) ≤ Y.map J.subtype := by
      have hh := map_mono (f := J.subtype) hSY
      change ((T : Subgroup G).subgroupOf J).map J.subtype ≤ _ at hh
      rwa [map_subgroupOf_eq_of_le hJ.1.1.2] at hh
    have hYJ : Y.map J.subtype < J := by
      have hh := (map_lt_map_iff_of_injective J.subtype_injective).mpr
        (lt_top_iff_ne_top.mpr hne)
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    exact map_le_iff_le_comap.mp
      (le_inf (map_subtype_le _) (Chapter3.HStar.proper_overgroup_le T hJ hTY hYJ))
  let c := (pResidual 2 J).equivMapOfInjective J.subtype J.subtype_injective
  let d := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e
  have hc := Theory.SpecificGroups.Alternating.FiveResidualPlacement.core_le_residual_join_core
    (T.subtype hJ.1.1.2) (B.subgroupOf J) (comap_mono hTB) hp d
  have hm := map_mono (f := J.subtype) hc
  rw [Theory.SpecificGroups.Alternating.FiveBorelCentralFactor.core_subgroupOf_map
    (show B ≤ J from inf_le_left),Subgroup.map_sup] at hm
  exact hm

/-- Every local actor in K O₂(J) is even for the same faithful five-point
marking. This uses the actual kernel quotient and its residual inclusion. -/
theorem local_even_of_le_residual_join_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (α : LocalQuotient T J →* Equiv.Perm (Fin 5))
    (hmark : ∀ k : localResidual J, α (localActorMap (T := T)
      (map_subtype_le (pResidual 2 J)) k) ∈ alternatingGroup (Fin 5))
    {A : Subgroup G} (hAJ : A ≤ J) (hA : A ≤ localResidual J ⊔ J.pCoreIn 2)
    (a : A) : α (localActorMap (T := T) hAJ a) ∈ alternatingGroup (Fin 5) := by
  let f := α.comp (QuotientGroup.mk' (localConjugation T J).ker)
  let P := ((alternatingGroup (Fin 5)).comap f).map J.subtype
  have hr : localResidual J ≤ P := by
    intro k hk
    exact ⟨inclusion (map_subtype_le (pResidual 2 J)) ⟨k,hk⟩,hmark ⟨k,hk⟩,rfl⟩
  have hc : J.pCoreIn 2 ≤ P := by
    intro k hk
    have hkc := Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_core_centralizes
      H.source hJ hk
    have hh : (⟨k,pCoreIn_le 2 J hk⟩ : J) ∈ (localConjugation T J).ker := by
      rw [localConjugation_ker]
      exact hkc
    refine ⟨⟨k,pCoreIn_le 2 J hk⟩,?_,rfl⟩
    change α (QuotientGroup.mk' (localConjugation T J).ker _) ∈ alternatingGroup (Fin 5)
    have hq : QuotientGroup.mk' (localConjugation T J).ker ⟨k,pCoreIn_le 2 J hk⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hh
    rw [hq,map_one]
    exact one_mem _
  obtain ⟨x,hx,he⟩ := (hA.trans (sup_le hr hc)) a.property
  have he' : x = inclusion hAJ a := Subtype.ext he
  subst x
  exact hx

end LocalFiveAction

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V J : Subgroup G}

/-- The original 12.6.23 contradiction with both five-point markings
constructed from the source one-or-two A₅ modules. The literal Borel
placement is the sole remaining local group-placement premise. -/
theorem SourceHypothesis.fixed_hstar_one_or_two_contradiction
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (hJM : J ⊓ M L ≤ LT T L)
    (hm : Chapter6.Source.IsOneOrTwoA5Modules (localResidual J)
      ⁅localSpan T J,localResidual J⁆) : False := by
  let := H.local_span_elementary hJ
  obtain ⟨α,hα,hmark,j,hj,he⟩ := LocalFiveAction.exists_local_five_summand H
    (H.fixed_sylow_seed_centralizer_le D hTV hz) hJ hm
  have heK : Nonempty ((localResidual J ⧸ pCore 2 (localResidual J)) ≃*
      alternatingGroup (Fin 5)) := by
    rcases hm with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
  obtain ⟨e⟩ := heK
  obtain ⟨g,hAT,hAB,hne⟩ := H.fixed_local_actor_exists D hTV hTI hz hJ hJM
  have hAJ := hAT.trans hJ.1.1.2
  have hAK := hAB.trans (LocalFiveAction.local_borel_core_le_residual_join_core H hJ e)
  have heven := LocalFiveAction.local_even_of_le_residual_join_core H hJ α hmark hAJ hAK
  apply H.fixed_marked_local_actor_contradiction D hTV hTI hz hAJ hne α hα heven j hj
  intro a v
  exact he (inclusion hAJ a) v (heven a)

/-- The source Borel has only primes two and three in its five-point core
quotient. Its two-residual is therefore the prime-to-three residual and
lies in the original L. This supplies the literal Borel placement. -/
theorem SourceHypothesis.fixed_hstar_borel_le_join
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (e : (localResidual J ⧸ pCore 2 (localResidual J)) ≃* alternatingGroup (Fin 5)) :
    J ⊓ M L ≤ LT T L := by
  let B := J ⊓ M L
  let S := T.subtype hJ.1.1.2
  let cR := (pResidual 2 J).equivMapOfInjective J.subtype J.subtype_injective
  let eR := (QuotientGroup.congr _ _ cR (pCore_map_iso 2 cR)).trans e
  obtain ⟨f,hfk,hA⟩ : ∃ f : J →* Equiv.Perm (Fin 5),
      f.ker = pCore 2 J ∧ alternatingGroup (Fin 5) ≤ f.range := by
    have he := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
      (pResidual 2 J) (S : Subgroup J) le_normalizer_of_normal S.isPGroup' eR
    rw [pResidual_sup_sylow_eq_top S] at he
    let c := QuotientGroup.congr _ _ (topEquiv : (⊤ : Subgroup J) ≃* J)
      (pCore_map_iso 2 topEquiv)
    let q := QuotientGroup.mk' (pCore 2 J)
    rcases he with ha | ha
    · obtain ⟨a⟩ := ha
      let d := c.symm.trans a
      let f := (alternatingGroup (Fin 5)).subtype.comp (d.toMonoidHom.comp q)
      have hsurj := d.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 J))
      refine ⟨f,?_,?_⟩
      · rw [MonoidHom.ker_comp_of_injective _ _ Subtype.val_injective,
          MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
      · intro x hx
        obtain ⟨j,hj⟩ := hsurj ⟨x,hx⟩
        exact ⟨j,congrArg Subtype.val hj⟩
    · obtain ⟨a⟩ := ha
      let d := c.symm.trans a
      let f := d.toMonoidHom.comp q
      refine ⟨f,?_,?_⟩
      · rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
      · rw [MonoidHom.range_eq_top.mpr
          (d.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 J)))]
        exact le_top
  have hp : ∀ Y : Subgroup J, (S : Subgroup J) ≤ Y →
      Y ≠ ⊤ → Y ≤ B.subgroupOf J := by
    intro Y hSY hne
    have hTY : (T : Subgroup G) ≤ Y.map J.subtype := by
      have hh := map_mono (f := J.subtype) hSY
      change ((T : Subgroup G).subgroupOf J).map J.subtype ≤ _ at hh
      rwa [map_subgroupOf_eq_of_le hJ.1.1.2] at hh
    have hYJ : Y.map J.subtype < J := by
      have hh := (map_lt_map_iff_of_injective J.subtype_injective).mpr
        (lt_top_iff_ne_top.mpr hne)
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    exact map_le_iff_le_comap.mp
      (le_inf (map_subtype_le _) (Chapter3.HStar.proper_overgroup_le T hJ hTY hYJ))
  have hB : B.subgroupOf J ≠ ⊤ := by
    intro he
    apply hJ.1.2
    intro j hj
    have hh : (⟨j,hj⟩ : J) ∈ B.subgroupOf J := he ▸ mem_top _
    exact hh.2
  obtain ⟨i,hi,_⟩ := Theory.SpecificGroups.Alternating.FiveExtensionAction.point_stabilizer_of_unique_maximal
    f hA (S : Subgroup J) (B.subgroupOf J) S.isPGroup' hB hp
  let fB := f.comp (B.subgroupOf J).subtype
  have him : fB.range ≤ MulAction.stabilizer (Equiv.Perm (Fin 5)) i := by
    rintro x ⟨b,rfl⟩
    exact show b.val ∈ (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).comap f from hi ▸ b.property
  have hcard : Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) = 24 := by
    have hh := (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).card_mul_index
    rw [MulAction.index_stabilizer_of_transitive,Nat.card_perm] at hh
    norm_num [Nat.factorial,Nat.card_fin] at hh
    rw [Nat.card_eq_fintype_card]
    change Fintype.card {g : Equiv.Perm (Fin 5) // g i = i} = 24
    omega
  have hPi : IsPiGroup twoThreePrimes fB.range := by
    rw [IsPiGroup_iff]
    intro p hp
    have hd := hp.trans (card_dvd_of_le him)
    rw [hcard] at hd
    change p.val = 2 ∨ p.val = 3
    have hd' : p.val ∣ 2 ^ 3 * 3 := by norm_num; exact hd
    rcases p.property.dvd_mul.mp hd' with ht | ht
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow ht) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp ht |>.resolve_left p.property.ne_one)
  have hk : IsPGroup 2 fB.rangeRestrict.ker := by
    have he : fB.rangeRestrict.ker = (pCore 2 J).subgroupOf (B.subgroupOf J) := by
      rw [MonoidHom.ker_rangeRestrict]
      ext b
      change f b.val = 1 ↔ b.val ∈ pCore 2 J
      exact show b.val ∈ f.ker ↔ b.val ∈ pCore 2 J from hfk ▸ Iff.rfl
    rw [he]
    exact pCore_isPGroup.comap_subtype
  have hres := twoResidual_eq_primeToResidual_three_of_two_kernel fB.rangeRestrict
    fB.rangeRestrict_surjective hk (twoResidual_eq_primeToResidual_three hPi)
  let cB := subgroupOfEquivOfLe (show B ≤ J from inf_le_left)
  have hresB : pResidual 2 B = primeToResidual 3 B := by
    have hh := congrArg (map cB.toMonoidHom) hres
    rwa [map_pResidual_of_surjective 2 cB.toMonoidHom cB.surjective,
      map_primeToResidual_of_surjective 3 cB.toMonoidHom cB.surjective] at hh
  apply borel_le_LT_of_residual hJ.1.1.2 H.chosen.sylow_normalizes_component
  change (pResidual 2 B).map B.subtype ≤ L
  rw [hresB]
  exact (embedded_primeToResidual_mono 3 (show B ≤ M L from inf_le_right)).trans_eq
    (H.normalizer_primeToResidual D)

/-- The A₅ module source alone now discharges all local group, quotient,
action, evenness, summand and Borel-placement inputs of 12.6.23. -/
theorem SourceHypothesis.fixed_hstar_not_one_or_two
    [IsElementaryAbelian 2 V]
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    ¬ Chapter6.Source.IsOneOrTwoA5Modules (localResidual J)
      ⁅localSpan T J,localResidual J⁆ := by
  intro hm
  have he : Nonempty ((localResidual J ⧸ pCore 2 (localResidual J)) ≃*
      alternatingGroup (Fin 5)) := by
    rcases hm with ⟨e,_,_⟩ | ⟨e,_,_⟩ <;> exact ⟨e⟩
  obtain ⟨e⟩ := he
  exact H.fixed_hstar_one_or_two_contradiction D hTV hTI hz hJ
    (H.fixed_hstar_borel_le_join D hJ e) hm

end CFSG.Quasithin.Chapter12.Section06
