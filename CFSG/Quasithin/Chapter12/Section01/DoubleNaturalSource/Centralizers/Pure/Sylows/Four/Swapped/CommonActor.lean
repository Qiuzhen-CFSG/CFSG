module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.NormalizedActor

/-!
# One moving cubic actor in the original swapped configuration

Choose a starred cubic actor on the actual faithful FSU module. Each original
component has cubic ratio greater than two on both the module and its fixed
quotient, so neither component contains this actor. A component normalized
by the actor is centralized, by the exact homogeneous quotient construction.
The normal pair has two-group quotient and trivial centralizer; therefore
the actor cannot normalize both components.

The final theorem constructs this common actor from the original marked pure
point, contrary ambient Sylow assumption and fixed-subgroup premise, retaining
the actual conjugation action and both component markings. Excluding the
remaining actor which moves components, and the ambient Sylow/core/fusion/
abelian-closure assembly, remain with qt-d-double-natural-pure-fusion. The
original fixed-subgroup premise remains with qt-rank-two-ms93 and final
qt-d-double-natural-centralizers; no MS classification is assumed proved.

Source: Aschbacher--Smith D.2.7, D.3.5--9 and 12.1.4,
printed pp.190,195--201,790--791 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding Representation.BinaryOffender.Homogeneous
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem cubic_actor_not_le_of_restriction
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (C E : Subgroup Q)
    (hC : 2 < cubicRatio (ρ.comp C.subtype))
    (hE : E ∈ ChapterD.QhatStar ρ) : ¬ E ≤ C := by
  intro hEC
  let : IsElementaryAbelian 2 E := hE.1.2.1.2
  have hEl : IsElementaryTwo (E.subgroupOf C) := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hEC⟩
    intro he
    exact hE.1.2.1.1 (by rw [←map_subgroupOf_eq_of_le hEC,he,Subgroup.map_bot])
  have hc : IsCubic (ρ.comp C.subtype) (E.subgroupOf C) :=
    fun a ha b hb c hc v => hE.1.2.2.1 a ha b hb c hc v
  have hd := (actionRatio_le_nat_iff ρ hE.1.2.1 2).mp
    (hE.1.2.2.2.trans_le hE.1.1)
  have hd' : fixedCodim (ρ.comp C.subtype) (E.subgroupOf C) ≤
      2 * rank (E.subgroupOf C) := by
    rwa [fixedCodim_subgroupOf ρ hEC,rank_subgroupOf hEC]
  exact (not_lt_of_ge ((cubicRatio_le_nat_iff (ρ.comp C.subtype) 2).mpr
    ⟨E.subgroupOf C,hEl,hc,hd'⟩)) hC

/-- One original starred actor, with the cubic barriers and its component action. -/
@[expose] def CommonCubicActorPair
    {Q U : Type*} [Group Q] [Finite Q] [AddCommGroup U]
    [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) Q U) (C₁ C₂ : Subgroup Q)
    (K : Type*) [Group K] : Prop :=
    ∃ E : Subgroup Q, E ∈ ChapterD.QhatStar ρ ∧
      (¬ E ≤ normalizer (C₁ : Set Q) ⊓ normalizer (C₂ : Set Q)) ∧
      ∀ C ∈ ({C₁,C₂} : Set (Subgroup Q)),
        IsComponent Q C ∧ Nonempty (C ≃* K) ∧
        2 < cubicRatio (ρ.comp C.subtype) ∧
        2 < cubicRatio ((fixedQuotient ρ ⊤).comp C.subtype) ∧
        (¬ E ≤ C) ∧
        (E ≤ normalizer (C : Set Q) → E ≤ centralizer (C : Set Q))

private theorem pair_centralizer_eq_bot
    {Q : Type*} [Group Q] [Finite Q]
    (C₁ C₂ : Subgroup Q) (h₁ : IsComponent Q C₁) (h₂ : IsComponent Q C₂)
    [IsSimpleGroup C₁] [IsSimpleGroup C₂]
    (hne : C₁ ≠ C₂) [(C₁ ⊔ C₂).Normal]
    (hquot : IsPGroup 2 (Q ⧸ (C₁ ⊔ C₂))) (hcore : pCore 2 Q = ⊥) :
    centralizer ((C₁ ⊔ C₂ : Subgroup Q) : Set Q) = ⊥ := by
  let N := centralizer ((C₁ ⊔ C₂ : Subgroup Q) : Set Q)
  let := h₁.2
  let := h₂.2
  have hZ₁ : center C₁ = ⊥ :=
    (inferInstance : (center C₁).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C₁ (center_eq_top_iff.mp he))
  have hZ₂ : center C₂ = ⊥ :=
    (inferInstance : (center C₂).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative C₂ (center_eq_top_iff.mp he))
  have havoid₁ : ¬ C₁ ≤ N := fun hh =>
    Group.IsPerfect.not_isMulCommutative C₁
      (le_centralizer_iff_isMulCommutative.mp (hh.trans (centralizer_le (show C₁ ≤ C₁ ⊔ C₂ from le_sup_left))))
  have havoid₂ : ¬ C₂ ≤ N := fun hh =>
    Group.IsPerfect.not_isMulCommutative C₂
      (le_centralizer_iff_isMulCommutative.mp (hh.trans (centralizer_le (show C₂ ≤ C₁ ⊔ C₂ from le_sup_right))))
  have hp := isTwoGroup_of_normal_avoiding_component_pair C₁ C₂ N h₁ h₂ hne
    hZ₁ hZ₂ hquot havoid₁ havoid₂
  have hle : N ≤ pCore 2 Q := le_sSup ⟨inferInstance,hp⟩
  exact bot_unique (hle.trans hcore.le)

/-- The two component applications share one starred actor of the original action. -/
theorem local_quotient_common_cubic_actor
    [IsSimpleGroup (L ⧸ pCore 2 L)]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) (XiQuotient (localJoin T L)) U)
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2)
    (hsqQ : IsSQTK KnownSimple.IsKnownSimple (XiQuotient (localJoin T L)))
    (C₁ C₂ : Subgroup (XiQuotient (localJoin T L)))
    (hCs : ∀ C ∈ ({C₁,C₂} : Set (Subgroup (XiQuotient (localJoin T L)))),
      IsComponent (XiQuotient (localJoin T L)) C ∧ Nonempty (C ≃* XiQuotient L))
    (hne : C₁ ≠ C₂) (hnorm : (C₁ ⊔ C₂).Normal)
    (hpair : C₁ ⊔ C₂ = ((localOrbit T L).subgroupOf (localJoin T L)).map
      (QuotientGroup.mk' (pCore 2 (localJoin T L))))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (XiQuotient L))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient L) 2 p)
    (hmod : p % 24 = 11 ∨ p % 24 = 13) :
    CommonCubicActorPair ρ C₁ C₂ (XiQuotient L) := by
  obtain ⟨E,hE⟩ := (ChapterD.QhatStar_nonempty_iff ρ).mpr hc
  have hEs : ∀ C ∈ ({C₁,C₂} : Set (Subgroup (XiQuotient (localJoin T L)))),
      IsComponent (XiQuotient (localJoin T L)) C ∧ Nonempty (C ≃* XiQuotient L) ∧
      2 < cubicRatio (ρ.comp C.subtype) ∧
      2 < cubicRatio ((fixedQuotient ρ ⊤).comp C.subtype) ∧ (¬ E ≤ C) ∧
      (E ≤ normalizer (C : Set (XiQuotient (localJoin T L))) →
        E ≤ centralizer (C : Set (XiQuotient (localJoin T L)))) := by
    intro C hC
    obtain ⟨hcomp,heC⟩ := hCs C hC
    have hb := local_quotient_component_cubic_barrier ρ hf C hcomp heC hsq hp ho hm hmod
    let := hcomp.2
    let : IsSimpleGroup C := heC.some.isSimpleGroup
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
    have hmC : ClassicalGroup.IsPSL C 2 p :=
      ⟨F,inferInstance,inferInstance,hF,⟨heC.some.trans a⟩⟩
    exact ⟨hcomp,heC,hb.1,hb.2,cubic_actor_not_le_of_restriction ρ C E hb.1 hE,
      (fun hn => normalized_rank_one_component_centralized ρ hf hsqQ E C hE hn hp ho hmC hmod)⟩
  have h₁ := hEs C₁ (by simp)
  have h₂ := hEs C₂ (by simp)
  let : IsSimpleGroup C₁ := h₁.2.1.some.isSimpleGroup
  let : IsSimpleGroup C₂ := h₂.2.1.some.isSimpleGroup
  let := hnorm
  let H := localJoin T L
  let q := QuotientGroup.mk' (pCore 2 H)
  let S := ((T : Subgroup G).subgroupOf H).map q
  have hS : IsPGroup 2 S := (T.isPGroup'.comap_subtype).map q
  have hgen : (C₁ ⊔ C₂) ⊔ S = ⊤ := by
    rw [hpair,←Subgroup.map_sup,←subgroupOf_sup
      (show localOrbit T L ≤ H from le_sup_left)
      (show (T : Subgroup G) ≤ H from le_sup_right),subgroupOf_self,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hquot := isPGroup_quotient_of_sup_eq_top (C₁ ⊔ C₂) S hS hgen
  have hcent := pair_centralizer_eq_bot C₁ C₂ h₁.1 h₂.1 hne hquot
    (pCore_quotient_pCore_eq_bot 2)
  refine ⟨E,hE,?_,hEs⟩
  intro hn
  have he₁ := h₁.2.2.2.2.2 (hn.trans inf_le_left)
  have he₂ := h₂.2.2.2.2.2 (hn.trans inf_le_right)
  have he : E ≤ centralizer ((C₁ ⊔ C₂ : Subgroup (XiQuotient H)) : Set (XiQuotient H)) :=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp he₁) (le_centralizer_iff.mp he₂))
  exact hE.1.2.1.1 (bot_unique (he.trans hcent.le))

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.PureFourXi

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open Chapter3.Section02 Representation.BinaryOffender.Homogeneous
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- The original swapped witness has one starred actor which moves a component,
centralizes each component it normalizes, and belongs to neither component. -/
theorem doubleNatural_four_pure_common_cubic_actor_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ (P : Sylow 2 G) (A : Sylow 3 X) (K : Subgroup G)
        (F : FundamentalSetup KnownSimple.IsKnownSimple T K),
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
          ((A : Subgroup X).map X.subtype) H K ∧
        conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
        X < componentOrbit K (T : Subgroup G) ∧
        (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
          (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
        elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (F.moduleSubgroup : Set G) ∧
        F.moduleSubgroup ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        letI := F.module_elementary
        let Q := XiQuotient (localJoin T K)
        let q := QuotientGroup.mk' (pCore 2 (localJoin T K))
        let K₁ := (K.subgroupOf (localJoin T K)).map q
        ∃ ρ : Representation (ZMod 2) Q (Additive F.moduleSubgroup),
          Function.Injective ρ ∧ Function.Injective (fixedQuotient ρ ⊤) ∧
          (∀ (x : localJoin T K) (v : F.moduleSubgroup),
            (ρ (q x) (Additive.ofMul v)).toMul =
              ⟨(x : G) * v * (x : G)⁻¹,
                (F.join_normalizes_module x.property v).mp v.property⟩) ∧
          cubicRatio ρ ≤ 2 ∧ cubicRatio (fixedQuotient ρ ⊤) ≤ 2 ∧
          ∃ t : localJoin T K, (t : G) ∈ T ∧ (t : G) ∉ normalizer (K : Set G) ∧
            let K₂ := K₁.map (MulAut.conj (q t)).toMonoidHom
            K₁ ≠ K₂ ∧ (K₁ ⊔ K₂).Normal ∧
            K₁ ⊔ K₂ = ((localOrbit T K).subgroupOf (localJoin T K)).map q ∧
            PureFourXi.CommonCubicActorPair ρ K₁ K₂ (XiQuotient K) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,A,K,F,hs,he,hstrict,hodd,hJF,hFQ,ρ,hρ,hρq,hact,hρc,hρqc,
      t,ht,htn,hneK,hnK,hpair,hCs⟩ :=
    D.doubleNatural_four_pure_faithful_sections_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  obtain ⟨_,hmodel⟩ := SwappedSylow.nonnormal_model_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hs.toSwappedInput
  let : IsSimpleGroup (XiQuotient K) :=
    SwappedFactorsProof.quotient_simple hs.toSwappedInput hmodel
  have hsqK : IsSQTK KnownSimple.IsKnownSimple (XiQuotient K) :=
    (IsSQTK.equiv (SwappedFactorsProof.componentImageEquiv hs.toSwappedInput hs.component
      (le_componentOrbit K (T : Subgroup G)))).mpr
        ((SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).subgroup _)
  have hJH : localJoin T K ≤ (P : Subgroup G) ⊔ (PureFourXi.residual T L ⊔ (T : Subgroup G)) :=
    sup_le (SwappedSylow.orbit_le_overgroup hs.toSwappedInput)
      (le_sup_right.trans hs.overgroup)
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (localJoin T K) :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hJH)).mp (hs.sqtk.subgroup _)
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (XiQuotient (localJoin T K)) :=
    ⟨quotient_stronglyQuasithin hsqJ.stronglyQuasithin,hsqJ.isKGroup.quotient _⟩
  obtain ⟨p,hp',ho,hm,h8,h24⟩ := hodd
  let := F.module_elementary
  refine ⟨P,A,K,F,hs,he,hstrict,⟨p,hp',ho,hm,h8,h24⟩,hJF,hFQ,ρ,hρ,hρq,hact,hρc,hρqc,
    t,ht,htn,hneK,hnK,hpair,?_⟩
  exact PureFourXi.local_quotient_common_cubic_actor ρ hρ hρc hsqQ _ _
    (fun C hC => ⟨(hCs C hC).1,(hCs C hC).2.1⟩) hneK hnK hpair hsqK hp' ho hm h24
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
