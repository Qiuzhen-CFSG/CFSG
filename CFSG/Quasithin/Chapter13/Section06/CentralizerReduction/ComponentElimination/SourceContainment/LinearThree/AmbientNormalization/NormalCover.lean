module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.NoncentralLift
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.SourceInputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.CComponent.NonquasisimpleAction
public import Theory.GroupTheory.CComponent.QuasisimpleImageRigidity
public import Theory.GroupTheory.PResidual.NormalizerImage
public import Theory.Quasithin.Rank

/-!
# A normal containing component for the noncentral L₃(2) branch

The actual local family and the earlier A.3 containment and orbit theorems
place K in a normal C-component D of the original plus actor. Its plus image
equals K⁺. The noncentral projection then puts Lᵥ in D: the equivariant
commutator lift uses D's ambient normality and only the kernel on Lᵥ.
Moreover K supplements the intrinsic solvable radical of D.

If D/O₂(D) is quasisimple, Sylow normalization and supplement rigidity give
D = K, and hence the required normalization by Lᵥ. The exceptional odd-radical
alternatives of A.3.6 are not discharged here. In particular this module does
not assert ambient normalization for the whole source branch or assume that
the plus kernel is a two-group. The universal A.3 inputs also remain explicit.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.20,
printed p.931; 1.2.4, p.505; A.3.6 and A.3.12, pp.43–48.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization
open ComponentSelection Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The projection already lifts into any normalized overgroup of K.
This permits its use with the containing C-component before K itself has
been shown to be normal. -/
theorem lv_le_normalized_overgroup (K L T D : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (model : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hcomm : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥)
    (hKD : K ≤ D) (hLD : Lv L v ≤ normalizer (D : Set G)) : Lv L v ≤ D := by
  obtain ⟨f, hf, hne, _, hk, _⟩ :=
    exists_noncentral_projection K L T z v hL hz hK hn model hc hcomm
  have hgen :=
    (projection_parabolic_and_commutator K L T z v hL hz hK hn model f hf hc hne).2.2.2
  apply le_of_equivariant_projection (Lv L v) D (Tv T v ⊓ K)
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v))
    (inf_le_left.trans hL) (inf_le_right.trans hKD) hLD f
    (componentSylowMap K L T z v hL hz) (pCore_isPGroup.to_le hk) _ hgen
  intro s l
  apply Subtype.ext
  exact projection_equivariant K L T z v hL hz hK hn model f hf
    ⟨s, s.property.1⟩ l

private theorem radical_supplement_of_image_eq {A X : Type*}
    [Group A] [Finite A] [Group X] (q : A →* X)
    {B D : Subgroup A} (hD : D.IsCComponent) (hBD : B ≤ D)
    (he : B.map q = D.map q) (hne : D.map q ≠ ⊥) :
    solvableRadical D ⊔ B.subgroupOf D = ⊤ := by
  let g := q.subgroupMap D
  have hg : g.ker ≠ ⊤ := by
    intro ht
    apply hne
    apply (Subgroup.map_eq_bot_iff _).mpr
    intro d hd
    have h := ht ▸ (mem_top (⟨d, hd⟩ : D))
    exact congrArg Subtype.val (show g ⟨d, hd⟩ = 1 from h)
  let : Group.IsSolvable g.ker :=
    hD.isSolvable_of_subnormal_lt_top (inferInstance : g.ker.Normal).isSubnormal hg
  have hcover : B.subgroupOf D ⊔ g.ker = ⊤ := by
    apply top_unique
    intro d _
    obtain ⟨b, hb, he⟩ := he.symm ▸ mem_map_of_mem q d.property
    apply mem_sup_of_normal_right.mpr
    refine ⟨⟨b, hBD hb⟩, hb, ⟨b⁻¹ * d, D.mul_mem (D.inv_mem (hBD hb)) d.property⟩,
      ?_, ?_⟩
    · apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      change q (b⁻¹ * d) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    · apply Subtype.ext
      simp
  apply top_unique
  rw [← hcover]
  exact sup_le le_sup_right
    ((le_solvableRadical g.ker inferInstance inferInstance).trans le_sup_left)

/-- Construct D inside the original actor, with both containments and its
literal plus image. The radical supplement is intrinsic to this same D. -/
theorem exists_normal_cover {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧ NonnormalCComponentModel D)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (model : plusImage K L T z v hL hz K ≃* Matrix.PSL3Two.PSL)
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hcomm : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥) :
    ∃ D : Subgroup (plusActor K L T v),
      D.IsCComponent ∧ D.Normal ∧ K.subgroupOf (plusActor K L T v) ≤ D ∧
      Lv L v ≤ D.map (plusActor K L T v).subtype ∧
      D.map (plusMk K L T z v hL hz) = plusImage K L T z v hL hz K ∧
      solvableRadical D ⊔ (K.subgroupOf (plusActor K L T v)).subgroupOf D = ⊤ := by
  let A := plusActor K L T v
  let B := K.subgroupOf A
  have hKA : K ≤ A := K_le_plusActor K L T v
  have hTA : Tv T v ≤ A := le_sup_right
  have hAG : A ≤ Gv v := plusActor_le_Gv K L T v hK.1.1
  obtain ⟨S, hS⟩ := hSyl.restrict hTA hAG
  have hSeq : (S : Subgroup A) = (Tv T v).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTA]
  have hB : B ∈ Chapter1.L A (S : Subgroup A) := by
    rw [hSeq]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTA hKA).mp ⟨hKA, hK.1.2⟩
  have hsq : IsSQTK κ A := (IsSQTK.equiv (subgroupOfEquivOfLe hAG)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup (A.subgroupOf (Gv v)))
  have hsqQ : IsSQTK κ (A ⧸ pCore 2 A) := by
    refine ⟨?_, hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 A) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  obtain ⟨D, hD, hBD, _, hnormal⟩ :=
    lemma_1_2_4_containment_normality_of_A_3_12_A_3_8 hA312 hA38 hsqQ S hB
  have hSB : (S : Subgroup A) ≤ normalizer (B : Set A) := by
    rw [hSeq, ← subgroupOf_normalizer_eq hKA]
    exact comap_mono hn
  let : D.Normal := hnormal hSB
  let q := plusMk K L T z v hL hz
  have hP : (B.map q).IsCComponent :=
    (show IsComponent (Gplus K L T z v hL hz) (plusImage K L T z v hL hz K) from
      ⟨plusImage_K_subnormal K L T z v hL hz hK,
        plusImage_K_quasisimple K L T z v hL hz hK hR⟩).isCComponent
  have hDne : D.map q ≠ ⊥ := fun he => hP.ne_bot
    (bot_unique ((map_mono hBD).trans he.le))
  have hDf : (D.map q).IsCComponent :=
    (NonquasisimpleAction.ccomponent_image_or_bot hD q
      (QuotientGroup.mk'_surjective _)).resolve_left hDne
  have he : B.map q = D.map q := hP.eq_of_le hDf (map_mono hBD)
  have hKD : K ≤ D.map A.subtype := by
    simpa only [B, map_subgroupOf_eq_of_le hKA] using map_mono (f := A.subtype) hBD
  have hAD : A ≤ normalizer (D.map A.subtype : Set G) := by
    have h := D.le_normalizer_map A.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  refine ⟨D, hD, inferInstance, hBD,
    lv_le_normalized_overgroup K L T _ z v hL hz hK hn model hc hcomm hKD
      ((show Lv L v ≤ A from le_sup_right.trans le_sup_left).trans hAD),
    he.symm, radical_supplement_of_image_eq q hD hBD he hDne⟩

/-- The quasisimple branch needs no odd-radical rigidity: the two-core of
D lies in the supplied Sylow, so the actual K supplement equals D. -/
theorem normalizes_of_quasisimple_cover (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (D : Subgroup (plusActor K L T v)) (hD : D.IsCComponent)
    (hKD : K.subgroupOf (plusActor K L T v) ≤ D)
    (hLD : Lv L v ≤ D.map (plusActor K L T v).subtype)
    (he : D.map (plusMk K L T z v hL hz) = plusImage K L T z v hL hz K)
    (hne : plusImage K L T z v hL hz K ≠ ⊥)
    [IsQuasisimple (D ⧸ pCore 2 D)] : Lv L v ≤ normalizer (K : Set G) := by
  let A := plusActor K L T v
  let B := K.subgroupOf A
  have hKA : K ≤ A := K_le_plusActor K L T v
  have hTA : Tv T v ≤ A := le_sup_right
  obtain ⟨S, hS⟩ := hSyl.restrict hTA (plusActor_le_Gv K L T v hK.1.1)
  have hSeq : (S : Subgroup A) = (Tv T v).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTA]
  have hSB : (S : Subgroup A) ≤ normalizer (B : Set A) := by
    rw [hSeq, ← subgroupOf_normalizer_eq hKA]
    exact comap_mono hn
  have hcore : (pCore 2 D).map D.subtype ≤ (S : Subgroup A) :=
    (pCoreIn_le_of_subnormal 2 hD.subnormal).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hnorm : pCore 2 D ≤ normalizer (B.subgroupOf D : Set D) := by
    rw [← subgroupOf_normalizer_eq hKD]
    exact (map_le_iff_le_comap.mp hcore).trans (comap_mono hSB)
  have hBD : B = D := IsCComponent.eq_of_image_eq_of_twoCore_normalizes
    (plusMk K L T z v hL hz) hD hKD he.symm (he ▸ hne) hnorm
  have hDK : D.map A.subtype = K := by
    rw [← hBD, map_subgroupOf_eq_of_le hKA]
  exact (hLD.trans hDK.le).trans K.le_normalizer

private theorem perfect_twoPerfect {H : Type*} [Group H] [Finite H]
    [Group.IsPerfect H] : IsPPerfect 2 H := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (H ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (H ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance

/-- Normalization can be tested modulo the intrinsic O₂(D), with its
kernel-normalization hypothesis proved from the actual source Sylow.
This uses neither the star kernel nor the plus kernel. -/
theorem normalizes_of_twoCore_image (K L T : Subgroup G) (z v : G)
    (hK : K ∈ Yz L T z v)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (D : Subgroup (plusActor K L T v)) (hD : D.IsCComponent)
    (hKD : K.subgroupOf (plusActor K L T v) ≤ D)
    (hLD : Lv L v ≤ D.map (plusActor K L T v).subtype)
    (himage : ((Lv L v).subgroupOf (plusActor K L T v)).subgroupOf D ≤
      (normalizer (((K.subgroupOf (plusActor K L T v)).subgroupOf D).map
        (QuotientGroup.mk' (pCore 2 D)) : Set (D ⧸ pCore 2 D))).comap
          (QuotientGroup.mk' (pCore 2 D))) :
    Lv L v ≤ normalizer (K : Set G) := by
  let A := plusActor K L T v
  let B := K.subgroupOf A
  let B' := B.subgroupOf D
  have hKA : K ≤ A := K_le_plusActor K L T v
  have hTA : Tv T v ≤ A := le_sup_right
  obtain ⟨S, hS⟩ := hSyl.restrict hTA (plusActor_le_Gv K L T v hK.1.1)
  have hSeq : (S : Subgroup A) = (Tv T v).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hS, map_subgroupOf_eq_of_le hTA]
  have hSB : (S : Subgroup A) ≤ normalizer (B : Set A) := by
    rw [hSeq, ← subgroupOf_normalizer_eq hKA]
    exact comap_mono hn
  have hcore : (pCore 2 D).map D.subtype ≤ (S : Subgroup A) :=
    (pCoreIn_le_of_subnormal 2 hD.subnormal).trans (pCore_isPGroup.le_sylow_of_normal S)
  have hnorm : pCore 2 D ≤ normalizer (B' : Set D) := by
    rw [← subgroupOf_normalizer_eq hKD]
    exact (map_le_iff_le_comap.mp hcore).trans (comap_mono hSB)
  let := Chapter1.mem_L_isPerfect hK.1.2
  let e : B' ≃* K := (subgroupOfEquivOfLe hKD).trans (subgroupOfEquivOfLe hKA)
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hker : IsPGroup 2 (QuotientGroup.mk' (pCore 2 D)).ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkn : (QuotientGroup.mk' (pCore 2 D)).ker ≤ normalizer (B' : Set D) := by
    rwa [QuotientGroup.ker_mk']
  rw [comap_normalizer_map_of_pPerfect _ B' perfect_twoPerfect hker hkn] at himage
  have hnB : (B'.map D.subtype).map A.subtype = K := by
    rw [map_subgroupOf_eq_of_le hKD, map_subgroupOf_eq_of_le hKA]
  intro l hl
  obtain ⟨d, hd, hdl⟩ := hLD hl
  change (d : G) = l at hdl
  have hdL : (⟨d, hd⟩ : D) ∈ ((Lv L v).subgroupOf A).subgroupOf D := by
    change (d : G) ∈ Lv L v
    simpa only [hdl] using hl
  have hdN := himage hdL
  rw [← hnB]
  have h := (B'.map D.subtype).le_normalizer_map A.subtype
    (mem_map_of_mem A.subtype (B'.le_normalizer_map D.subtype
      (mem_map_of_mem D.subtype hdN)))
  exact hdl ▸ h

/-- Source application on the actual A₅ marking. The Sylow and cubic
premises come from the constructed local configuration; the earlier reduced
module supplies O₂(G⁺)=1. The noncentrality producer remains independent. -/
theorem exists_normal_cover_of_source
    {K L M V V₁ V₂ : Subgroup G} {T : Sylow 2 G}
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (f : A5Module.FlagMarking T L V V₁ V₂) (c : LocalConfiguration M f)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ D : Subgroup X, D.IsCComponent → D.Normal ∨
        (normalizer (D : Set X)).index = 2 ∧ NonnormalCComponentModel D)
    (hK : K ∈ Yz L (T : Subgroup G) (A5Module.markedZ f.module) (A5Module.markedV f.module))
    (hn : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    (hz : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hred : WK K L (T : Subgroup G) (A5Module.markedZ f.module) (A5Module.markedV f.module) ∈
      Chapter6.Source.reducedFamily (plusActor K L (T : Subgroup G) (A5Module.markedV f.module)))
    (model : plusImage K L (T : Subgroup G) (A5Module.markedZ f.module)
      (A5Module.markedV f.module) hL hz K ≃* Matrix.PSL3Two.PSL)
    (hcomm : ⁅plusImage K L (T : Subgroup G) (A5Module.markedZ f.module)
        (A5Module.markedV f.module) hL hz K,
      plusImage K L (T : Subgroup G) (A5Module.markedZ f.module) (A5Module.markedV f.module)
        hL hz (Lv L (A5Module.markedV f.module))⁆ ≠ ⊥) :
    ∃ D : Subgroup (plusActor K L (T : Subgroup G) (A5Module.markedV f.module)),
      D.IsCComponent ∧ D.Normal ∧
      K.subgroupOf (plusActor K L (T : Subgroup G) (A5Module.markedV f.module)) ≤ D ∧
      Lv L (A5Module.markedV f.module) ≤ D.map
        (plusActor K L (T : Subgroup G) (A5Module.markedV f.module)).subtype ∧
      D.map (plusMk K L (T : Subgroup G) (A5Module.markedZ f.module)
        (A5Module.markedV f.module) hL hz) =
        plusImage K L (T : Subgroup G) (A5Module.markedZ f.module)
          (A5Module.markedV f.module) hL hz K ∧
      solvableRadical D ⊔ (K.subgroupOf
        (plusActor K L (T : Subgroup G) (A5Module.markedV f.module))).subgroupOf D = ⊤ := by
  have hv : orderOf (A5Module.markedV f.module) = 2 := by
    apply (orderOf_eq_prime_iff (p := 2)).mpr
    refine ⟨?_, A5Module.markedV_ne_one f.module⟩
    change f.module.map _ ^ 2 = 1
    rw [← map_pow]
    exact (congrArg f.module.map
      (show (Multiplicative.ofAdd BinaryPermutation.FiveCentralizerGeometry.v) ^ 2 = 1
        by decide +kernel)).trans f.module.map.map_one
  exact exists_normal_cover standing.qtke hA312 hA38 K L (T : Subgroup G)
    (A5Module.markedZ f.module) (A5Module.markedV f.module) hv hK
    ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩ hn hL hz
    (RankTwo.LocalApplication.plus_twoCore_eq_bot_of_reduced _ _ _ _ _ hL hz hred)
    model c.residual_card hcomm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.AmbientNormalization
