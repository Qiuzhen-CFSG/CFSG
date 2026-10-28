module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.IntrinsicModels.RecognitionInput
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ActionKernels
public import Theory.Quasithin.Rank

/-!
# Intrinsic markings from the literal component action

The original subgroup maps onto its plus image by the composite of the
star map and the restricted star-to-plus map. Its kernel is exactly
C_K(W_K). The two-reduced plus action kills O₂(K).

Apply universal A.3.6 to the image of the local C-component in its ambient
two-core quotient. The independent catalogue comparison in RecognitionInput
then makes the induced surjection to SL₄(2) injective. Transporting back
gives K/O₂(K) ≃ SL₄(2), with the original action map as representative
formula, and proves C_K(W_K) = O₂(K).

The A.3.6 comparison remains an explicit, separately tracked obligation.
These conditional constructions do not yet discharge it.
Source: Aschbacher–Smith, 13.6.23, p.933, with A.3.3 and A.3.6.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection
universe u
variable {G : Type u} [Group G]

/-- The actual action map on the original component, through the star quotient. -/
noncomputable def intrinsicToPlus (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K →* plusImage K L T z v hL hz K :=
  (componentStarToPlus K L T z v hK hL hz).comp (starImageMap z v K hK)

theorem intrinsicToPlus_surjective (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (intrinsicToPlus K L T z v hK hL hz) :=
  (componentStarToPlus_surjective K L T z v hK hL hz).comp
    (starImageMap_surjective z v K hK)

/-- The kernel is computed in K itself, not in K*. -/
theorem intrinsicToPlus_ker (K L T : Subgroup G) (z v : G)
    (hK : K ≤ Gv v) (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (intrinsicToPlus K L T z v hK hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  ext x
  change componentStarToPlus K L T z v hK hL hz (starImageMap z v K hK x) = 1 ↔ _
  rw [Subtype.ext_iff, componentStarToPlus_mk]
  change inclusion (K_le_plusActor K L T v) x ∈ (plusMk K L T z v hL hz).ker ↔ _
  rw [plusMk_ker]
  rfl

private theorem twoCore_le_ker {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) (hB : pCore 2 B = ⊥) :
    pCore 2 A ≤ f.ker := by
  have hm : (pCore 2 A).map f ≤ pCore 2 B :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f hf, pCore_isPGroup.map f⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans hB.le))

variable [Finite G]

/-- Universal A.3.6 is applied in the actual ambient two-core quotient.
The catalogue comparison is the sole additional recognition premise. -/
noncomputable def cComponentFourEquiv {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hrecognition : A36RankFourRecognition.{u})
    (hG : IsSQTK 𝒦 G) (B : Subgroup G) (hB : B.IsCComponent)
    (f : B →* SL(4, ZMod 2)) (hf : Function.Surjective f)
    (hcore : pCore 2 SL(4, ZMod 2) = ⊥) :
    B ⧸ pCore 2 B ≃* SL(4, ZMod 2) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G) := by
    refine ⟨?_, hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let := pCore_isNilpotent (p := 2) (G := G)
  have hBq : (B.map q).IsCComponent := hB.map_quotient _
  let fQ := QuotientGroup.lift (pCore 2 B) f (twoCore_le_ker f hf hcore)
  have hfQ : Function.Surjective fQ := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let eB := cComponentTwoCoreQuotientEquiv hB
  let g := fQ.comp eB.symm.toMonoidHom
  have hg : Function.Surjective g := hfQ.comp eB.symm.surjective
  have hi : Function.Injective g := hrecognition _ _ hBq
    (hA36 _ hQ (pCore_quotient_pCore_eq_bot 2) _ hBq) g hg
  exact eB.trans (MulEquiv.ofBijective g ⟨hi, hg⟩)

/-- The constructed equivalence retains the given epimorphism on representatives. -/
theorem cComponentFourEquiv_mk {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hrecognition : A36RankFourRecognition.{u})
    (hG : IsSQTK 𝒦 G) (B : Subgroup G) (hB : B.IsCComponent)
    (f : B →* SL(4, ZMod 2)) (hf : Function.Surjective f)
    (hcore : pCore 2 SL(4, ZMod 2) = ⊥) (b : B) :
    cComponentFourEquiv hA36 hrecognition hG B hB f hf hcore
      (QuotientGroup.mk' _ b) = f b := by
  change (QuotientGroup.lift (pCore 2 B) f (twoCore_le_ker f hf hcore))
    ((cComponentTwoCoreQuotientEquiv hB).symm
      ((cComponentTwoCoreQuotientEquiv hB) (QuotientGroup.mk' _ b))) = f b
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The action marking of K⁺ gives an intrinsic marking of K/O₂(K),
conditional only on the remaining catalogue comparison and universal A.3.6. -/
theorem exists_intrinsic_four_marking {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hrecognition : A36RankFourRecognition.{u})
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) :
    ∃ eK : K ⧸ pCore 2 K ≃* SL(4, ZMod 2),
      ∀ k : K, eK (QuotientGroup.mk' _ k) =
        e (intrinsicToPlus K L T z v hK.1.1 hL hz k) := by
  let H := K ⊔ Tv T v
  let B := K.subgroupOf H
  have hHG : H ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hH : IsSQTK 𝒦 H := (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp
    (hlocal.subgroup (H.subgroupOf (Gv v)))
  let eB : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let f := (e.toMonoidHom.comp (intrinsicToPlus K L T z v hK.1.1 hL hz)).comp eB.toMonoidHom
  have hf : Function.Surjective f := e.surjective.comp
    ((intrinsicToPlus_surjective K L T z v hK.1.1 hL hz).comp eB.surjective)
  have hplus : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (plusImage K L T z v hL hz K).ker_subtype
  have hfour : pCore 2 SL(4, ZMod 2) = ⊥ := by
    rw [← pCore_map_iso 2 e, hplus, Subgroup.map_bot]
  let c := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  let d := cComponentFourEquiv hA36 hrecognition hH B hK.1.2.1 f hf hfour
  refine ⟨c.symm.trans d, ?_⟩
  intro k
  obtain ⟨b, rfl⟩ := eB.surjective k
  have hc : c (QuotientGroup.mk' _ b) = QuotientGroup.mk' _ (eB b) := rfl
  change d (c.symm (QuotientGroup.mk' _ (eB b))) = _
  rw [← hc, c.symm_apply_apply]
  exact cComponentFourEquiv_mk hA36 hrecognition hH B hK.1.2.1 f hf hfour b

/-- The representative formula identifies the full original action kernel
with the intrinsic two-core. The catalogue obligation remains explicit. -/
theorem intrinsic_action_kernel_eq_twoCore {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → Chapter1.Section02.A36Conclusion B)
    (hrecognition : A36RankFourRecognition.{u})
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* SL(4, ZMod 2)) :
    (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K := by
  obtain ⟨eK, heK⟩ := exists_intrinsic_four_marking hA36 hrecognition
    K L T z v hlocal hL hz hK hR e
  rw [← intrinsicToPlus_ker K L T z v hK.1.1 hL hz]
  ext k
  change intrinsicToPlus K L T z v hK.1.1 hL hz k = 1 ↔ k ∈ pCore 2 K
  calc
    _ ↔ e (intrinsicToPlus K L T z v hK.1.1 hL hz k) = 1 := e.map_eq_one_iff.symm
    _ ↔ eK (QuotientGroup.mk' _ k) = 1 := by rw [heK]
    _ ↔ QuotientGroup.mk' (pCore 2 K) k = 1 := eK.map_eq_one_iff
    _ ↔ k ∈ pCore 2 K := QuotientGroup.eq_one_iff _

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
