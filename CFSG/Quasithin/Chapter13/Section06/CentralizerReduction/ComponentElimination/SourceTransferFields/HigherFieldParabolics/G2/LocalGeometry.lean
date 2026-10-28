module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2
public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance
public import Theory.GroupTheory.RelativeNormalizerTransport

/-!
# Local geometry of the lifted G₂ parabolics

This file records the source-side geometry which is needed after the two
full G₂ parabolics have been pulled back to `K`.  The quotient marking is kept
literal: the subgroup occurring in the normalizer transport is the image of
the actual `Tᵥ ∩ K`, and the kernel used in the pullback arguments is the
actual relative centralizer `C_K(W_K)`.

The remaining marked-action and C.1.26 hypotheses are parameters of the
conditional statements below.  This is the interface used by the final
13.6.19 assembly; no family tag or abstract quotient is substituted for the
source subgroup.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 13.6.16 and
13.6.19, printed pp.930--931; B.6.1 and C.1.26.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp
open CFSG.Quasithin.Chapter1
open Atlas.G2.HigherFieldResiduals
open Atlas.G2.LieParabolicSetup
open Atlas.G2.SylowParabolicInvariance

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2

universe u

variable {G : Type u} [Group G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable {F : Type*} [Field F] [CharP F 2]
variable (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)

lemma parabolic_stable (β : MulAut (Atlas.G2.Model F))
    (hβ : Atlas.G2.unipotent.map β.toMonoidHom = Atlas.G2.unipotent) (i : Fin 2) :
    (parabolicAt (F := F) i).map β.toMonoidHom = parabolicAt i := by
  have ha := map_eq_of_centralInvolutions Atlas.G2.unipotent highestRoot
    highestRoot_iff_centralInvolution β hβ
  have hb := map_eq_of_secondCentralInvolutions Atlas.G2.unipotent Atlas.G2.longRootLocal
    longRootLocal_iff_secondCentralInvolution β hβ
  fin_cases i
  · change parabolic₁.map β.toMonoidHom = parabolic₁
    rw [← normalizer_highestRoot, map_equiv_normalizer_eq, ha]
  · change parabolic₂.map β.toMonoidHom = parabolic₂
    rw [← normalizer_longRootLocal, map_equiv_normalizer_eq, hb]

/- The intersection Sylow is transported through the actual subgroup `K`.
   Keeping this proof here avoids silently replacing it by a Sylow of a
   quotient image. -/
theorem sylow_intersection [Finite G] (hK : K ∈ Yz L T z v)
    (hKinvar : Tv T v ≤ normalizer (K : Set G)) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K).map K.subtype = Tv T v ⊓ K := by
  let H := K ⊔ Tv T v
  have hKH : K ≤ H := le_sup_left
  have hnorm : (K.subgroupOf H).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hKH).mpr
    intro x hx
    exact sup_le K.le_normalizer hKinvar hx
  let _ : (K.subgroupOf H).Normal := hnorm
  obtain ⟨P, hP⟩ := hK.1.2.2.1
  let eKH := Subgroup.subgroupOfEquivOfLe hKH
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal (K.subgroupOf H)
  let QK : Sylow 2 K := Q.mapSurjective (f := eKH.toMonoidHom) eKH.surjective
  refine ⟨QK, ?_⟩
  change ((Q : Subgroup (K.subgroupOf H)).map eKH.toMonoidHom).map K.subtype = _
  rw [Subgroup.map_map]
  have hecomp : K.subtype.comp eKH.toMonoidHom =
      H.subtype.comp (K.subgroupOf H).subtype := by
    ext x
    rfl
  rw [hecomp, hQ, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    Subgroup.map_inf _ _ H.subtype H.subtype_injective, hP,
    Subgroup.map_subgroupOf_eq_of_le hKH]

theorem marked_sylow_eq_unipotent [Finite G] [Finite F]
    (hK : K ∈ Yz L T z v)
    (hKinvar : Tv T v ≤ normalizer (K : Set G))
    (hmark : ((Tv T v ⊓ K).subgroupOf K).map
      (modelMap K L T z v hL hz e) ≤ Atlas.G2.unipotent) :
    ∃ Q : Sylow 2 (Atlas.G2.Model F), (Q : Subgroup (Atlas.G2.Model F)) = Atlas.G2.unipotent := by
  obtain ⟨QK, hQK⟩ := sylow_intersection K L T z v hK hKinvar
  let Q : Sylow 2 (Atlas.G2.Model F) :=
    QK.mapSurjective (f := modelMap K L T z v hL hz e)
      (modelMap_surjective K L T z v hL hz e)
  have hQK' : (QK : Subgroup K) = (Tv T v ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
    exact hQK
  have hQ : (Q : Subgroup (Atlas.G2.Model F)) =
      ((Tv T v ⊓ K).subgroupOf K).map (modelMap K L T z v hL hz e) := by
    simp only [Q, Sylow.coe_mapSurjective, hQK']
  refine ⟨Q, le_antisymm (hQ ▸ hmark) ?_⟩
  exact (Q.is_maximal' (Atlas.G2.LieParabolicSetup.unipotent_isTwoGroup (F := F))
    (hQ ▸ hmark)).le

/- The actual plus image of `Tᵥ` normalizes the actual plus image of `K`.
   This is a quotient-map statement, so it does not use an unverified
   equality between a marked image and its ambient family tag. -/
theorem plusImage_tv_normalizer
    (hKinvar : Tv T v ≤ normalizer (K : Set G)) :
    plusImage K L T z v hL hz (Tv T v) ≤
      normalizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) := by
  let A := plusActor K L T v
  have hKA : K ≤ A :=
    (le_conjugateSpanBy K (Tv T v)).trans (le_sup_left.trans le_sup_left)
  have hnormA : (Tv T v).subgroupOf A ≤ normalizer (K.subgroupOf A) := by
    rw [← subgroupOf_normalizer_eq hKA]
    intro x hx
    change (x : G) ∈ normalizer (K : Set G)
    exact hKinvar hx
  exact (map_mono hnormA).trans (le_normalizer_map (plusMk K L T z v hL hz))

/- The local-family membership used by the terminal obstruction is assembled
   from the three source clauses, with the ambient subgroup retained. -/
theorem residualIn_mem_LIn_of_source_clauses [Finite G]
    (P H S : Subgroup G) (hPS : residualIn P ≤ H)
    (hcomp : ((residualIn P).subgroupOf (residualIn P ⊔ S)).IsCComponent)
    (hsylow : IsSylowIn 2 S (residualIn P ⊔ S))
    (hcore : (residualIn P ⊔ S).pCoreIn 2 ≠ ⊥) :
    residualIn P ∈ Chapter1.LIn H S := by
  refine ⟨hPS, ?_⟩
  exact ⟨hcomp, hsylow, hcore⟩

/- B.6.1 is applied to each genuinely aligned Sylow.  The ambient-image
   equality is an argument of the source clauses, rather than a containment
   silently promoted to equality. -/
theorem minimal_parabolic_over_of_aligned_source [Finite G]
    (H S : Subgroup G)
    (hsource : ∀ Q : Sylow 2 H,
      (Q : Subgroup H).map H.subtype = S →
      Order.HasUniqueMaximalOver (Q : Subgroup H) (⊤ : Subgroup H) ∧
        ¬ ((Q : Subgroup H).subgroupOf (⊤ : Subgroup H)).Normal) :
    ∀ Q : Sylow 2 H, (Q : Subgroup H).map H.subtype = S →
      ChapterB.IsMinimalParabolicOver Q ⊤ := by
  intro Q hQ
  rw [ChapterB.isMinimalParabolicOver_iff]
  exact hsource Q hQ

/- The marked-image equality is deliberately an explicit source premise.  It
   is the equality which the marked-action construction has to prove; a mere
   containment is insufficient for relative normality. -/
theorem plusImage_parabolic_normalizer [Finite G] [Finite F]
    (hKinvar : Tv T v ≤ normalizer (K : Set G))
    (hmarkImage :
      ((plusImage K L T z v hL hz (Tv T v)).subgroupOf
        (plusImage K L T z v hL hz K)).map e.toMonoidHom = Atlas.G2.unipotent)
    (i : Fin 2) :
    plusImage K L T z v hL hz (Tv T v) ≤
      normalizer (map (plusImage K L T z v hL hz K).subtype
        (map e.symm.toMonoidHom (parabolicAt i))) := by
  have hs := Subgroup.normalizes_pullback_of_stabilizer_invariant e Atlas.G2.unipotent
    (parabolicAt i) hmarkImage (by
      intro β hβ
      exact parabolic_stable (F := F) β hβ i)
  exact (show plusImage K L T z v hL hz (Tv T v) ≤
      plusImage K L T z v hL hz (Tv T v) ⊓
        normalizer (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) from
      le_inf le_rfl (plusImage_tv_normalizer K L T z v hL hz hKinvar)).trans hs

/- The source residual is invariant once its literal model action has been
   checked.  The premise is an image inclusion in `K`; the conclusion is the
   desired subgroup normalizer in `G`.  The proof uses the actual kernel of
   `modelMap`, hence is valid with the relative two-group kernel. -/
omit [CharP F 2] in
theorem liftedParabolic_normalizer_of_model_action [Finite G] [Finite F]
    (i : Fin 2)
    (hmodel : ∀ t : Tv T v, ∀ x : G,
      x ∈ liftedParabolic K L T z v hL hz e i →
      (t : G) * x * (t : G)⁻¹ ∈ liftedParabolic K L T z v hL hz e i) :
    Tv T v ≤ normalizer
      (liftedParabolic K L T z v hL hz e i : Set G) := by
  apply le_normalizer_iff.mpr
  intro t ht x hx
  exact hmodel ⟨t, ht⟩ x hx

/- This consumer is intentionally thin: the C.1.26 source and the genuine
   ambient SQTK, Fitting and minimal-parabolic hypotheses remain explicit. -/
theorem false_of_constructed_moving_residual [Finite G] {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (P T : Subgroup G) (z v : G)
    (hlocal : residualIn P ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hSK : Tv T v ≤ normalizer (residualIn P : Set G))
    (hm : ¬ residualIn P ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    (hsqtk : IsSQTK 𝒦 (residualIn P ⊔ Tv T v : Subgroup G))
    (hf : generalizedFitting (residualIn P ⊔ Tv T v : Subgroup G) =
      pCore 2 (residualIn P ⊔ Tv T v : Subgroup G))
    (hpar : ∀ S : Sylow 2 (residualIn P ⊔ Tv T v : Subgroup G),
      (S : Subgroup (residualIn P ⊔ Tv T v : Subgroup G)).map
        (residualIn P ⊔ Tv T v).subtype = Tv T v →
      ChapterB.IsMinimalParabolicOver S ⊤)
    [IsQuasisimple (residualIn P ⧸ pCore 2 (residualIn P))]
    (hn : ¬ ChapterC.IsShort (residualIn P)) : False :=
  false_of_moving_local_nonshort choices source T (residualIn P) z v hlocal hSK hm
    h16 hsqtk hf hpar hn

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2

end
