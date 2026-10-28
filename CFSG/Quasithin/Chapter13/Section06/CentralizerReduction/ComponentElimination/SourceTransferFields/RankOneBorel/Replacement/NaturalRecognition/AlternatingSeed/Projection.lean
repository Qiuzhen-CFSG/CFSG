module

public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.ParabolicProjection

/-!
# The original A₅ component projection in 13.6.15

Two-perfectness of Lᵥ kills its outer action on the actual normal K⁺. The
resulting inner projection respects the literal Tᵥ conjugation. Its nonzero
image has cubic quotient by its two-core and is normalized by the original
component Sylow intersection. The concrete A₅ calculation therefore marks
its range as the full A₄ Borel by an inner conjugate of the given coordinates.

This supplies the actual projection and Borel marking, without assuming an
image identity. The supported-transposition argument must still identify
Lᵥ⁺ itself with this projection before applying the Borel-module obstruction.
Source: Aschbacher–Smith, 13.6.15, printed p.930 (PDF p.947).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection SourceContainment.LinearThree
variable {G : Type*} [Group G]

private theorem component_conj_injective {C : Type*} [Group C]
    (e : C ≃* alternatingGroup (Fin 5)) : Function.Injective (MulAut.conj : C →* MulAut C) := by
  intro x y h
  apply e.injective
  apply MulAut.conj_injective_of_center_eq_bot (alternatingGroup.center_eq_bot (by simp))
  rw [← MulAut.congr_conj e x, ← MulAut.congr_conj e y, h]

/-- The component projection is constructed from its original conjugation action. -/
theorem exists_component_projection [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 5)) :
    ∃ f : Lv L v →* plusImage K L T z v hL hz K,
      ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
        (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
          residualPlusMap K L T z v hL hz l * k *
            (residualPlusMap K L T z v hL hz l)⁻¹ := by
  let N := plusImage K L T z v hL hz K
  let : N.Normal := plus_component_normal K L T z v hL hz hK hn
  let a : Lv L v →* MulAut N :=
    (MulAut.conjNormal : Gplus K L T z v hL hz →* MulAut N).comp
      (residualPlusMap K L T z v hL hz)
  obtain ⟨f, hf⟩ := AlternatingFiveProjection.exists_inner_lift
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)) a e
  refine ⟨f, fun l k => ?_⟩
  exact congrArg (fun b : Lv L v →* MulAut N => ((b l k : N) : Gplus K L T z v hL hz)) hf

theorem projection_equivariant (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 5))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (t : Tv T v) (l : Lv L v) :
    (f (conjugationAction (Lv L v) (Tv T v) hL t l) : Gplus K L T z v hL hz) =
      plusMk K L T z v hL hz (inclusion le_sup_right t) * f l *
        (plusMk K L T z v hL hz (inclusion le_sup_right t))⁻¹ := by
  let N := plusImage K L T z v hL hz K
  let q := residualPlusMap K L T z v hL hz
  let a := plusMk K L T z v hL hz (inclusion le_sup_right t)
  have hN := plus_component_normal K L T z v hL hz hK hn
  let b : N := ⟨a * f l * a⁻¹, hN.conj_mem (f l) (f l).property a⟩
  have hq : q (conjugationAction (Lv L v) (Tv T v) hL t l) = a * q l * a⁻¹ := by
    let ta : plusActor K L T v := ⟨t, (show Tv T v ≤ plusActor K L T v from le_sup_right) t.property⟩
    let la : plusActor K L T v := ⟨l,
      (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left) l.property⟩
    calc
      _ = plusMk K L T z v hL hz (ta * la * ta⁻¹) := rfl
      _ = _ := by rw [map_mul, map_mul, map_inv]; rfl
  have he : f (conjugationAction (Lv L v) (Tv T v) hL t l) = b := by
    apply component_conj_injective e
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    have hk : a⁻¹ * k * a ∈ N := by
      simpa only [inv_inv] using hN.conj_mem k k.property a⁻¹
    have hh := hf l ⟨a⁻¹ * k * a, hk⟩
    change (f l : Gplus K L T z v hL hz) * (a⁻¹ * k * a) * (f l : Gplus K L T z v hL hz)⁻¹ =
      q l * (a⁻¹ * k * a) * (q l)⁻¹ at hh
    change (f (conjugationAction (Lv L v) (Tv T v) hL t l) : Gplus K L T z v hL hz) * k *
      (f (conjugationAction (Lv L v) (Tv T v) hL t l) : Gplus K L T z v hL hz)⁻¹ =
      (a * f l * a⁻¹) * k * (a * f l * a⁻¹)⁻¹
    rw [hf]
    change q (conjugationAction (Lv L v) (Tv T v) hL t l) * k *
      (q (conjugationAction (Lv L v) (Tv T v) hL t l))⁻¹ = _
    rw [hq]
    calc
      _ = a * (q l * (a⁻¹ * k * a) * (q l)⁻¹) * a⁻¹ := by group
      _ = a * ((f l : Gplus K L T z v hL hz) * (a⁻¹ * k * a) *
          (f l : Gplus K L T z v hL hz)⁻¹) * a⁻¹ := by rw [hh]
      _ = _ := by group
  exact congrArg Subtype.val he

/-- The ambient range of the projection is normalized by the literal T_v+
image. This is the invariance needed for the parabolic recognition. -/
theorem projection_range_normalized (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 5))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹) :
    plusImage K L T z v hL hz (Tv T v) ≤
      normalizer (f.range.map (plusImage K L T z v hL hz K).subtype : Set _) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨t, ht, rfl⟩ _ ⟨k, ⟨l, rfl⟩, rfl⟩
  have h := projection_equivariant K L T z v hL hz hK hn e f hf ⟨t, ht⟩ l
  change plusMk K L T z v hL hz t * f l * (plusMk K L T z v hL hz t)⁻¹ ∈ _
  change (f (conjugationAction (Lv L v) (Tv T v) hL ⟨t, ht⟩ l) :
    Gplus K L T z v hL hz) = plusMk K L T z v hL hz t * f l *
      (plusMk K L T z v hL hz t)⁻¹ at h
  rw [← h]
  exact mem_map.mpr ⟨_, ⟨_, rfl⟩, rfl⟩

theorem componentSylow_normalizes_projection (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 5))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹) :
    (componentSylowMap K L T z v hL hz).range ≤ normalizer (f.range : Set (plusImage K L T z v hL hz K)) := by
  rintro _ ⟨s, rfl⟩
  have ha := projection_range_normalized K L T z v hL hz hK hn e f hf
  have hs : (componentSylowMap K L T z v hL hz s : Gplus K L T z v hL hz) ∈
      plusImage K L T z v hL hz (Tv T v) :=
    ⟨⟨s, (show Tv T v ≤ plusActor K L T v from le_sup_right) s.property.1⟩, s.property.1, rfl⟩
  have hh := le_normalizer_comap (H := f.range.map
      (plusImage K L T z v hL hz K).subtype)
    (plusImage K L T z v hL hz K).subtype
    (show componentSylowMap K L T z v hL hz s ∈
      (normalizer (f.range.map (plusImage K L T z v hL hz K).subtype : Set _)).comap
        (plusImage K L T z v hL hz K).subtype from ha hs)
  rwa [comap_map_eq_self_of_injective (plusImage K L T z v hL hz K).subtype_injective] at hh


/-- The projected residual has the literal A₄ range after an inner change of marking. -/
theorem exists_projected_borel [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 5))
    (hc : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3)
    (hcomm : ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥) :
    ∃ f : Lv L v →* plusImage K L T z v hL hz K,
      (∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
        (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
          residualPlusMap K L T z v hL hz l * k *
            (residualPlusMap K L T z v hL hz l)⁻¹) ∧
      ∃ g : alternatingGroup (Fin 5),
        f.range.map (e.trans (MulAut.conj g)).toMonoidHom =
          BinaryPermutation.AlternatingFiveBorel.B := by
  obtain ⟨f,hf⟩ := exists_component_projection K L T z v hL hz hK hn e
  have hne := projection_range_ne_bot K L T z v hL hz f hf hcomm
  let A := f.range.map e.toMonoidHom
  obtain ⟨S,hS⟩ := exists_componentSylow K L T z v hL hz hK hn
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hnS : (S : Subgroup (plusImage K L T z v hL hz K)) ≤ normalizer (f.range : Set _) := by
    rw [hS]
    exact componentSylow_normalizes_projection K L T z v hL hz hK hn e f hf
  have hnR : (R : Subgroup (alternatingGroup (Fin 5))) ≤ normalizer (A : Set _) :=
    (map_mono (f := e.toMonoidHom) hnS).trans (le_normalizer_map _)
  let F := e.subgroupMap f.range
  have hpA : IsPPerfect 2 A := (projection_range_twoPerfect K L T z v hL hz f).of_surjective
    F.toMonoidHom F.surjective
  let q := QuotientGroup.congr (pCore 2 f.range) (pCore 2 A) F (pCore_map_iso 2 F)
  have hcA : Nat.card (A ⧸ pCore 2 A) = 3 :=
    (Nat.card_congr q.toEquiv).symm.trans (residual_image_core_quotient_card L v hc f hne)
  have hA : A ≠ ⊥ := fun hb => hne ((f.range.map_eq_bot_iff_of_injective e.injective).mp hb)
  have h5 : ∀ d ∈ A, d^5=1 → d=1 := by
    intro d hd hd5
    have h := AlternatingFiveProjection.no_five_of_core_quotient_three hcA
      (⟨d,hd⟩ : A) (Subtype.ext hd5)
    exact congrArg Subtype.val h
  obtain ⟨g,hg⟩ := AlternatingFiveProjection.conjugate_eq_borel R A hA hpA h5 hnR
  refine ⟨f,hf,g,?_⟩
  change (f.range.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hg
  rwa [map_map] at hg

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
