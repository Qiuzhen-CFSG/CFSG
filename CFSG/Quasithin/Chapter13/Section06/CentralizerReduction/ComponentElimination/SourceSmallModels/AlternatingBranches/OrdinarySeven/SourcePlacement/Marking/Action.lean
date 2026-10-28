module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ActionKernels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Action

/-!
# The actual plus action in ordinary alternating-block coordinates

Relative normality identifies the actor with KTᵥ. The two-reducedness of W_K
kills O₂(K) in the plus image. Simplicity of the ordinary A₇ quotient and
nontriviality from Y_z then identify K⁺ with that quotient, preserving every
representative. Conjugation on this normal subgroup and Aut(A₇) = S₇ supply
an injective seven-point action. The quotient coordinates are those of the
chosen block-module model.

This constructs the action; it does not assert the Thompson or Baumann
markings. Two-reducedness is retained as an earlier component-module input
from the paragraph preceding 13.6.14, rather than inferred from the ordinary
block predicate. Source: Aschbacher–Smith, combined manuscript of 1 March
2004, printed pp.929 and 932, Lemma 13.6.22.
-/

@[expose] public section
open Subgroup Equiv
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking

variable {G : Type*} [Group G]

/-- In the source branch both factors added to K₋ lie in KTᵥ. -/
theorem plusActor_eq (K L T : Subgroup G) (v : G)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K) :
    plusActor K L T v = K ⊔ Tv T v := by
  have hm : Kminus K T v = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy K (Tv T v))
  rw [plusActor, hm, sup_eq_left.mpr hLv]

/-- The source normalization is relative to the plus actor. -/
theorem component_normal (K L T : Subgroup G) (v : G)
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K) :
    (K.subgroupOf (plusActor K L T v)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (ComponentSelection.K_le_plusActor K L T v)).mpr
    (by rw [plusActor_eq K L T v hn hLv]; exact sup_le K.le_normalizer hn)

/-- The literal K⁺ is normal in the actual plus quotient. -/
theorem component_image_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K) :
    (plusImage K L T z v hL hz K).Normal := by
  let := component_normal K L T v hn hLv
  exact Subgroup.Normal.map inferInstance _ (plusMk_surjective K L T z v hL hz)

/-- Restrict the actual plus projection to the original K. -/
def componentMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    K →* plusImage K L T z v hL hz K :=
  ((plusMk K L T z v hL hz).comp
    (inclusion (ComponentSelection.K_le_plusActor K L T v))).codRestrict _
      (fun k => mem_map.mpr ⟨⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩,
        k.property, rfl⟩)

theorem componentMap_surjective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Surjective (componentMap K L T z v hL hz) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

variable [Finite G]

/-- Two-reducedness of W_K kills the intrinsic two-core in this actual map. -/
theorem component_core_le_kernel (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥) :
    pCore 2 K ≤ (componentMap K L T z v hL hz).ker := by
  let D := plusImage K L T z v hL hz K
  let := component_image_normal K L T z v hL hz hn hLv
  have hd : pCore 2 D = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : D.Normal).isSubnormal, hR]
    exact (MonoidHom.ker_eq_bot_iff D.subtype).mpr D.subtype_injective
  have hm : (pCore 2 K).map (componentMap K L T z v hL hz) ≤ pCore 2 D :=
    le_sSup ⟨Subgroup.Normal.map inferInstance _
      (componentMap_surjective K L T z v hL hz), pCore_isPGroup.map _⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hm.trans hd.le))

/-- The isomorphism from K/O₂(K) to its plus image is the induced original map. -/
noncomputable def componentQuotientEquiv (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    (K ⧸ pCore 2 K) ≃* plusImage K L T z v hL hz K := by
  let f := QuotientGroup.lift (pCore 2 K) (componentMap K L T z v hL hz)
    (component_core_le_kernel K L T z v hL hz hn hLv hR)
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ _
    (componentMap_surjective K L T z v hL hz) _
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by norm_num)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := e.isSimpleGroup
  have hk : f.ker = ⊥ := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      apply plusImage_ne_bot_of_mem_Yz K L T z v hL hz hY
      apply le_bot_iff.mp
      intro x hx
      obtain ⟨y, hy⟩ := hf ⟨x, hx⟩
      have he : f y = 1 := by
        change y ∈ f.ker
        rw [ht]
        exact mem_top y
      exact congrArg Subtype.val (hy.symm.trans he)
  exact MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).mp hk, hf⟩

theorem componentQuotientEquiv_mk (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (k : K) :
    componentQuotientEquiv K L T z v hL hz hn hLv hY hR e
      (QuotientGroup.mk' (pCore 2 K) k) = componentMap K L T z v hL hz k := rfl

omit [Finite G] in
/-- K⁺ and Tᵥ⁺ generate the whole plus quotient. -/
theorem component_sup_two_image (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K) :
    plusImage K L T z v hL hz K ⊔ plusImage K L T z v hL hz (Tv T v) = ⊤ := by
  rw [plusImage, plusImage, ← Subgroup.map_sup,
    ← subgroupOf_sup (ComponentSelection.K_le_plusActor K L T v) le_sup_right,
    ← plusActor_eq K L T v hn hLv, subgroupOf_self,
    map_top_of_surjective _ (plusMk_surjective K L T z v hL hz)]

/-- The source Sylow witness survives the literal plus projection. -/
theorem two_image_sylow (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v) :
    ∃ P : Sylow 2 (Gplus K L T z v hL hz),
      (P : Subgroup _) = plusImage K L T z v hL hz (Tv T v) := by
  have hs := hY.1.2.2.1
  rw [← plusActor_eq K L T v hn hLv] at hs
  obtain ⟨P, hP⟩ := hs
  refine ⟨P.mapSurjective (plusMk_surjective K L T z v hL hz), ?_⟩
  rw [Sylow.coe_mapSurjective, plusImage, ← hP]
  congr 1
  exact (comap_map_eq_self_of_injective (plusActor K L T v).subtype_injective _).symm

omit [Finite G] in
/-- The X_z generation clause descends through the original star-to-plus map.
This supplies the nontrivial Thompson action without adding 13.6.16 as a premise. -/
theorem component_commutator_thompson (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hY : K ∈ Yz L T z v) :
    ⁅plusImage K L T z v hL hz K,
      plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        plusImage K L T z v hL hz K := by
  let J := Stellmacher.elementaryAbelianMaxJ (Tv T v)
  have hJT : J ≤ Tv T v := sSup_le fun _ hA => hA.1
  have hJA : J ≤ plusActor K L T v := hJT.trans le_sup_right
  have hgen := hY.2.2.1.2.2.2
  have hm : Kminus K T v = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy K (Tv T v))
  rw [← starImage_Kminus K T z v hY.1.1, hm] at hgen
  let A := starImage z v (plusActor K L T v)
  have hKA : starImage z v K ≤ A :=
    map_mono (comap_mono (ComponentSelection.K_le_plusActor K L T v))
  have hJA' : starImage z v J ≤ A := map_mono (comap_mono hJA)
  have hi : ⁅(starImage z v K).subgroupOf A, (starImage z v J).subgroupOf A⁆ =
      (starImage z v K).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hKA,
      map_subgroupOf_eq_of_le hJA', hgen]
  have ho := congrArg (Subgroup.map (starToPlus K L T z v hY.1.1 hL hz)) hi
  rw [map_commutator,
    starToPlus_image K L T z v hY.1.1 hL hz K (ComponentSelection.K_le_plusActor K L T v),
    starToPlus_image K L T z v hY.1.1 hL hz J hJA] at ho
  exact ho

omit [Finite G] in
/-- Membership in the literal Y_z rules out a trivial Thompson plus image. -/
theorem thompson_image_ne_bot (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hY : K ∈ Yz L T z v) :
    plusImage K L T z v hL hz (Stellmacher.elementaryAbelianMaxJ (Tv T v)) ≠ ⊥ := by
  intro he
  have hc := component_commutator_thompson K L T z v hL hz hn hY
  rw [he, commutator_bot_right] at hc
  exact plusImage_ne_bot_of_mem_Yz K L T z v hL hz hY hc.symm

/-- A faithful action compatible with any specified actual A₇ quotient coordinates.
The two-group hypothesis comes from the literal Y_z Sylow placement. -/
theorem action_exists (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ φ : Gplus K L T z v hL hz →* Perm (Fin 7), Function.Injective φ ∧
      (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7) ∧
      ∀ k : K,
        φ (plusMk K L T z v hL hz
          ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
            (blockProjection K e k : Perm (Fin 7)) := by
  let := component_image_normal K L T z v hL hz hn hLv
  let a := componentQuotientEquiv K L T z v hL hz hn hLv hY hR e
  let b := a.symm.trans e
  let φ := Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.permutationAction _ b
  have ht : IsPGroup 2 (Tv T v) := (Chapter1.isSylowIn_iff.mp hY.1.2.2.1).1
  refine ⟨φ, Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.permutationAction_injective
    _ b _ ((ht.comap_subtype).map _)
    (component_sup_two_image K L T z v hL hz hn hLv) hR,
    Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.permutationAction_map _ b, ?_⟩
  intro k
  change φ (componentMap K L T z v hL hz k).val = _
  rw [Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.permutationAction_on_subgroup]
  change (e (a.symm (componentMap K L T z v hL hz k))).val = _
  rw [← componentQuotientEquiv_mk K L T z v hL hz hn hLv hY hR e k]
  exact congrArg (fun x => (e x).val) (a.symm_apply_apply _)

/-- Use the quotient coordinates of the actual chosen ordinary-block model. -/
theorem ordinary_action_exists (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) (hLv : Lv L v ≤ K)
    (hY : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hblock : ChapterC.IsAlternatingBlock K 7) :
    ∃ φ : Gplus K L T z v hL hz →* Perm (Fin 7), Function.Injective φ ∧
      (plusImage K L T z v hL hz K).map φ = alternatingGroup (Fin 7) ∧
      ∀ k : K,
        φ (plusMk K L T z v hL hz
          ⟨k, ComponentSelection.K_le_plusActor K L T v k.property⟩) =
            (blockProjection K (ordinaryQuotientEquiv K hblock) k : Perm (Fin 7)) :=
  action_exists K L T z v hL hz hn hLv hY hR (ordinaryQuotientEquiv K hblock)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement.Marking
end
