module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2FullActor
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2FixedResidual
/-!
# The full binary actor of an actual normalized block

The KT action on K/O₂(K) gives a homomorphism into the full group G₂(2).
Its restriction to K has exactly the derived image G₂(2)′, and the original
six-dimensional module coordinates intertwine literal KT conjugation with
this full actor. The action kernel is a two-group inside O₂(KT).
Consequently a pair generating the derived image lifts to generation of K
modulo the original local core. No full-image surjectivity is assumed.

Source: Aschbacher–Smith B.4.6 and 3.3.28, printed pp.88–90 and 601.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.G2BlockAction
open Atlas.G2.LieAutomorphismExtensions
variable {G : Type*} [Group G] {T : Sylow 2 G} {K : Subgroup G}

@[expose] def joinFullActor (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    ↥(K ⊔ (T : Subgroup G)) →* Atlas.G2.Model (ZMod 2) :=
  binaryAutomorphismEquiv.symm.toMonoidHom.comp (joinAction hTK m)

@[simp] theorem joinFullActor_conjugation
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (x : ↥(K ⊔ (T : Subgroup G))) :
    binaryAutomorphismEquiv (joinFullActor hTK m x) = joinAction hTK m x := by
  simp [joinFullActor]

@[simp] theorem joinFullActor_on_block
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) (k : K) :
    joinFullActor hTK m (inclusion le_sup_left k) = (m.actor k).val := by
  change m.g2FullActor (K.normalizerMonoidHom
    (inclusion (sup_le K.le_normalizer hTK) (inclusion le_sup_left k))) = _
  have he : K.normalizerMonoidHom
      (inclusion (sup_le K.le_normalizer hTK) (inclusion le_sup_left k)) =
      MulAut.conj k := by
    apply MulEquiv.ext
    intro l
    rfl
  rw [he, m.g2FullActor_inner]

theorem joinFullActor_block_image
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    (K.subgroupOf (K ⊔ (T : Subgroup G))).map (joinFullActor hTK m) =
      commutator (Atlas.G2.Model (ZMod 2)) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have he : x = inclusion le_sup_left (⟨x.val,hx⟩ : K) := rfl
    rw [he, joinFullActor_on_block]
    exact (m.actor ⟨x.val,hx⟩).property
  · intro x hx
    obtain ⟨k, hk⟩ := m.actor_surjective (⟨x,hx⟩ : Actor)
    refine ⟨inclusion le_sup_left k, k.property, ?_⟩
    rw [joinFullActor_on_block]
    exact congrArg Subtype.val hk

theorem derived_le_joinFullActor_range
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    commutator (Atlas.G2.Model (ZMod 2)) ≤ (joinFullActor hTK m).range := by
  rw [← joinFullActor_block_image hTK m]
  rintro _ ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

theorem joinFullActor_modulePoint
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (x : ↥(K ⊔ (T : Subgroup G))) (u : blockU K) :
    modulePoint m (MulAut.characteristic (blockU K)
      (K.normalizerMonoidHom (inclusion (sup_le K.le_normalizer hTK) x)) u) =
      Atlas.G2.Natural.action (ZMod 2) (joinFullActor hTK m x) (modulePoint m u) :=
  m.g2_moduleIso_characteristic _ u

@[simp] theorem joinFullActor_eq_one_iff
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (x : ↥(K ⊔ (T : Subgroup G))) :
    joinFullActor hTK m x = 1 ↔ joinAction hTK m x = 1 := by
  change binaryAutomorphismEquiv.symm (joinAction hTK m x) = 1 ↔ _
  exact binaryAutomorphismEquiv.symm.map_eq_one_iff

theorem joinFullActor_kernel_isPGroup
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    IsPGroup 2 (joinFullActor hTK m).ker := by
  have he : (joinFullActor hTK m).ker = (joinAction hTK m).ker := by
    ext x
    exact joinFullActor_eq_one_iff hTK m x
  rw [he]
  exact joinAction_kernel_isPGroup hTK m

theorem joinFullActor_kernel_le_core
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction) :
    (joinFullActor hTK m).ker ≤ pCore 2 ↥(K ⊔ (T : Subgroup G)) :=
  le_sSup ⟨inferInstance, joinFullActor_kernel_isPGroup hTK m⟩

theorem mem_core_of_joinFullActor_eq_one
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (x : ↥(K ⊔ (T : Subgroup G))) (hx : joinFullActor hTK m x = 1) :
    (x : G) ∈ (K ⊔ (T : Subgroup G)).pCoreIn 2 :=
  mem_core_of_joinAction_eq_one hTK m x ((joinFullActor_eq_one_iff hTK m x).mp hx)

/-- Derived-image generation lifts through the actual kernel into the
original local core; full-image surjectivity is not needed. -/
theorem joinFullActor_generation_lifts
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (E : Subgroup ↥(K ⊔ (T : Subgroup G)))
    (hgen : commutator (Atlas.G2.Model (ZMod 2)) ≤ E.map (joinFullActor hTK m)) :
    K ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
      E.map (K ⊔ (T : Subgroup G)).subtype := by
  let H := K ⊔ (T : Subgroup G)
  let q := joinFullActor hTK m
  have hh : K.subgroupOf H ≤ E ⊔ q.ker := by
    rw [← comap_map_eq]
    intro k hk
    apply hgen
    rw [← joinFullActor_block_image hTK m]
    exact mem_map_of_mem q hk
  have hl : K.subgroupOf H ≤ pCore 2 H ⊔ E :=
    hh.trans (sup_le le_sup_right ((joinFullActor_kernel_le_core hTK m).trans le_sup_left))
  have hm := map_mono (f := H.subtype) hl
  rw [map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left), Subgroup.map_sup] at hm
  exact hm

/-- A pair of concrete derived-conjugate image generators supplies the
literal generation premise used in the G₂ core-product argument. -/
theorem joinFullActor_two_conjugate_generation
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (m : BlockModuleModel K g2TwoNaturalAction)
    (A : Subgroup ↥(K ⊔ (T : Subgroup G))) (g : Actor)
    (hgen : commutator (Atlas.G2.Model (ZMod 2)) ≤
      A.map (joinFullActor hTK m) ⊔
        (A.map (joinFullActor hTK m)).map (MulAut.conj g.val).toMonoidHom) :
    ∃ k : K, K ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ⊔
      (A.map (K ⊔ (T : Subgroup G)).subtype ⊔
        (A.map (K ⊔ (T : Subgroup G)).subtype).map (MulAut.conj k.val).toMonoidHom) := by
  obtain ⟨k, hk⟩ := m.actor_surjective g
  let H := K ⊔ (T : Subgroup G)
  let x : H := inclusion le_sup_left k
  let q := joinFullActor hTK m
  have hx : q x = g.val := by
    rw [show q x = (m.actor k).val from joinFullActor_on_block hTK m k, hk]
  have he : (A.map (MulAut.conj x).toMonoidHom).map q =
      (A.map q).map (MulAut.conj g.val).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      map_mul, map_inv, hx]
  have hh := joinFullActor_generation_lifts hTK m
    (A ⊔ A.map (MulAut.conj x).toMonoidHom) (by rwa [Subgroup.map_sup, he])
  refine ⟨k, ?_⟩
  rw [Subgroup.map_sup] at hh
  have he' : (A.map (MulAut.conj x).toMonoidHom).map H.subtype =
      (A.map H.subtype).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map, map_map]
    rfl
  rwa [he'] at hh

end CFSG.Quasithin.ChapterC.G2BlockAction
