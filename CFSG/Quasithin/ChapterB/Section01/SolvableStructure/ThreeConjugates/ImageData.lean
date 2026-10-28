module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Generation
/-!
# The source cyclic-three configuration in the faithful image

The Sylow subgroup is first restricted to H and then mapped by the actual
surjective action on U. Because its kernel O₂(H) lies in that Sylow subgroup,
an image offender lies in the image Sylow exactly when its original subgroup
lies in the original Sylow. This identifies the two local generated subgroups
and transports the source commutator equality.

The order-three subgroup injects across the two-group kernel. Its image is
subnormal, still has order three, and generates the image group together with
the image Sylow. These are the inputs to the remaining coordinate-recognition
argument, with no factor-identification hypothesis introduced here.

Source: Aschbacher–Smith, B.1.12, printed p. 73 (PDF p. 84).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) [Finite G]

/-- The genuine Sylow subgroup in the faithful image. -/
noncomputable def localImageSylow (K : Subgroup G) (T : Sylow 2 G) :
    Sylow 2 (subspaceActionImage (localRepresentation ρ K (T : Subgroup G))
      (localFixedSpace ρ K (T : Subgroup G))) :=
  (T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)).mapSurjective
    (fixedSpaceActionHom_surjective _ _)

/-- The actual image of K, via its inclusion in H. -/
noncomputable def localImageThree (K T : Subgroup G) :
    Subgroup (subspaceActionImage (localRepresentation ρ K T) (localFixedSpace ρ K T)) :=
  (K.subgroupOf (K ⊔ T)).map (localActionHom ρ K T)

variable [FiniteDimensional (ZMod 2) V]

/-- The local generated image family equals the image of J(T,V). -/
theorem localImageFamily_generatedAtSylow (hf : Function.Injective ρ)
    (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3) :
    generatedBy (localImageFamily ρ K (T : Subgroup G)) (localImageSylow ρ K T) =
      ((localOffenderSubgroup ρ (T : Subgroup G)).subgroupOf (K ⊔ (T : Subgroup G))).map
        (localActionHom ρ K (T : Subgroup G)) := by
  let H := K ⊔ (T : Subgroup G)
  let S := (T : Subgroup G).subgroupOf H
  let f := localActionHom ρ K (T : Subgroup G)
  have hker : f.ker ≤ S := by
    rw [localActionHom_ker ρ hf K (T : Subgroup G) hK hcard T.isPGroup']
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right)
  rw [← localOffenderSubgroup_subgroupOf]
  change generatedBy _ (S.map f) = (localOffenderSubgroup (localRepresentation ρ K (T : Subgroup G)) S).map f
  apply le_antisymm
  · refine iSup_le fun D => iSup_le fun hD => ?_
    obtain ⟨_, A, hA, he⟩ := hD.1
    have he' : A.map f = D := (local_restrictedSubgroup_eq_map ρ K (T : Subgroup G) A).symm.trans he
    have hAS : A ≤ S := by
      have hle := map_le_iff_le_comap.mp (he'.le.trans hD.2)
      simpa only [comap_map_eq_self hker] using hle
    rw [← he']
    exact map_mono (le_iSup_of_le A (le_iSup_of_le ⟨hA, hAS⟩ le_rfl))
  · change (⨆ A, ⨆ (_ : IsBestOffender (localRepresentation ρ K (T : Subgroup G)) A ∧ A ≤ S), A).map f ≤ _
    simp only [Subgroup.map_iSup]
    refine iSup_le fun A => iSup_le fun hA => ?_
    by_cases hb : A.map f = ⊥
    · exact hb.le.trans bot_le
    · exact le_iSup_of_le _ (le_iSup_of_le
        ⟨⟨hb, A, hA.1, local_restrictedSubgroup_eq_map ρ K (T : Subgroup G) A⟩,
          map_mono hA.2⟩ le_rfl)

/-- The exact commutator identity needed for coordinate recognition. -/
theorem localImageThree_commutator (hf : Function.Injective ρ)
    (K : Subgroup G) (T : Sylow 2 G)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hcard : Nat.card K = 3)
    (hcomm : K = ⁅K, localOffenderSubgroup ρ (T : Subgroup G)⁆) :
    localImageThree ρ K (T : Subgroup G) =
      ⁅localImageThree ρ K (T : Subgroup G),
        generatedBy (localImageFamily ρ K (T : Subgroup G)) (localImageSylow ρ K T)⁆ := by
  rw [localImageFamily_generatedAtSylow ρ hf K T hK hcard,
    localImageThree, ← map_commutator, ← local_commutator ρ K (T : Subgroup G) hcomm]

omit [FiniteDimensional (ZMod 2) V] in
/-- The two image subgroups generate the whole faithful action image. -/
theorem localImageThree_sup_sylow (K : Subgroup G) (T : Sylow 2 G) :
    localImageThree ρ K (T : Subgroup G) ⊔ (localImageSylow ρ K T : Subgroup _) = ⊤ := by
  change (K.subgroupOf (K ⊔ (T : Subgroup G))).map (localActionHom ρ K (T : Subgroup G)) ⊔
    ((T : Subgroup G).subgroupOf (K ⊔ (T : Subgroup G))).map (localActionHom ρ K (T : Subgroup G)) = _
  rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  exact (MonoidHom.range_eq_map _).symm.trans (MonoidHom.range_eq_top.mpr
    (fixedSpaceActionHom_surjective _ _))

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Source subnormality descends through the surjection from H. -/
theorem localImageThree_subnormal (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) :
    (localImageThree ρ K T).IsSubnormal :=
  hK.map (fixedSpaceActionHom_surjective _ _)

/-- Coprimality of the kernel preserves the order-three subgroup. -/
theorem localImageThree_card (hf : Function.Injective ρ) (K T : Subgroup G)
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (hT : IsPGroup 2 T) : Nat.card (localImageThree ρ K T) = 3 := by
  let H := K ⊔ T
  let KH := K.subgroupOf H
  let f := localActionHom ρ K T
  have hcard' : Nat.card KH = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).toEquiv).trans hcard
  have h3 : IsPGroup 3 KH := IsPGroup.of_card (n := 1) (by simpa using hcard')
  have h2 : IsPGroup 2 f.ker := (localActionHom_ker ρ hf K T hK hcard hT).symm ▸ pCore_isPGroup
  have hd : Disjoint KH f.ker := h3.disjoint_of_coprime h2 (by decide : Nat.Coprime 3 2)
  have hinj : Function.Injective (f.subgroupMap KH) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    have hfa : f a = 1 := congrArg Subtype.val ha
    exact mem_bot.mp (hd.eq_bot ▸ (show (a : H) ∈ KH ⊓ f.ker from ⟨a.property, hfa⟩))
  exact (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap KH)
    ⟨hinj, f.subgroupMap_surjective KH⟩).toEquiv).symm.trans hcard'

end CFSG.Quasithin.ChapterB.ThreeConjugates
