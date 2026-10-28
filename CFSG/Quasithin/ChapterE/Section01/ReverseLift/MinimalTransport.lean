module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Kernel
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Intrinsic quotients of minimal supplements

The Frattini argument makes the intersection of the prescribed Sylow subgroup
with the preimage of the image's two-core normal. It is therefore exactly the
two-core of the supplement. This identifies the preimage and image of local tau
and gives an actual isomorphism between the images of `A` modulo the two-cores.
The solvable kernel also gives the canonical radical-quotient isomorphism;
under it both the actor and its local tau have precisely the required images.

These are the common transport steps in the reverse quotient lift, not a
claim that an arbitrary minimal supplement is already an E-member. The odd
commutator and component-orbit conditions still need separate proofs.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
proof of E.1.10(7), printed pp.211--212, using E.1.10(2).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Group H]

private theorem map_twoCore_le (f : G →* H) (hf : Function.Surjective f) :
    (pCore 2 G).map f ≤ pCore 2 H := by
  have hn : ((pCore 2 G).map f).Normal := Normal.map inferInstance f hf
  exact le_sSup ⟨hn, pCore_isPGroup.map f⟩

/-- Tau maps into tau under every surjection; no special kernel hypothesis is needed. -/
theorem map_tau_le_of_surjective (f : G →* H) (hf : Function.Surjective f)
    (T A : Subgroup G) : (tau T A).map f ≤ tau (T.map f) (A.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨mem_map_of_mem f hxT, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_commutatorElement]
  exact map_twoCore_le f hf (mem_map_of_mem f (hc a ha))

variable [Finite G]

/-- The prescribed Sylow meets the preimage of the image two-core in exactly `O₂(K)`. -/
theorem IsMinimalSupplement.inf_preimage_twoCore (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    (T : Subgroup G).subgroupOf K ⊓
      (pCore 2 (K.map (QuotientGroup.mk' Y))).comap
        ((QuotientGroup.mk' Y).subgroupMap K) = pCore 2 K := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  let S : Sylow 2 K := T.subtype h.1.1
  apply le_antisymm
  · exact le_sSup ⟨h.normal_inf_preimage T _ pCore_isPGroup,
      S.isPGroup'.to_le inf_le_left⟩
  · exact le_inf (pCore_isPGroup.le_sylow_of_normal S)
      (map_le_iff_le_comap.mp (map_twoCore_le f
        ((QuotientGroup.mk' Y).subgroupMap_surjective K)))

/-- The two-core of a minimal supplement maps onto the intrinsic two-core of its image. -/
theorem IsMinimalSupplement.map_twoCore (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    (pCore 2 K).map ((QuotientGroup.mk' Y).subgroupMap K) =
      pCore 2 (K.map (QuotientGroup.mk' Y)) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  let S : Sylow 2 K := T.subtype h.1.1
  apply le_antisymm (map_twoCore_le f hf)
  intro x hx
  have hxs : x ∈ (S : Subgroup K).map f :=
    (pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hf)) hx
  obtain ⟨k, hk, rfl⟩ := hxs
  refine ⟨k, ?_, rfl⟩
  rw [← h.inf_preimage_twoCore T]
  exact ⟨hk, hx⟩

/-- The exact local tau preimage identity used in both branches of E.1.10(7). -/
theorem IsMinimalSupplement.tau_eq_preimage (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    tau ((T : Subgroup G).subgroupOf K) (A.subgroupOf K) =
      (T : Subgroup G).subgroupOf K ⊓
        (tau (((T : Subgroup G).subgroupOf K).map
          ((QuotientGroup.mk' Y).subgroupMap K))
          ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K))).comap
            ((QuotientGroup.mk' Y).subgroupMap K) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  let S := (T : Subgroup G).subgroupOf K
  let B := A.subgroupOf K
  let Z := (pCore 2 (K.map (QuotientGroup.mk' Y))).comap f
  have hb : B ≤ S := subgroupOf_mono K hAT
  have hcentral : centralizerModulo S B Z = tau S B :=
    centralizerModulo_eq_tau hb (h.inf_preimage_twoCore T)
  rw [← hcentral]
  ext k
  change k ∈ centralizerModulo S B Z ↔ k ∈ S ∧ f k ∈ tau (S.map f) (B.map f)
  constructor
  · intro hk
    obtain ⟨hk, hc⟩ := mem_centralizerModulo_iff.mp hk
    refine ⟨hk, mem_centralizerModulo_iff.mpr ⟨mem_map_of_mem f hk, ?_⟩⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_commutatorElement]
    exact hc a ha
  · rintro ⟨hk, hc⟩
    obtain ⟨_, hc⟩ := mem_centralizerModulo_iff.mp hc
    refine mem_centralizerModulo_iff.mpr ⟨hk, fun a ha => ?_⟩
    have hh := hc (f a) (mem_map_of_mem f ha)
    rwa [← map_commutatorElement] at hh

/-- The local tau maps onto the local tau of the actual quotient image. -/
theorem IsMinimalSupplement.map_tau (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    (tau ((T : Subgroup G).subgroupOf K) (A.subgroupOf K)).map
        ((QuotientGroup.mk' Y).subgroupMap K) =
      tau (((T : Subgroup G).subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K))
        ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  apply le_antisymm (map_tau_le_of_surjective f
    ((QuotientGroup.mk' Y).subgroupMap_surjective K) _ _)
  intro x hx
  obtain ⟨k, hk, rfl⟩ := tau_le _ _ hx
  refine ⟨k, ?_, rfl⟩
  rw [h.tau_eq_preimage T A hAT]
  exact ⟨hk, hx⟩

/-- The two-core quotient images of any subgroup of the prescribed Sylow are isomorphic. -/
noncomputable def IsMinimalSupplement.twoCoreImageEquiv (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) ≃*
      ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)).map
        (QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y)))) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  let B := A.subgroupOf K
  let u := (QuotientGroup.mk' (pCore 2 K)).subgroupMap B
  let v := ((QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y)))).subgroupMap
    (B.map f)).comp (f.subgroupMap B)
  have hv : Function.Surjective v :=
    ((QuotientGroup.mk' _).subgroupMap_surjective _).comp (f.subgroupMap_surjective B)
  have hk : u.ker = v.ker := by
    ext a
    change u a = 1 ↔ v a = 1
    rw [Subtype.ext_iff, Subtype.ext_iff]
    change QuotientGroup.mk' (pCore 2 K) (a : K) = 1 ↔
      QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y))) (f (a : K)) = 1
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← h.inf_preimage_twoCore T]
    exact ⟨And.right, fun ha => ⟨hAT a.property, ha⟩⟩
  exact (QuotientGroup.quotientKerEquivOfSurjective u
    ((QuotientGroup.mk' _).subgroupMap_surjective B)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective v hv))

/-- The odd-branch rank is preserved exactly under the minimal-supplement quotient. -/
theorem IsMinimalSupplement.rank_twoCore_image (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) =
      Group.rank (((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K)).map
        (QuotientGroup.mk' (pCore 2 (K.map (QuotientGroup.mk' Y))))) :=
  Group.rank_congr (h.twoCoreImageEquiv T A hAT)

/-- The solvable kernel identifies the two intrinsic radical quotients. -/
noncomputable def IsMinimalSupplement.radicalQuotientEquiv (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) :
    K ⧸ solvableRadical K ≃*
      (K.map (QuotientGroup.mk' Y)) ⧸ solvableRadical (K.map (QuotientGroup.mk' Y)) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hk : f.ker = Y.subgroupOf K := by
    ext k
    change (f k = 1) ↔ (k : G) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : G)
  let : Group.IsSolvable f.ker := hk.symm ▸ h.isSolvable_kernel T
  exact solvableRadicalQuotientEquiv f ((QuotientGroup.mk' Y).subgroupMap_surjective K)

/-- The radical-quotient equivalence is induced by the literal map into `G/Y`. -/
theorem IsMinimalSupplement.radicalQuotientEquiv_mk (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (k : K) :
    h.radicalQuotientEquiv T (QuotientGroup.mk' (solvableRadical K) k) =
      QuotientGroup.mk' (solvableRadical (K.map (QuotientGroup.mk' Y)))
        ((QuotientGroup.mk' Y).subgroupMap K k) := rfl

/-- Transport a subgroup image through the canonical radical-quotient equivalence. -/
theorem IsMinimalSupplement.map_radical_quotient_image (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (B : Subgroup K) :
    (B.map (QuotientGroup.mk' (solvableRadical K))).map
        (h.radicalQuotientEquiv T).toMonoidHom =
      (B.map ((QuotientGroup.mk' Y).subgroupMap K)).map
        (QuotientGroup.mk' (solvableRadical (K.map (QuotientGroup.mk' Y)))) := by
  rw [map_map, map_map]
  rfl

/-- The component-branch rank is preserved exactly under this quotient. -/
theorem IsMinimalSupplement.rank_radical_image (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K) (B : Subgroup K) :
    Group.rank (B.map (QuotientGroup.mk' (solvableRadical K))) =
      Group.rank ((B.map ((QuotientGroup.mk' Y).subgroupMap K)).map
        (QuotientGroup.mk' (solvableRadical (K.map (QuotientGroup.mk' Y))))) :=
  Group.rank_congr (((B.map (QuotientGroup.mk' (solvableRadical K))).equivMapOfInjective
    (h.radicalQuotientEquiv T).toMonoidHom (h.radicalQuotientEquiv T).injective).trans
      (MulEquiv.subgroupCongr (h.map_radical_quotient_image T B)))

/-- The local tau actor in E.1.2(E2) transports through the actual radical quotients. -/
theorem IsMinimalSupplement.map_local_tau_radical_image (T : Sylow 2 G)
    {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (A : Subgroup G) (hAT : A ≤ (T : Subgroup G)) :
    ((tau ((T : Subgroup G).subgroupOf K) (A.subgroupOf K)).map
      (QuotientGroup.mk' (solvableRadical K))).map
        (h.radicalQuotientEquiv T).toMonoidHom =
      (tau (((T : Subgroup G).subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K))
        ((A.subgroupOf K).map ((QuotientGroup.mk' Y).subgroupMap K))).map
          (QuotientGroup.mk' (solvableRadical (K.map (QuotientGroup.mk' Y)))) := by
  rw [h.map_radical_quotient_image T, h.map_tau T A hAT]

end CFSG.Quasithin.ChapterE
