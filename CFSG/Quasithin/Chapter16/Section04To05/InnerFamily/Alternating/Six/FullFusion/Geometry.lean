module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.FullFusion.Conjugation
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.FullFusion.Reduction
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryPair
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The two maximal elementary sixteen-groups in the full A₆ case

The genuine conjugation map sends T onto a Sylow subgroup P of Aut(A₆)
with kernel of order two. Every elementary subgroup has order at most
sixteen, since its image has order at most eight. Equality forces it to
contain the kernel and to be the full preimage of its image.

The proved pair of elementary eight-groups in P therefore lifts to A and
Aˢ, for an actual s in T. Normalizers are preimages of the actual natural
S₆ intersection and have order 32. The component Sylow acts by inner
automorphisms, so s lies outside A T_L. This constructs the maximal-order
family and computes the normalizer without assuming a family classification
or any ambient fusion conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
open AlternatingSix.ShadowLocal

section Lift
variable {X : Type*} [Group X] [Finite X] (P : Sylow 2 AutA6) (f : X →* P)

omit [Finite X] in
theorem elementary_image_bound (E : Subgroup X) [IsElementaryAbelian 2 E] :
    Nat.card (E.map f) ≤ 8 := by
  let : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 ((E.map f).map (P : Subgroup AutA6).subtype) :=
    IsElementaryAbelian.map _
  have h := AlternatingSix.ShadowLocal.elementary_card_le_eight
    ((E.map f).map (P : Subgroup AutA6).subtype)
  rwa [card_map_of_injective (P : Subgroup AutA6).subtype_injective] at h

theorem elementary_lift_bound (hK : Nat.card f.ker = 2)
    (E : Subgroup X) [IsElementaryAbelian 2 E] : Nat.card E ≤ 16 := by
  have hI := elementary_image_bound P f E
  have hKI : Nat.card (f.ker.subgroupOf E) ≤ 2 := by
    rw [← card_map_of_injective E.subtype_injective, subgroupOf_map_subtype]
    exact (card_le_of_le inf_le_left).trans hK.le
  have hh := (f.ker.subgroupOf E).card_mul_index
  rw [show (f.ker.subgroupOf E).index = Nat.card (E.map f) from relIndex_ker E f] at hh
  nlinarith

theorem elementary_lift_image (hK : Nat.card f.ker = 2)
    (E : Subgroup X) [IsElementaryAbelian 2 E] (hE : Nat.card E = 16) :
    Nat.card (E.map f) = 8 ∧ f.ker ≤ E := by
  have hI := elementary_image_bound P f E
  have hKI : Nat.card (f.ker.subgroupOf E) ≤ 2 := by
    rw [← card_map_of_injective E.subtype_injective, subgroupOf_map_subtype]
    exact (card_le_of_le inf_le_left).trans hK.le
  have hh := (f.ker.subgroupOf E).card_mul_index
  rw [show (f.ker.subgroupOf E).index = Nat.card (E.map f) from relIndex_ker E f, hE] at hh
  have hIc : Nat.card (E.map f) = 8 := by nlinarith
  have hKc : Nat.card (f.ker ⊓ E : Subgroup X) = 2 := by
    rw [← subgroupOf_map_subtype, card_map_of_injective E.subtype_injective]
    nlinarith
  refine ⟨hIc, ?_⟩
  exact inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left (by rw [hKc, hK]))

theorem elementary_lift_normalizer (hf : Function.Surjective f) (hK : Nat.card f.ker = 2)
    (A : Subgroup X) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) :
    normalizer (A : Set X) = (sylowNatural P).comap f := by
  have hAi := elementary_lift_image P f hK A hA
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map _
  rw [← ElementaryPair.normalizer_elementary_eight P (A.map f) hAi.1,
    comap_normalizer_eq_of_surjective _ hf, comap_map_eq, sup_eq_left.mpr hAi.2]

omit [Finite X] in
private theorem map_conjugate {Y : Type*} [Group Y] (φ : X →* Y) (E : Subgroup X) (s : X) :
    (E.conjBy s).map φ = (E.map φ).conjBy (φ s) := by
  rw [conjBy, conjBy, map_map, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem elementary_lift_pair (hf : Function.Surjective f) (hK : Nat.card f.ker = 2)
    (A : Subgroup X) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) :
    ∃ s : X, A.conjBy s ≠ A ∧
      (∀ E : Subgroup X, IsElementaryAbelian 2 E → Nat.card E = 16 →
        E = A ∨ E = A.conjBy s) ∧
      Nat.card (normalizer (A : Set X)) = 32 := by
  have hAi := elementary_lift_image P f hK A hA
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map _
  obtain ⟨s, hs⟩ := hf (Identification.sylowEquiv P Holomorph.rotation)
  have hpre (E : Subgroup X) (hEK : f.ker ≤ E) : (E.map f).comap f = E := by
    rw [comap_map_eq, sup_eq_left.mpr hEK]
  have hinj (E F : Subgroup X) (hEK : f.ker ≤ E) (hFK : f.ker ≤ F)
      (he : E.map f = F.map f) : E = F := by
    rw [← hpre E hEK, ← hpre F hFK, he]
  have hAsK : f.ker ≤ A.conjBy s := by
    intro x hx
    refine ⟨s⁻¹ * x * s, hAi.2 ?_, ?_⟩
    · change f (s⁻¹ * x * s) = 1
      simp only [map_mul, map_inv, show f x = 1 from hx, mul_one, inv_mul_cancel]
    · simp [MulAut.conj_apply, mul_assoc]
  have hswap := map_conjugate f A s
  rw [hs] at hswap
  have hcases := ElementaryPair.elementary_eight_cases P (A.map f) hAi.1
  have hdistinct : (A.conjBy s).map f ≠ A.map f := by
    rcases hcases with h | h
    · rw [hswap, h, conjBy, ElementaryPair.rotation_conjugates]
      exact (ElementaryPair.zero_ne_one P).symm
    · rw [hswap, h, conjBy, ElementaryPair.rotation_conjugates_one]
      exact ElementaryPair.zero_ne_one P
  refine ⟨s, fun he => hdistinct (congrArg (Subgroup.map f) he), ?_, ?_⟩
  · intro E hEe hEc
    let : IsElementaryAbelian 2 E := hEe
    have hEi := elementary_lift_image P f hK E hEc
    let : IsElementaryAbelian 2 (E.map f) := IsElementaryAbelian.map _
    have hEcases := ElementaryPair.elementary_eight_cases P (E.map f) hEi.1
    rcases hcases with hA0 | hA1 <;> rcases hEcases with hE0 | hE1
    · exact Or.inl (hinj E A hEi.2 hAi.2 (hE0.trans hA0.symm))
    · apply Or.inr (hinj E (A.conjBy s) hEi.2 hAsK ?_)
      rw [hswap, hA0, conjBy, ElementaryPair.rotation_conjugates, hE1]
    · apply Or.inr (hinj E (A.conjBy s) hEi.2 hAsK ?_)
      rw [hswap, hA1, conjBy, ElementaryPair.rotation_conjugates_one, hE0]
    · exact Or.inl (hinj E A hEi.2 hAi.2 (hE1.trans hA1.symm))
  · have hN : normalizer (A : Set X) = (sylowNatural P).comap f := by
      rw [← ElementaryPair.normalizer_elementary_eight P (A.map f) hAi.1,
        comap_normalizer_eq_of_surjective _ hf, hpre A hAi.2]
    have hKN : f.ker ≤ normalizer (A : Set X) := hAi.2.trans A.le_normalizer
    have hcardK : Nat.card (f.ker.subgroupOf (normalizer (A : Set X))) = 2 :=
      (Nat.card_congr (subgroupOfEquivOfLe hKN).toEquiv).trans hK
    have hmapN : (normalizer (A : Set X)).map f = sylowNatural P := by
      rw [hN, map_comap_eq_self_of_surjective hf]
    have hh := (f.ker.subgroupOf (normalizer (A : Set X))).card_mul_index
    rw [show (f.ker.subgroupOf (normalizer (A : Set X))).index =
        Nat.card ((normalizer (A : Set X)).map f) from relIndex_ker _ f,
      hcardK, hmapN, sylowNatural_card] at hh
    exact hh.symm

end Lift

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z r : G}

def actionToSylow (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6))
    (hfull : FullAutomorphismCase e) : T →* imageSylow h e hfull :=
  (sylowConjugation h e).codRestrict (imageSylow h e hfull) (by
    intro t
    exact (imageSylow_eq_range h e hfull).symm.le ⟨t, rfl⟩)

theorem actionToSylow_surjective (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6))
    (hfull : FullAutomorphismCase e) : Function.Surjective (actionToSylow h e hfull) := by
  intro a
  have ha : (a : AutA6) ∈ (sylowConjugation h e).range :=
    (imageSylow_eq_range h e hfull).le a.property
  obtain ⟨t, ht⟩ := ha
  exact ⟨t, Subtype.ext ht⟩

theorem actionToSylow_kernel_card (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    Nat.card (actionToSylow h e hfull).ker = 2 := by
  have hk : (actionToSylow h e hfull).ker = (sylowConjugation h e).ker := by
    ext t
    exact Subtype.ext_iff
  rw [hk, sylowConjugation_kernel,
    ← card_map_of_injective (T : Subgroup G).subtype_injective,
    subgroupOf_map_subtype, inf_comm, ← commutingSylow, hTC, Nat.card_zpowers, h.involution]

theorem full_sylow_pair (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    ∃ s ∈ (T : Subgroup G),
      (elementary M).conjBy s ≠ elementary M ∧
      (∀ E : Subgroup G, E ≤ T → IsElementaryAbelian 2 E → Nat.card E = 16 →
        E = elementary M ∨ E = (elementary M).conjBy s) ∧
      Nat.card ↥((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 32 := by
  let A := (elementary M).subgroupOf (T : Subgroup G)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAT
  have hAc : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans (elementary_card M)
  obtain ⟨s, hne, hfamily, hNc⟩ := elementary_lift_pair (imageSylow h e hfull)
    (actionToSylow h e hfull) (actionToSylow_surjective h e hfull)
    (actionToSylow_kernel_card h e hfull hTC) A hAc
  have hmapA : A.map (T : Subgroup G).subtype = elementary M := map_subgroupOf_eq_of_le hAT
  have hconj : (A.conjBy s).map (T : Subgroup G).subtype = (elementary M).conjBy (s : G) := by
    rw [map_conjugate, hmapA]
    rfl
  refine ⟨s, s.property, ?_, ?_, ?_⟩
  · intro he
    apply hne
    apply map_injective (f := (T : Subgroup G).subtype) Subtype.val_injective
    rw [hconj, hmapA, he]
  · intro E hET hEe hEc
    let : IsElementaryAbelian 2 E := hEe
    let : IsElementaryAbelian 2 (E.subgroupOf (T : Subgroup G)) := IsElementaryAbelian.subgroupOf hET
    have hEC : Nat.card (E.subgroupOf (T : Subgroup G)) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv).trans hEc
    rcases hfamily (E.subgroupOf (T : Subgroup G)) inferInstance hEC with he | he
    · left
      simpa only [map_subgroupOf_eq_of_le hET, hmapA] using congrArg (Subgroup.map (T : Subgroup G).subtype) he
    · right
      simpa only [map_subgroupOf_eq_of_le hET, hconj] using congrArg (Subgroup.map (T : Subgroup G).subtype) he
  · rw [← subgroupOf_normalizer_eq hAT] at hNc
    rw [← card_map_of_injective (T : Subgroup G).subtype_injective,
      subgroupOf_map_subtype, inf_comm] at hNc
    exact hNc

theorem full_elementary_card_bound (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) (E : Subgroup G) (hET : E ≤ T)
    [IsElementaryAbelian 2 E] : Nat.card E ≤ 16 := by
  let : IsElementaryAbelian 2 (E.subgroupOf (T : Subgroup G)) := IsElementaryAbelian.subgroupOf hET
  have hb := elementary_lift_bound (imageSylow h e hfull) (actionToSylow h e hfull)
    (actionToSylow_kernel_card h e hfull hTC) (E.subgroupOf (T : Subgroup G))
  rwa [Nat.card_congr (subgroupOfEquivOfLe hET).toEquiv] at hb

theorem full_maximal_iff (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) (E : Subgroup G) :
    E ∈ Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) ↔
      E ≤ T ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 16 := by
  constructor
  · rintro ⟨hET, hEe, hmax⟩
    let : IsElementaryAbelian 2 E := hEe
    have hlo := hmax (elementary M) hAT inferInstance
    rw [elementary_card] at hlo
    exact ⟨hET, hEe, le_antisymm (full_elementary_card_bound h e hfull hTC E hET) hlo⟩
  · rintro ⟨hET, hEe, hEc⟩
    refine ⟨hET, hEe, ?_⟩
    intro B hBT hBe
    let : IsElementaryAbelian 2 B := hBe
    rw [hEc]
    exact full_elementary_card_bound h e hfull hTC B hBT

theorem componentSylow_le_normalizer (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    componentSylow T L ≤ normalizer (elementary M : Set G) := by
  let A := (elementary M).subgroupOf (T : Subgroup G)
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAT
  have hAc : Nat.card A = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAT).toEquiv).trans (elementary_card M)
  have hN := elementary_lift_normalizer (imageSylow h e hfull) (actionToSylow h e hfull)
    (actionToSylow_surjective h e hfull) (actionToSylow_kernel_card h e hfull hTC) A hAc
  intro t ht
  have htI : sylowConjugation h e ⟨t, ht.1⟩ = MulAut.conj (e ⟨t, ht.2⟩) := by
    apply MulEquiv.ext
    intro a
    obtain ⟨a, rfl⟩ := e.surjective a
    simp only [sylowConjugation, normalizerConjugation, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change e (L.normalizerMonoidHom (inclusion h.sylow_normalizes ⟨t, ht.1⟩) a) =
      e ⟨t, ht.2⟩ * e a * (e ⟨t, ht.2⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have htN : (⟨t, ht.1⟩ : T) ∈ normalizer (A : Set T) := by
    rw [hN]
    change sylowConjugation h e ⟨t, ht.1⟩ ∈ natural
    rw [htI]
    exact inner_le_natural ⟨e ⟨t, ht.2⟩, rfl⟩
  rw [← subgroupOf_normalizer_eq hAT] at htN
  exact htN

theorem full_sylow_geometry (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    ∃ s ∈ (T : Subgroup G), s ∉ elementary M ⊔ componentSylow T L ∧
      (elementary M).conjBy s ≠ elementary M ∧
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
        {elementary M, (elementary M).conjBy s} ∧
      Nat.card ↥((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 32 := by
  obtain ⟨s, hs, hne, hpair, hN⟩ := full_sylow_pair h e M hAT hfull hTC
  have hsout : s ∉ elementary M ⊔ componentSylow T L := by
    intro hsA
    exact hne (mem_normalizer_iff_map_conj_eq.mp
      ((sup_le (elementary M).le_normalizer
        (componentSylow_le_normalizer h e M hAT hfull hTC)) hsA))
  refine ⟨s, hs, hsout, hne, ?_, hN⟩
  ext E
  rw [full_maximal_iff h e M hAT hfull hTC]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hET, hEe, hEc⟩
    exact hpair E hET hEe hEc
  · rintro (rfl | rfl)
    · exact ⟨hAT, inferInstance, elementary_card M⟩
    · refine ⟨?_, IsElementaryAbelian.map _, ?_⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hs (hAT ha))
          ((T : Subgroup G).inv_mem hs)
      · rw [conjBy, card_map_of_injective (MulAut.conj s).injective, elementary_card]

end CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
