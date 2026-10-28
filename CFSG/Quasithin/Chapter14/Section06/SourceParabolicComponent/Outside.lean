module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent
public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# The selected parabolic component escapes the original module normalizer

The precise component–Sylow supplement supplied by F.6.18 is enough:
K T_I is either I or has index three in I. If K lay in I∩M, prime index
would force I∩M=K T_I. Its two-residual would then lie in K. But K is
perfect and so centralizes the normal four-group V, contradicting the
already proved fact that L_I escapes M_c, which contains C_G(V).

The same selected K is used throughout. The component–Sylow supplement
remains an explicit earlier-source premise; no bound is inferred from
the weaker opposite-parabolic supplement alone.

Source: Aschbacher–Smith, F.6.18 and 14.6.10(5), printed pp.309–310,1029.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_sup_le_normal (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) (hp : IsPGroup 2 S) :
    (pResidual 2 (P ⊔ S : Subgroup G)).map (P ⊔ S).subtype ≤ P := by
  let J := P ⊔ S
  let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hq : IsPGroup 2 (J ⧸ P.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top (P.subgroupOf J) (S.subgroupOf J)
      hp.comap_subtype (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  have hr : pResidual 2 J ≤ P.subgroupOf J := sInf_le ⟨inferInstance,hq⟩
  rintro x ⟨a,ha,rfl⟩
  exact hr ha

omit [Finite G] in
private theorem index_three_intermediate_eq {J M I : Subgroup G}
    (hJM : J ≤ M) (hMI : M ≤ I) (hproper : ¬ I ≤ M)
    (hindex : J.relIndex I = 3) : J = M := by
  have hd : M.relIndex I ∣ 3 := hindex ▸ relIndex_dvd_of_le_left I hJM
  have hMIindex : M.relIndex I = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact (hproper (relIndex_eq_one.mp h)).elim
    · exact h
  have hm := relIndex_mul_relIndex J M I hJM hMI
  rw [hindex,hMIindex] at hm
  exact le_antisymm hJM (relIndex_eq_one.mp (by omega : J.relIndex M = 1))

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal

/-- The same original component is outside I∩M once F.6.18 supplies its
component–Sylow supplement or its exceptional index-three alternative. -/
theorem source_parabolic_component_outside_of_sylow_supplement
    (I : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (K : Subgroup I) (hK : K.IsCComponent) [K.Normal]
    (hsupp : K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I) = I ∨
      (K.map I.subtype ⊔ ((T : Subgroup G) ⊓ I)).relIndex I = 3) :
    ¬ K.map I.subtype ≤ I ⊓ M := by
  let KG := K.map I.subtype
  let S := (T : Subgroup G) ⊓ I
  let LI := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hLIout := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).2.2.2
  intro hKM
  have hKM' : KG ≤ M := hKM.trans inf_le_right
  have hSM : S ≤ I ⊓ M := le_inf inf_le_right (inf_le_left.trans hM.1.2)
  have hJMI : KG ⊔ S ≤ I ⊓ M := sup_le hKM hSM
  have hMI : KG ⊔ S = I ⊓ M := by
    rcases hsupp with hs | hs
    · exact (hI.1.2.2.2 ((hs ▸ hJMI).trans inf_le_right)).elim
    · exact index_three_intermediate_eq hJMI inf_le_left
        (fun hh => hI.1.2.2.2 (hh.trans inf_le_right)) hs
  have hNK : I ≤ normalizer (KG : Set G) := by
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le K)).mp
    change (KG.subgroupOf I).Normal
    rw [show KG.subgroupOf I = K from comap_map_eq_self_of_injective I.subtype_injective K]
    infer_instance
  have hLIKG : LI ≤ KG := by
    have hr := embedded_pResidual_mono 2
      (show sourceResidual M Mc ⊓ I ≤ I ⊓ M from
        le_inf inf_le_right (inf_le_left.trans (sourceResidual_le M Mc)))
    rw [←hMI] at hr
    exact hr.trans (residual_sup_le_normal KG S (inf_le_right.trans hNK)
      (T.isPGroup'.to_le inf_le_left))
  let V := localModule T M
  let : Group.IsPerfect K := hK.perfect
  let : Group.IsPerfect KG := Group.IsPerfect.map I.subtype
  let : Group.IsPerfect (KG.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKM').symm.toMonoidHom)
    (subgroupOfEquivOfLe hKM').symm.surjective
  let : (V.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hVM : V ≤ M := localModule_le T hM.1.2
  have hc := le_centralizer_of_isPerfect_of_card_le_four (KG.subgroupOf M)
    (V.subgroupOf M) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVM).toEquiv,hcard])
  have hKC : KG ≤ centralizer (V : Set G) := by
    intro k hk v hv
    exact congrArg M.subtype (hc (show (⟨k,hKM' hk⟩ : M) ∈ KG.subgroupOf M from hk)
      ⟨v,hVM hv⟩ hv)
  exact hLIout (hLIKG.trans (hKC.trans
    (InitialSource.localModule_centralizer_le_partner T M hunique)))

end CFSG.Quasithin.Chapter14.Section06
