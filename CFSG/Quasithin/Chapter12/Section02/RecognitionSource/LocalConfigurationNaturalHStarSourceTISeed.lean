module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceRestrictionsCore
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The exact central seed for the nonsolvable H-star TI argument

For K=O²(H), define V_Z=⟨(Ω₁(Z(T))∩V)ᴷ⟩ on the original subgroups.
Since H=KT and T centralizes the seed, this is also its H-orbit. It lies
in the reduced omega module V_H and is itself reduced by Sylow inheritance.
In particular the source U=V∩O₂(H) is nontrivial. Residual escape and
NoEscape give C_V(K)=1, so the actual quotient V_Z/C_{V_Z}(K) is nontrivial.

The final containment theorem applies to either proposed TI overmodule
W=U Uʰ or W=U Uˣ Uʰ, once its K-invariance is proved. It preserves the
literal seed and centralizer quotient. Constructing that W and recognizing
its natural SL₂(4) factors remain with qt-d-12213-hstar-natural; no such
representation conclusion is assumed or asserted by these seed results.

Source: Aschbacher–Smith, 12.2.19, printed pp.801–802, using B.2.14, p.78.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}

/-- The exact original seed module V_Z in 12.2.19. -/
def hstarSeedModule (T : Sylow 2 G) (V H : Subgroup G) : Subgroup G :=
  conjugateSpanBy (omegaCenterIn (T : Subgroup G) ⊓ V) ((pResidual 2 H).map H.subtype)

private theorem residual_sup_sylow (hTH : (T : Subgroup G) ≤ H) :
    (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  have ht : (((T.subtype hTH : Sylow 2 H) : Subgroup H)).map H.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTH
  simpa only [Subgroup.map_sup, ht, ← MonoidHom.range_eq_map, range_subtype] using he

omit [Finite G] in
private theorem sylow_normalizes_residual (hTH : (T : Subgroup G) ≤ H) :
    (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) :=
  hTH.trans (H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pResidual 2 H)))

omit [Finite G] in
private theorem omega_centralizes_sylow :
    omegaCenterIn (T : Subgroup G) ≤ centralizer (T : Set G) :=
  fun _ hz => ((mem_omegaCenterIn_iff _ _).mp hz).2.1

/-- Taking the K-orbit or the H-orbit gives exactly the same omega module. -/
theorem chosen_hstar_omega_eq_residual_orbit (hTH : (T : Subgroup G) ≤ H) :
    hstarOmegaModule T H =
      conjugateSpanBy (omegaCenterIn (T : Subgroup G)) ((pResidual 2 H).map H.subtype) := by
  unfold hstarOmegaModule
  conv_lhs => rw [← residual_sup_sylow hTH]
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp omega_centralizes_sylow).trans (Subgroup.centralizer_le_normalizer _))
    (sylow_normalizes_residual hTH)

/-- T centralizes the seed Z∩V, so it adds no conjugates to its K-orbit. -/
theorem chosen_hstar_seed_eq_full_orbit (hTH : (T : Subgroup G) ≤ H) :
    hstarSeedModule T V H = conjugateSpanBy (omegaCenterIn (T : Subgroup G) ⊓ V) H := by
  unfold hstarSeedModule
  conv_rhs => rw [← residual_sup_sylow hTH]
  symm
  exact conjugateSpanBy_sup_of_normalizes_seed _ _ _
    ((le_centralizer_iff.mp (inf_le_left.trans omega_centralizes_sylow)).trans
      (Subgroup.centralizer_le_normalizer _)) (sylow_normalizes_residual hTH)

theorem chosen_hstar_seed_le_omega (hTH : (T : Subgroup G) ≤ H) :
    hstarSeedModule T V H ≤ hstarOmegaModule T H := by
  rw [chosen_hstar_seed_eq_full_orbit hTH]
  exact conjugateSpanBy_mono inf_le_left le_rfl

theorem chosen_hstar_seed_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsElementaryAbelian 2 (hstarSeedModule T V H) := by
  let := chosen_hstar_omega_elementary h hH
  exact IsElementaryAbelian.of_le (chosen_hstar_seed_le_omega hH.1.1.2)

theorem chosen_hstar_seed_le_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    hstarSeedModule T V H ≤ H.pCoreIn 2 :=
  (chosen_hstar_seed_le_omega hH.1.1.2).trans (chosen_hstar_omega_le_core h hH)

/-- The original source seed lies in U=V∩O₂(H), before movement is used. -/
theorem chosen_hstar_central_seed_le_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    omegaCenterIn (T : Subgroup G) ⊓ V ≤ V ⊓ H.pCoreIn 2 :=
  le_inf inf_le_right ((le_conjugateSpanBy _ _).trans (chosen_hstar_seed_le_core h hH))

/-- B.2.14 applies also to the exact smaller seed orbit V_Z. -/
theorem chosen_hstar_seed_reduced
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsPReduced 2 ((hstarSeedModule T V H).subgroupOf H) := by
  let A := omegaCenterIn (T : Subgroup G) ⊓ V
  have hAT : A ≤ (T : Subgroup G) := fun _ ha => ((mem_omegaCenterIn_iff _ _).mp ha.1).1
  have hAH : A ≤ H := hAT.trans hH.1.1.2
  have he : normalClosure (A.subgroupOf H : Set H) = (hstarSeedModule T V H).subgroupOf H := by
    rw [normalClosure_subgroupOf_eq_conjugateSpanBy A H hAH,
      ← chosen_hstar_seed_eq_full_orbit hH.1.1.2]
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let := chosen_hstar_seed_elementary (V := V) h hH
  let : IsMulCommutative (normalClosure (A.subgroupOf H : Set H)) := he.symm ▸ inferInstance
  have hr := isPReduced_normalClosure_of_sylow_central (T.subtype hH.1.1.2)
    (A.subgroupOf H) (show A.subgroupOf H ≤ ((T.subtype hH.1.1.2 : Sylow 2 H) : Subgroup H) from
      comap_mono hAT) (by
        intro a ha t ht
        exact Subtype.ext (omega_centralizes_sylow ha.1 t ht))
  exact he ▸ hr

/-- The actual U used in both nonsolvable TI-pair branches is nontrivial. -/
theorem chosen_hstar_intersection_ne_bot_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    V ⊓ H.pCoreIn 2 ≠ ⊥ := by
  have hi := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (T : Subgroup G)
    D.le_sylow T.isPGroup' (((structural L h).2.2 V D).1) D.ne_bot
  intro he
  apply hi
  apply bot_unique
  rw [inf_comm]
  exact (chosen_hstar_central_seed_le_intersection h hH).trans_eq he

/-- Residual escape makes the exact seed module noncentral. No natural
module structure is assumed in this step. -/
theorem chosen_hstar_seed_not_central_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ hstarSeedModule T V H ≤ centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  have hi := inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V (T : Subgroup G)
    D.le_sylow T.isPGroup' (((structural L h).2.2 V D).1) D.ne_bot
  intro hc
  apply hi
  apply bot_unique
  rw [← chosen_hstar_residual_fixed_eq_bot_at h structural hnone hH]
  exact le_inf inf_le_left ((show V ⊓ omegaCenterIn (T : Subgroup G) ≤ hstarSeedModule T V H from
    fun z hz => le_conjugateSpanBy _ _ ⟨hz.2,hz.1⟩).trans hc)

/-- Any actual K-invariant elementary overmodule of U contains the original V_Z.
This is the literal application used for W=U Uʰ or W=U Uˣ Uʰ in 12.2.19. -/
theorem chosen_hstar_seed_le_overmodule
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (W : Subgroup G) (hUW : V ⊓ H.pCoreIn 2 ≤ W)
    (hKW : (pResidual 2 H).map H.subtype ≤ normalizer (W : Set G)) :
    hstarSeedModule T V H ≤ W :=
  conjugateSpanBy_le ((chosen_hstar_central_seed_le_intersection h hH).trans hUW) hKW

/-- Application to the candidate pair module: its K-action cannot be trivial.
The TI-pair recognition and the construction of this W remain with the
same source-theorem owner qt-d-12213-hstar-natural. -/
theorem chosen_hstar_overmodule_not_central_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (W : Subgroup G) (hUW : V ⊓ H.pCoreIn 2 ≤ W)
    (hKW : (pResidual 2 H).map H.subtype ≤ normalizer (W : Set G)) :
    ¬ W ≤ centralizer ((pResidual 2 H).map H.subtype : Set G) :=
  fun hc => chosen_hstar_seed_not_central_at h D structural hnone hH
    ((chosen_hstar_seed_le_overmodule h hH W hUW hKW).trans hc)

/-- The original quotient V_Z/C_{V_Z}(K) is nontrivial, with its actual
subgroup-of centralizer. Natural SL₂(4) recognition is not asserted here. -/
theorem chosen_hstar_seed_quotient_nontrivial_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    letI := chosen_hstar_seed_elementary (V := V) h hH
    Nontrivial ((hstarSeedModule T V H) ⧸
      (centralizer ((pResidual 2 H).map H.subtype : Set G)).subgroupOf (hstarSeedModule T V H)) := by
  let := chosen_hstar_seed_elementary (V := V) h hH
  apply QuotientGroup.nontrivial_iff.mpr
  intro he
  exact chosen_hstar_seed_not_central_at h D structural hnone hH (subgroupOf_eq_top.mp he)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
