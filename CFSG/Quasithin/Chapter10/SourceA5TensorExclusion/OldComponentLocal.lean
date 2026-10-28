module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponentCenter
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponent
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorLine
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl

/-!
# Local membership of the old residual at the component stabilizer

The original tensor line contains a T-central involution. Tensor non-FF
makes H centralize that involution. Since the line lies in T∩N(L), its
cyclic group lies centrally in O²(H)(T∩N(L)), giving a nontrivial two-core.
Thus the literal old residual belongs to the stabilizer local family as
soon as its A₅ quotient and the source 9.3.2 Sylow clause are supplied.
No containment of the entire two-core of H is needed.

Source: Aschbacher–Smith 9.2.2,9.3.2–4, printed pp.730–733.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}

theorem old_residual_mem_local_at_stabilizer (m : SourceA5TensorModel D e)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))) :
    (pResidual 2 H).map H.subtype ∈
      Chapter1.L G ((T : Subgroup G) ⊓ normalizer (L : Set G)) := by
  let K := (pResidual 2 H).map H.subtype
  let R := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let J := K ⊔ R
  have hJH : J ≤ H := sup_le (map_subtype_le _) (inf_le_left.trans hH.1.1.2)
  have hK := (source_hstar_residual_mem_local_of_a5 hH eK).1
  rw [source_hstar_residual_sup_sylow hH] at hK
  refine ⟨hK.subgroupOf_of_le le_sup_left hJH,hSyl,?_⟩
  obtain ⟨z,hz,hzU,hzT⟩ := m.exists_central_involution_tensorLine
  have hVR : D.fullModule ≤ R := by
    rw [← m.module_eq]
    exact le_inf D.module_le_sylow
      (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hzR : z ∈ R := hVR (m.tensorLine_le_fullModule hzU)
  have hzOmega : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzR.1, hz ▸ pow_orderOf_eq_one z, hzT⟩
  have hzCH : z ∈ centralizer (H : Set G) :=
    (le_centralizer_iff.mp (m.hstar_centralizes_sylowOmega hH)) hzOmega
  have hZH : zpowers z ≤ centralizer (H : Set G) := zpowers_le.mpr hzCH
  have hJZ : J ≤ normalizer (zpowers z : Set G) :=
    (hJH.trans (le_centralizer_iff.mpr hZH)).trans
      (Subgroup.centralizer_le_normalizer (zpowers z : Set G))
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hz]; rfl)
  have hZQ : zpowers z ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hp
    (zpowers_le.mpr (show z ∈ J from mem_sup_right hzR)) hJZ
  intro hbot
  have hz1 : z = 1 := mem_bot.mp (hbot ▸ hZQ (mem_zpowers z))
  simp [hz1] at hz

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
