module

public import Theory.GroupTheory.MinimalParabolicResidual
public import Theory.GroupTheory.MinimalSylowSupplementKernel

/-!
# Frattini kernels in minimal parabolics

A normal subgroup N containing O₂(G), whose join with the given Sylow
subgroup is proper, lies in the unique maximal overgroup of that Sylow.
Frattini's argument identifies the Sylow intersection with O₂(G). The image
of N modulo O₂(G) has odd order and no proper supplement containing the
image Sylow; conjugacy of Sylow subgroups puts it in the Frattini subgroup.

Source application: the no-partial-complement condition in Campbell,
*Pushing up in Finite Groups* (1979), Hypothesis (E), printed p.9, for the
minimal parabolic in Aschbacher–Smith C.1.17, printed p.126.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The literal kernel image belongs to the Frattini subgroup of the core quotient. -/
theorem normal_image_le_frattini_of_uniqueMaximal (T : Sylow 2 G)
    (hu : Order.HasUniqueMaximalOver (T : Subgroup G) ⊤)
    (N : Subgroup G) [N.Normal] (hQN : pCore 2 G ≤ N)
    (hproper : N ⊔ (T : Subgroup G) < ⊤) :
    N.map (QuotientGroup.mk' (pCore 2 G)) ≤ frattini (G ⧸ pCore 2 G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M,hM,_⟩ := hu.2
  have hNM : N ≤ M := le_sup_left.trans (hu.le_maximal hM le_sup_right hproper)
  have hTN : (T : Subgroup G) ⊓ N = pCore 2 G := by
    exact le_antisymm (sylow_inf_normal_le_twoCore_of_uniqueMaximal T hu M N
      ⟨hM.1,hM.2.isCoatom⟩ hNM)
      (le_inf (pCore_isPGroup.le_sylow_of_normal T) hQN)
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  let D := N.map q
  let : D.Normal := (inferInstance : N.Normal).map q hq
  obtain ⟨R,hR⟩ := T.exists_subgroupOf_eq_of_normal N
  have hQN' : (pCore 2 G).subgroupOf N = (R : Subgroup N) := by
    rw [← hTN,hR]
    ext x
    exact and_iff_left x.property
  have hDcard : ¬ 2 ∣ Nat.card D := by
    have hc : Nat.card D = (R : Subgroup N).index := by
      rw [← relIndex_ker N q]
      change (QuotientGroup.mk' (pCore 2 G)).ker.relIndex N = _
      rw [QuotientGroup.ker_mk',relIndex,hQN']
    rw [hc]
    exact R.not_dvd_index
  apply (T.mapSurjective hq).normal_le_frattini_of_minimal_supplement D hDcard
  intro L hSL hLD
  have hSL' : (T : Subgroup G) ≤ L.comap q := map_le_iff_le_comap.mp hSL
  have hDN : D.comap q = N := by
    change (N.map q).comap q = N
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hQN]
  have hLN : L.comap q ⊔ N = ⊤ := by
    rw [← hDN,comap_sup_eq q L D hq,hLD,comap_top]
  have hLt : L.comap q = ⊤ := by
    by_contra hn
    have hLM := hu.le_maximal hM hSL' (lt_top_iff_ne_top.mpr hn)
    exact hM.2.ne (top_unique (hLN ▸ sup_le hLM hNM))
  have he := congrArg (Subgroup.map q) hLt
  rwa [map_comap_eq_self_of_surjective hq,map_top_of_surjective q hq] at he

end Theory.GroupTheory
