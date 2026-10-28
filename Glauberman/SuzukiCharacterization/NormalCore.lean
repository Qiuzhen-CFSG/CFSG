module

public import Glauberman.SuzukiCharacterization.NormalIntersection
public import Glauberman.SuzukiCharacterization.CentralizerReduction

/-!
# Excluding normal two-subgroups

A normal subgroup inherits the trivial odd core. If it has a normal
two-complement, it is therefore a two-group. For a nontrivial normal subgroup
contained in P, its central intersection W with P is normal in G by fusion.
The normal subgroup C_G(W) has a normal two-complement and contains P;
it must consequently equal P, contrary to the nonnormality hypothesis.

This proves the exclusion of the two-group case in Proposition 2.1(ii),
p. 80, of Glauberman, *A Characterization of the Suzuki Groups* (1968),
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup inherits the trivial odd core. -/
public theorem Hypotheses.normal_oddCore_eq_bot (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] : pPrimeCore 2 N = ⊥ := by
  apply Subgroup.map_injective N.subtype_injective
  rw [Subgroup.map_bot]
  apply eq_bot_iff.mpr
  have hle := pPrimeCore_map_subtype_le_pPrimeCore_of_normal 2 N
  rwa [h.oddCore_eq_bot] at hle

/-- A normal subgroup with a normal two-complement is a two-group. -/
public theorem Hypotheses.normal_isPGroup_of_hasNormalPComplement (P : Sylow 2 G)
    (h : Hypotheses P) (N : Subgroup G) [N.Normal]
    (hcomp : HasNormalPComplement 2 N) : IsPGroup 2 N := by
  have hp := isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 N hcomp
  exact hp.of_equiv ((QuotientGroup.quotientMulEquivOfEq
    (h.normal_oddCore_eq_bot P N)).trans QuotientGroup.quotientBot)

/-- A normal subgroup contained in the specified Sylow subgroup is trivial. -/
public theorem Hypotheses.normal_eq_bot_of_le_sylow (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hNP : N ≤ (P : Subgroup G)) : N = ⊥ := by
  by_contra hne
  let W := normalCenterIntersection P N
  have hWne : W ≠ ⊥ := h.normalCenterIntersection_ne_bot P N hne
  let : W.Normal := h.normalCenterIntersection_normal_of_le P N hNP
  obtain ⟨x, hxW, hxne⟩ := W.bot_or_exists_ne_one.resolve_left hWne
  have hxP : x ∈ (P : Subgroup G) := normalCenterIntersection_le_sylow P N hxW
  have hPC : (P : Subgroup G) ≤ centralizer (W : Set G) := by
    intro p hp
    apply mem_centralizer_iff.mpr
    rintro z ⟨zP, hzP, rfl⟩
    exact (congrArg Subtype.val (mem_center_iff.mp hzP.2 ⟨p, hp⟩)).symm
  have hcomp : HasNormalPComplement 2 (centralizer (W : Set G)) := by
    apply hasNormalPComplement_of_le 2 (L := centralizer ({x} : Set G))
      (centralizer_le (Set.singleton_subset_iff.mpr hxW))
    exact h.centralizer_hasNormalPComplement P x hxP hxne
  have hCp := h.normal_isPGroup_of_hasNormalPComplement P (centralizer (W : Set G)) hcomp
  have he := P.is_maximal' hCp hPC
  exact h.not_normal (he ▸ (inferInstance : (centralizer (W : Set G)).Normal))

/-- There are no nontrivial normal two-subgroups. -/
public theorem Hypotheses.normal_eq_bot_of_isPGroup (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hNp : IsPGroup 2 N) : N = ⊥ :=
  h.normal_eq_bot_of_le_sylow P N (hNp.le_sylow_of_normal P)

/-- The two-core is trivial. -/
public theorem Hypotheses.twoCore_eq_bot (P : Sylow 2 G) (h : Hypotheses P) :
    pCore 2 G = ⊥ :=
  h.normal_eq_bot_of_isPGroup P (pCore 2 G) pCore_isPGroup

/-- Every nontrivial normal subgroup has nonnormal Sylow two-subgroups. -/
public theorem Hypotheses.normal_sylow_not_normal (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) (T : Sylow 2 N) :
    ¬ (T : Subgroup N).Normal := by
  intro hT
  let : (T : Subgroup N).Normal := hT
  let : (T : Subgroup N).Characteristic := Sylow.characteristic_of_normal T hT
  have hmap : (T : Subgroup N).map N.subtype = ⊥ :=
    h.normal_eq_bot_of_isPGroup P _ (T.isPGroup'.map N.subtype)
  have hbot : (T : Subgroup N) = ⊥ :=
    (Subgroup.map_injective N.subtype_injective) (hmap.trans (Subgroup.map_bot _).symm)
  have hcop : Nat.Coprime 2 (Nat.card N) := Nat.prime_two.coprime_iff_not_dvd.mpr
    (by simpa only [hbot, Subgroup.index_bot] using T.not_dvd_index)
  exact hne (h.normal_eq_bot_of_coprime P N inferInstance hcop)

end Glauberman.SuzukiCharacterization
