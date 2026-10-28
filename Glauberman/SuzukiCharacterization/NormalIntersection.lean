module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Theory.GroupTheory.SylowNormalCenterIntersection

/-!
# The central intersection of a normal subgroup

Every nontrivial normal subgroup has even order when the odd core is trivial.
Its intersection with P is a nontrivial normal two-subgroup of P, so it meets
Z(P) nontrivially. Element fusion controlled by N_G(P) makes N ∩ Z(P)
closed under any ambient conjugacy whose endpoint lies in P.

These are the first reductions in Proposition 2.1(ii), p. 80, of Glauberman,
*A Characterization of the Suzuki Groups* (1968), saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Under the trivial odd core, every odd normal subgroup is trivial. -/
public theorem Hypotheses.normal_eq_bot_of_coprime (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) (hN : N.Normal) (hodd : Nat.Coprime 2 (Nat.card N)) : N = ⊥ := by
  apply eq_bot_iff.mpr
  have hle : N ≤ pPrimeCore 2 G := le_sSup ⟨hN, hodd⟩
  rwa [h.oddCore_eq_bot] at hle

/-- A nontrivial normal subgroup has a nonidentity element in the Sylow center. -/
public theorem Hypotheses.exists_ne_one_mem_center_of_normal (P : Sylow 2 G)
    (h : Hypotheses P) (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    ∃ x : P, x ∈ center P ∧ x ≠ 1 ∧ (x : G) ∈ N := by
  apply P.exists_ne_one_mem_center_of_normal N
  by_contra hdvd
  exact hne (h.normal_eq_bot_of_coprime P N inferInstance
    (Nat.prime_two.coprime_iff_not_dvd.mpr hdvd))

omit [Finite G] in
/-- Fusion preserves the central intersection of any normal subgroup. -/
public theorem Hypotheses.normal_center_fusion (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (x y : P) (hxZ : x ∈ center P)
    (hxN : (x : G) ∈ N) (hxy : IsConj (x : G) (y : G)) :
    y ∈ center P ∧ (y : G) ∈ N := by
  obtain ⟨n, hn, he⟩ := h.fusion x x.property y y.property hxy
  let f : MulAut P := (P : Subgroup G).normalizerMonoidHom ⟨n, hn⟩
  have hfy : f x = y := Subtype.ext he
  constructor
  · let hm := (Subgroup.centerCongr f) ⟨x, hxZ⟩
    have hz : f x ∈ center P := hm.property
    rwa [hfy] at hz
  · rw [← he]
    exact (inferInstance : N.Normal).conj_mem x hxN n

/-- The central intersection is nontrivial as an intrinsic subgroup of P. -/
public theorem Hypotheses.normal_center_inf_ne_bot (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) :
    N.subgroupOf (P : Subgroup G) ⊓ center P ≠ ⊥ := by
  obtain ⟨x, hxZ, hx, hxN⟩ := h.exists_ne_one_mem_center_of_normal P N hne
  intro he
  have hm : x ∈ N.subgroupOf (P : Subgroup G) ⊓ center P := ⟨hxN, hxZ⟩
  rw [he, mem_bot] at hm
  exact hx hm

/-- The subgroup N ∩ Z(P), viewed in G. -/
@[expose] public def normalCenterIntersection (P : Sylow 2 G) (N : Subgroup G) : Subgroup G :=
  (N.subgroupOf (P : Subgroup G) ⊓ center P).map (P : Subgroup G).subtype

omit [Finite G] in
/-- The central intersection lies in the given normal subgroup. -/
public theorem normalCenterIntersection_le (P : Sylow 2 G) (N : Subgroup G) :
    normalCenterIntersection P N ≤ N := by
  rintro x ⟨z, hz, rfl⟩
  exact hz.1

omit [Finite G] in
/-- The central intersection lies in P. -/
public theorem normalCenterIntersection_le_sylow (P : Sylow 2 G) (N : Subgroup G) :
    normalCenterIntersection P N ≤ (P : Subgroup G) := by
  rintro x ⟨z, _, rfl⟩
  exact z.property

/-- The ambient central intersection of a nontrivial normal subgroup is nontrivial. -/
public theorem Hypotheses.normalCenterIntersection_ne_bot (P : Sylow 2 G) (h : Hypotheses P)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥) : normalCenterIntersection P N ≠ ⊥ := by
  intro he
  apply h.normal_center_inf_ne_bot P N hne
  exact (Subgroup.map_injective (P : Subgroup G).subtype_injective)
    (he.trans (Subgroup.map_bot _).symm)

/-- Weak closure of N ∩ Z(P): a conjugate contained in P is the same subgroup. -/
public theorem Hypotheses.normalCenterIntersection_weakly_closed (P : Sylow 2 G)
    (h : Hypotheses P) (N : Subgroup G) [N.Normal] (g : G)
    (hg : (normalCenterIntersection P N).map (MulAut.conj g).toMonoidHom ≤
      (P : Subgroup G)) :
    g ∈ normalizer (normalCenterIntersection P N : Set G) := by
  apply mem_normalizer_fintype
  rintro x ⟨z, hz, rfl⟩
  have hxP : g * (z : G) * g⁻¹ ∈ (P : Subgroup G) :=
    hg (mem_map_of_mem _ (mem_map_of_mem _ hz))
  obtain ⟨hxZ, hxN⟩ := h.normal_center_fusion P N z ⟨_, hxP⟩ hz.2 hz.1
    (isConj_iff.mpr ⟨g, rfl⟩)
  exact mem_map.mpr ⟨⟨_, hxP⟩, ⟨hxN, hxZ⟩, rfl⟩

/-- The Sylow normalizer normalizes the central intersection. -/
public theorem Hypotheses.normalizer_le_normalizer_normalCenterIntersection
    (P : Sylow 2 G) (h : Hypotheses P) (N : Subgroup G) [N.Normal] :
    normalizer (P : Set G) ≤ normalizer (normalCenterIntersection P N : Set G) := by
  intro g hg
  apply h.normalCenterIntersection_weakly_closed P N g
  rintro x ⟨z, hz, rfl⟩
  exact (mem_normalizer_iff.mp hg z).mp (normalCenterIntersection_le_sylow P N hz)

/-- If a normal subgroup lies in P, its central intersection is normal in G. -/
public theorem Hypotheses.normalCenterIntersection_normal_of_le (P : Sylow 2 G)
    (h : Hypotheses P) (N : Subgroup G) [N.Normal] (hNP : N ≤ (P : Subgroup G)) :
    (normalCenterIntersection P N).Normal := by
  refine ⟨?_⟩
  intro x hx g
  have hg : g ∈ normalizer (normalCenterIntersection P N : Set G) := by
    apply h.normalCenterIntersection_weakly_closed P N g
    rintro y ⟨z, hz, rfl⟩
    exact hNP ((inferInstance : N.Normal).conj_mem z (normalCenterIntersection_le P N hz) g)
  exact (mem_normalizer_iff.mp hg x).mp hx

end Glauberman.SuzukiCharacterization
