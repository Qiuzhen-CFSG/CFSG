module

public import Theory.GroupTheory.CentralPChiefCore
public import Theory.GroupTheory.CentralPChiefFactorsQuotient
public import FeitThompson.ChiefFactors.Core

/-!
# Chief factors above a core and cores of surjective images

The conditions below quantify over actual ambient-normal chief intervals
above a specified subgroup. In particular the condition above O_p(G) says
that every p-chief factor in the terminal part of a chief series through
O_p(G) is central (or, in the stronger version, that none is a p-group).
It does not assume anything about the core of an image.

A surjection killing the specified subgroup pulls back each chief interval
of its image to such an interval. The relative chief quotients are identified
by `chiefComapQuotientEquiv`. For a p-perfect image the central-chief-factor
coprime-action theorem makes its p-core central. Under the stronger condition,
a minimal normal subgroup of a hypothetical nontrivial core is impossible.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.8(2) and the proof of A.4.11, printed pp.59–61.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- All p-chief intervals above N are central. Both endpoints are normal in G. -/
def HasCentralPChiefFactorsAbove (p : ℕ) (N : Subgroup G) : Prop :=
  ∀ (K L : Subgroup G) (_ : K.Normal) (_ : L.Normal), N ≤ K → K < L →
    (∀ D : Subgroup G, D.Normal → K ≤ D → D ≤ L → D = K ∨ D = L) →
    IsPGroup p (L ⧸ K.subgroupOf L) →
    L.map (QuotientGroup.mk' K) ≤ center (G ⧸ K)

/-- There are no p-chief intervals above N, including central intervals. -/
def HasNoPChiefFactorsAbove (p : ℕ) (N : Subgroup G) : Prop :=
  ∀ (K L : Subgroup G) (_ : K.Normal) (_ : L.Normal), N ≤ K → K < L →
    (∀ D : Subgroup G, D.Normal → K ≤ D → D ≤ L → D = K ∨ D = L) →
    ¬ IsPGroup p (L ⧸ K.subgroupOf L)

/-- The global central-chief hypothesis implies the condition above any subgroup. -/
theorem HasCentralPChiefFactors.above {p : ℕ}
    (h : HasCentralPChiefFactors p G) (N : Subgroup G) :
    HasCentralPChiefFactorsAbove p N := by
  intro K L hK hL _ hlt hchief hp
  exact h K L hK hL hlt hchief hp

/-- Pullback preserves actual chief intervals under a surjection. -/
theorem isChiefFactor_comap_of_surjective (f : G →* H) (hf : Function.Surjective f)
    {K L : Subgroup H} (hc : IsChiefFactor K L) :
    IsChiefFactor (K.comap f) (L.comap f) := by
  let := hc.normal_K
  let := hc.normal_H
  refine ⟨inferInstance, inferInstance, (comap_lt_comap_of_surjective hf).2 hc.lt, ?_⟩
  intro D hD hKD hDL
  have hlo : K ≤ D.map f := by
    rw [← map_comap_eq_self_of_surjective hf K]
    exact map_mono hKD
  have hhi : D.map f ≤ L := map_le_iff_le_comap.mpr hDL
  have hback : (D.map f).comap f = D := by
    rw [comap_map_eq, sup_eq_left.mpr ((ker_le_comap f K).trans hKD)]
  rcases hc.is_maximal (D.map f) (hD.map f hf) hlo hhi with he | he
  · exact Or.inl (hback.symm.trans (congrArg (comap f) he))
  · exact Or.inr (hback.symm.trans (congrArg (comap f) he))

/-- Killing N makes every chief factor of the image come from an interval above N. -/
theorem HasCentralPChiefFactorsAbove.of_surjective {p : ℕ} {N : Subgroup G}
    (h : HasCentralPChiefFactorsAbove p N) (f : G →* H) (hf : Function.Surjective f)
    (hN : N ≤ f.ker) : HasCentralPChiefFactors p H := by
  intro K L hK hL hlt hchief hp
  let := hK
  let := hL
  have hc := isChiefFactor_comap_of_surjective f hf
    (show IsChiefFactor K L from ⟨hK, hL, hlt, hchief⟩)
  have hc' := h (K.comap f) (L.comap f) hc.normal_K hc.normal_H
    (hN.trans (ker_le_comap f K)) hc.lt hc.is_maximal
    (hp.of_equiv (chiefComapQuotientEquiv f hf K L).symm)
  have hm := map_mono (f := f) ((map_mk_le_center_iff _ _).mp hc')
  apply (map_mk_le_center_iff K L).2
  rwa [map_commutator, map_top_of_surjective f hf,
    map_comap_eq_self_of_surjective hf L, map_comap_eq_self_of_surjective hf K] at hm

/-- The stronger chief-factor condition also descends when N is killed. -/
theorem HasNoPChiefFactorsAbove.of_surjective {p : ℕ} {N : Subgroup G}
    (h : HasNoPChiefFactorsAbove p N) (f : G →* H) (hf : Function.Surjective f)
    (hN : N ≤ f.ker) : HasNoPChiefFactorsAbove p (⊥ : Subgroup H) := by
  intro K L hK hL _ hlt hchief hp
  let := hK
  let := hL
  have hc := isChiefFactor_comap_of_surjective f hf
    (show IsChiefFactor K L from ⟨hK, hL, hlt, hchief⟩)
  exact h (K.comap f) (L.comap f) hc.normal_K hc.normal_H
    (hN.trans (ker_le_comap f K)) hc.lt hc.is_maximal
    (hp.of_equiv (chiefComapQuotientEquiv f hf K L).symm)

/-- With no p-chief factors a finite group has trivial p-core. -/
theorem HasNoPChiefFactorsAbove.pCore_eq_bot [Finite G] {p : ℕ}
    (h : HasNoPChiefFactorsAbove p (⊥ : Subgroup G)) : pCore p G = ⊥ := by
  by_contra hn
  obtain ⟨L, hL, hLP, hne, hmin⟩ :=
    exists_minimal_normal_le (pCore p G) inferInstance hn
  let := hL
  apply h ⊥ L inferInstance hL le_rfl (bot_lt_iff_ne_bot.mpr hne)
    (fun D hD _ hDL => ?_)
    ((pCore_isPGroup.to_le hLP).to_quotient ((⊥ : Subgroup G).subgroupOf L))
  by_cases he : D = ⊥
  · exact Or.inl he
  · exact Or.inr (hmin D hD hDL he)

/-- Chief factors above the original p-core control the core of every image
which kills that core. The residual and core conventions are distinct. -/
theorem pCore_image_le_center_of_chiefFactors [Finite H] {p : ℕ} [Fact p.Prime]
    (hG : IsPPerfect p G) (hchief : HasCentralPChiefFactorsAbove p (pCore p G))
    (f : G →* H) (hf : Function.Surjective f) (hkill : pCore p G ≤ f.ker) :
    pCore p H ≤ center H :=
  pCore_le_center_of_centralPChiefFactors p
    ((pResidual_eq_top_iff p H).mpr (hG.of_surjective f hf))
    (hchief.of_surjective f hf hkill)

/-- If every p-chief factor lies below the original p-core, the image core
is trivial; this conclusion does not require p-perfectness. -/
theorem pCore_image_eq_bot_of_chiefFactors [Finite H] {p : ℕ}
    (hchief : HasNoPChiefFactorsAbove p (pCore p G))
    (f : G →* H) (hf : Function.Surjective f) (hkill : pCore p G ≤ f.ker) :
    pCore p H = ⊥ :=
  (hchief.of_surjective f hf hkill).pCore_eq_bot
/-- Surjections preserve chief intervals containing the kernel. -/
theorem isChiefFactor_map_of_surjective (f : G →* H) (hf : Function.Surjective f)
    {K L : Subgroup G} (hc : IsChiefFactor K L) (hk : f.ker ≤ K) :
    IsChiefFactor (K.map f) (L.map f) := by
  let := hc.normal_K
  let := hc.normal_H
  have hbackK : (K.map f).comap f = K := by rw [comap_map_eq, sup_eq_left.mpr hk]
  have hbackL : (L.map f).comap f = L := by
    rw [comap_map_eq, sup_eq_left.mpr (hk.trans hc.lt.le)]
  refine ⟨hc.normal_K.map f hf, hc.normal_H.map f hf,
    lt_of_le_of_ne (map_mono hc.lt.le) ?_, ?_⟩
  · intro he
    exact hc.lt.ne (hbackK.symm.trans ((congrArg (comap f) he).trans hbackL))
  · intro D hD hKD hDL
    have hlo : K ≤ D.comap f := map_le_iff_le_comap.mp hKD
    have hhi : D.comap f ≤ L := (comap_mono hDL).trans hbackL.le
    rcases hc.is_maximal (D.comap f) (hD.comap f) hlo hhi with he | he
    · exact Or.inl ((map_comap_eq_self_of_surjective hf D).symm.trans (congrArg (map f) he))
    · exact Or.inr ((map_comap_eq_self_of_surjective hf D).symm.trans (congrArg (map f) he))

/-- The interval formulation above N is exactly central p-chief factors
of G/N; no core-centrality conclusion occurs in either hypothesis. -/
theorem hasCentralPChiefFactorsAbove_iff_quotient {p : ℕ} (N : Subgroup G) [N.Normal] :
    HasCentralPChiefFactorsAbove p N ↔ HasCentralPChiefFactors p (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  constructor
  · intro h
    exact h.of_surjective q hq (by rw [QuotientGroup.ker_mk'])
  · intro h K L hK hL hNK hlt hchief hp
    let := hK
    let := hL
    have hk : q.ker ≤ K := by rwa [QuotientGroup.ker_mk']
    have hc := isChiefFactor_map_of_surjective q hq
      (show IsChiefFactor K L from ⟨hK, hL, hlt, hchief⟩) hk
    let := hc.normal_K
    let := hc.normal_H
    have hbackK : (K.map q).comap q = K := by rw [comap_map_eq, sup_eq_left.mpr hk]
    have hbackL : (L.map q).comap q = L := by
      rw [comap_map_eq, sup_eq_left.mpr (hk.trans hlt.le)]
    let e := MulEquiv.subgroupCongr hbackL
    have heK : (((K.map q).comap q).subgroupOf ((L.map q).comap q)).map
        e.toMonoidHom = K.subgroupOf L := by
      ext k
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hbackK.le hy
      · intro hkK
        exact ⟨e.symm k, hbackK.ge hkK, e.apply_symm_apply k⟩
    let eQ := QuotientGroup.congr _ _ e heK
    have hp' := (hp.of_equiv eQ.symm).of_equiv
      (chiefComapQuotientEquiv q hq (K.map q) (L.map q))
    have he := h.commutator_le (K.map q) (L.map q) hc.lt hc.is_maximal hp'
    apply (map_mk_le_center_iff K L).mpr
    rw [← hbackK, ← map_le_iff_le_comap, map_commutator, map_top_of_surjective q hq]
    exact he
end Subgroup
