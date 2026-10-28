module

public import Theory.GroupTheory.CentralPChiefFactors

/-!
# Central p-chief factors descend along surjections

Pulling back a normal chief interval along a surjection gives a normal chief
interval containing the kernel. The relative chief quotients are explicitly
isomorphic, so the p-group condition pulls back. Its centrality then descends
by mapping the commutator containment.

This is the quotient transport required in the faithful moved-space reduction
of Aschbacher–Smith, *The Classification of Quasithin Groups*, B.7.2,
printed p. 119 (1 March 2004 manuscript).
-/

@[expose] public section

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The relative quotient of a pulled-back interval is the original relative quotient. -/
noncomputable def chiefComapQuotientEquiv (f : G →* H) (hf : Function.Surjective f)
    (K L : Subgroup H) [K.Normal] :
    (L.comap f) ⧸ (K.comap f).subgroupOf (L.comap f) ≃* L ⧸ K.subgroupOf L := by
  let fL : L.comap f →* L :=
    { toFun := fun x => ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun x y => Subtype.ext (map_mul f (x : G) (y : G)) }
  have hs : Function.Surjective fL := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨⟨x, by change f x ∈ L; rw [hx]; exact y.property⟩, Subtype.ext hx⟩
  let q := (QuotientGroup.mk' (K.subgroupOf L)).comp fL
  have hk : q.ker = (K.comap f).subgroupOf (L.comap f) := by
    ext x
    exact QuotientGroup.eq_one_iff (fL x)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hs))

/-- Every surjective image inherits central p-chief factors, with relative normality. -/
theorem HasCentralPChiefFactors.of_surjective {p : ℕ}
    (h : HasCentralPChiefFactors p G) (f : G →* H) (hf : Function.Surjective f) :
    HasCentralPChiefFactors p H := by
  intro K L hK hL hlt hchief hp
  let := hK
  let := hL
  have hlt' : K.comap f < L.comap f := (comap_lt_comap_of_surjective hf).2 hlt
  have hchief' : ∀ N : Subgroup G, N.Normal → K.comap f ≤ N → N ≤ L.comap f →
      N = K.comap f ∨ N = L.comap f := by
    intro N hN hKN hNL
    have hmapN : (N.map f).Normal := hN.map f hf
    have hlo : K ≤ N.map f := by
      rw [← map_comap_eq_self_of_surjective hf K]
      exact map_mono hKN
    have hhi : N.map f ≤ L := map_le_iff_le_comap.mpr hNL
    have hback : (N.map f).comap f = N := by
      rw [comap_map_eq, sup_eq_left.mpr ((ker_le_comap f K).trans hKN)]
    rcases hchief (N.map f) hmapN hlo hhi with he | he
    · exact Or.inl (hback.symm.trans (congrArg (comap f) he))
    · exact Or.inr (hback.symm.trans (congrArg (comap f) he))
  have hp' := hp.of_equiv (chiefComapQuotientEquiv f hf K L).symm
  have hc := h.commutator_le (K.comap f) (L.comap f) hlt' hchief' hp'
  apply (map_mk_le_center_iff K L).2
  have hm := map_mono (f := f) hc
  rwa [map_commutator, map_top_of_surjective f hf,
    map_comap_eq_self_of_surjective hf L, map_comap_eq_self_of_surjective hf K] at hm
end Subgroup
