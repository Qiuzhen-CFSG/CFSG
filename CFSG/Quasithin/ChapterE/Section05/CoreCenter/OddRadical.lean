module

public import CFSG.Quasithin.ChapterE.Section05.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.PCoreFrattiniQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# E.5.1: the Frattini-preimage radical in the odd branch

Write X = K/O₂(K). The structural clause of E.1.2(E1) makes X/O_p(X)
a two-group for an odd prime p. Since O₂(X) is trivial, the odd core is
self-centralizing, and hence F*(X) = O_p(X). Thus the literal radical
`weakClosureOddRadical K` is the preimage of the embedded Φ(O_p(X)).

Its kernel is O₂(K) and its image is a p-group, so it has a normal
Sylow two-subgroup. The Frattini action kernel proves that X/Φ(O_p(X))
has trivial two-core; an explicit quotient isomorphism transfers this to
K/R. Normality of R is intrinsic and is used by both the quotient theorem
and its E.5.1 consumer.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, Definition E.1.2(E1), printed pp.209–210,
and Proposition E.5.1, printed p.242.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE

/-- The Frattini preimage is normal in its own ambient group. -/
public instance weakClosureOddRadical_normal (K : Type*) [Group K] [Finite K] :
    (weakClosureOddRadical K).Normal := by
  unfold weakClosureOddRadical
  infer_instance

private theorem twoClosed_of_odd_image {H Y : Type*} [Group H] [Finite H] [Group Y]
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (f : H →* Y)
    (hker : IsPGroup 2 f.ker) (hY : IsPGroup p Y) : IsTwoClosed H := by
  let S : Sylow 2 H := default
  have hdis : Disjoint ((S : Subgroup H).map f) (⊤ : Subgroup Y) :=
    IsPGroup.disjoint_of_ne 2 p hp.symm _ _ (S.isPGroup'.map f) (hY.to_subgroup ⊤)
  have hm : (S : Subgroup H).map f = ⊥ := by simpa using hdis.eq_bot
  have he : (S : Subgroup H) = f.ker :=
    le_antisymm ((Subgroup.map_eq_bot_iff _).mp hm) (hker.le_sylow_of_normal S)
  refine ⟨S, ?_⟩
  rw [he]
  infer_instance

variable {G : Type*} [Group G] [Finite G] {A K : Subgroup G}

private theorem oddRadical_structure (h : ECaseOdd A K) :
    IsTwoClosed (weakClosureOddRadical K) ∧
      pCore 2 (K ⧸ weakClosureOddRadical K) = ⊥ := by
  obtain ⟨p, hprime, hodd, hquot, _⟩ := h
  let : Fact p.Prime := ⟨hprime⟩
  have hp : p ≠ 2 := by have := hprime.odd_iff.mp hodd; omega
  let X := K ⧸ pCore 2 K
  let P := pCore p X
  let N := (frattini P).map P.subtype
  let π := QuotientGroup.mk' (pCore 2 K)
  let R := weakClosureOddRadical K
  have hX : pCore 2 X = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hc : centralizer (P : Set X) ≤ P :=
    centralizer_pCore_le_of_quotient_isPGroup p 2 hX hquot
  have hF : generalizedFitting X = P := generalizedFitting_eq_pCore_of_selfCentralizing p hc
  have hR : R = N.comap π := by
    change ((frattini (generalizedFitting X)).map (generalizedFitting X).subtype).comap π = _
    rw [hF]
  have hN : IsPGroup p N := (pCore_isPGroup.to_subgroup (frattini P)).map P.subtype
  have hRN : R.map π = N := by
    rw [hR, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  constructor
  · let f := π.subgroupMap R
    have hk : IsPGroup 2 f.ker := by
      rw [ker_subgroupMap, QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    have hi : IsPGroup p (R.map π) := hRN.symm ▸ hN
    exact twoClosed_of_odd_image p hp f hk hi
  · have hNquot : pCore 2 (X ⧸ N) = ⊥ :=
      pCore_quotient_frattini_pCore_eq_bot p 2 hp hc
    let f := (QuotientGroup.mk' N).comp π
    have hf : Function.Surjective f :=
      (QuotientGroup.mk'_surjective N).comp (QuotientGroup.mk'_surjective _)
    have hk : f.ker = R := by
      rw [show f = (QuotientGroup.mk' N).comp π from rfl,
        ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact hR.symm
    let e : K ⧸ R ≃* X ⧸ N :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
    have he := pCore_map_iso 2 e
    rw [hNquot] at he
    exact (map_eq_bot_iff_of_injective _ e.injective).mp he

/-- In E1, the literal Frattini-preimage radical has a normal Sylow two-subgroup. -/
public theorem ECaseOdd.weakClosureOddRadical_twoClosed (h : ECaseOdd A K) :
    IsTwoClosed (weakClosureOddRadical K) := (oddRadical_structure h).1

/-- In E1, the quotient by the literal radical has trivial two-core, using
`weakClosureOddRadical_normal` as its intrinsic normality instance. -/
public theorem ECaseOdd.pCore_quotient_weakClosureOddRadical (h : ECaseOdd A K) :
    pCore 2 (K ⧸ weakClosureOddRadical K) = ⊥ := (oddRadical_structure h).2

end CFSG.Quasithin.ChapterE
