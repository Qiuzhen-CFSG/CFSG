module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair

/-!
# Transport of the sporadic Sylow-pair action

An isomorphism of ambient groups transports both members of the Sylow pair,
all seven `PairInput` hypotheses, and the actual extending automorphisms.
The induced equivalence of Frattini quotients intertwines these actions.
Pulling back a proper nonzero invariant subgroup therefore transfers the
model's reducibility result to an isomorphic copy, even across universes.

This is transport for the final sporadic paragraph of Aschbacher–Smith,
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
It does not assert any sporadic local-subgroup or automorphism computation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
universe u v
variable {Q : Type u} {G : Type v} [Group Q] [Group G]

private theorem map_frattini (e : Q ≃* G) :
    (frattini Q).map e.toMonoidHom = frattini G := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    exact ⟨e.symm b, frattini_le_comap_frattini_of_surjective
      (φ := e.symm.toMonoidHom) e.symm.surjective hb, e.apply_symm_apply b⟩

/-- The isomorphism induced on Frattini quotients. -/
noncomputable def frattiniEquiv (e : Q ≃* G) :
    (Q ⧸ frattini Q) ≃* (G ⧸ frattini G) :=
  QuotientGroup.congr _ _ e (by exact map_frattini e)

/-- The induced quotient map agrees with the ambient isomorphism on representatives. -/
theorem frattiniEquiv_apply_mk (e : Q ≃* G) (x : Q) :
    frattiniEquiv e (QuotientGroup.mk' (frattini Q) x) =
      QuotientGroup.mk' (frattini G) (e x) := rfl

/-- The Frattini equivalence intertwines transported automorphisms. -/
theorem frattiniEquiv_equivariant (e : Q ≃* G) (a : MulAut Q)
    (x : Q ⧸ frattini Q) :
    frattiniEquiv e (quotientAut (frattini Q) a x) =
      quotientAut (frattini G) (MulAut.congr e a) (frattiniEquiv e x) := by
  induction x using QuotientGroup.induction_on with | H x =>
    change frattiniEquiv e (quotientAut (frattini Q) a (QuotientGroup.mk' _ x)) =
      quotientAut (frattini G) (MulAut.congr e a)
        (frattiniEquiv e (QuotientGroup.mk' _ x))
    simp only [quotientAut_apply_mk, frattiniEquiv_apply_mk]
    congr 1
    change e (a x) = e (a (e.symm (e x)))
    rw [e.symm_apply_apply]

/-- The ambient isomorphism transports the extending automorphism as well. -/
theorem pairAutomizer_map (e : Q ≃* G) (S R : Subgroup Q)
    {a : MulAut R} (ha : a ∈ pairAutomizer S R) :
    MulAut.congr (e.subgroupMap R) a ∈
      pairAutomizer (S.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  obtain ⟨b, hb, hab⟩ := ha
  refine ⟨MulAut.congr e b, ?_, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply]
    constructor
    · rintro ⟨z, hz, he⟩
      have hz' : z = b x := e.injective he
      exact ⟨x, (hb x).mp (hz' ▸ hz), rfl⟩
    · rintro ⟨z, hz, he⟩
      have hz' : z = x := e.injective he
      exact ⟨b x, (hb x).mpr (hz' ▸ hz), rfl⟩
  · intro y
    obtain ⟨x, rfl⟩ := (e.subgroupMap R).surjective y
    change ((e.subgroupMap R) (a ((e.subgroupMap R).symm ((e.subgroupMap R) x))) : G) =
      e (b (e.symm (e (x : Q))))
    rw [MulEquiv.symm_apply_apply, MulEquiv.coe_subgroupMap_apply,
      e.symm_apply_apply, hab]

/-- Pull back the invariant subgroup for each transported two-group. -/
theorem pairReducible_of_map (e : Q ≃* G) (S R : Subgroup Q)
    (h : PairReducible (S.map e.toMonoidHom) (R.map e.toMonoidHom)) :
    PairReducible S R := by
  intro D hD htwo
  let a := MulAut.congr (e.subgroupMap R)
  let D' := D.map a.toMonoidHom
  have hD' : D' ≤ pairAutomizer (S.map e.toMonoidHom) (R.map e.toMonoidHom) := by
    rintro b ⟨c, hc, rfl⟩
    exact pairAutomizer_map e S R (hD hc)
  have htwo' : IsPGroup 2 D' := htwo.map a.toMonoidHom
  obtain ⟨A, hAb, hAt, hA⟩ := h D' hD' htwo'
  let f := frattiniEquiv (e.subgroupMap R)
  refine ⟨A.comap f.toMonoidHom, ?_, ?_, ?_⟩
  · intro hb
    apply hAb
    have hh := congrArg (Subgroup.map f.toMonoidHom) hb
    rw [map_comap_eq_self_of_surjective (f := f.toMonoidHom) f.surjective A, Subgroup.map_bot] at hh
    exact hh
  · intro ht
    apply hAt
    have hh := congrArg (Subgroup.map f.toMonoidHom) ht
    rw [map_comap_eq_self_of_surjective (f := f.toMonoidHom) f.surjective A,
      map_top_of_surjective f.toMonoidHom f.surjective] at hh
    exact hh
  · intro b hb x hx
    change f (quotientAut (frattini R) b x) ∈ A
    rw [frattiniEquiv_equivariant]
    exact hA (a b) ⟨b, hb, rfl⟩ (f x) hx

/-- Transport the Sylow subgroup and every source input, including permutability. -/
theorem pairInput_map [Finite Q] [Finite G] (e : Q ≃* G)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R) :
    PairInput (S.mapSurjective (f := e.toMonoidHom) e.surjective) (R.map e.toMonoidHom) := by
  let _ := h.quasisimple
  refine ⟨IsQuasisimple.of_mulEquiv e, ?_, ?_, ?_,
    h.oddComplement.of_mulEquiv (e.subgroupMap R), ?_, ?_⟩
  · rw [← pCore_map_iso 2 e, h.twoCore, Subgroup.map_bot]
  · intro p hp ho
    rw [← primeRank_congr p e]
    exact h.stronglyQuasithin p hp ho
  · rw [← primeRank_congr 3 e, h.rank]
  · have ht : (⊤ : Subgroup Q).map e.toMonoidHom = ⊤ :=
      map_top_of_surjective _ e.surjective
    rw [← ht, ← map_commutator, h.commutator, ht]
  · have hh := congrArg (Set.image e) h.permutes
    change (e '' (R : Set Q)) * (e '' (S : Set Q)) =
      (e '' (S : Set Q)) * (e '' (R : Set Q))
    simpa only [Set.image_mul] using hh

/-- A local computation on an isomorphic group supplies the original invariant subgroups. -/
theorem pairReducible_of_equiv [Finite Q] [Finite G] (e : Q ≃* G)
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hmodel : ∀ (S' : Sylow 2 G) (R' : Subgroup G),
      PairInput S' R' → PairReducible (S' : Subgroup G) R') :
    PairReducible (S : Subgroup Q) R := by
  exact pairReducible_of_map e S R
    (hmodel (S.mapSurjective (f := e.toMonoidHom) e.surjective)
      (R.map e.toMonoidHom) (pairInput_map e h))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions
