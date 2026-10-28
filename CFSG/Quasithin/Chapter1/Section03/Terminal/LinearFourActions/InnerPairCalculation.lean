module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.InnerPair
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.InnerPairCalculation.Geometry
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.InnerPairCalculation.Fixer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The inner Sylow-pair invariant in L₄(2)

We prove the intrinsic calculation used in the forced-outer-action step of
Lemma 1.3.9. An actual PSL₄(2) model is transported to GL₄(2), using the
field isomorphism with F₂ and the trivial scalar center. The order 20160
excludes the extraspecial complement of order 27, so R is elementary
abelian of order nine.

For the permuting Sylow pair, the transvection directions of RS form a
proper nonzero subspace preserved by both normalizers. The pointwise fixer
of this subspace in R is nontrivial and proper, by the small-dimensional
linear-group orders. Every inner pair automorphism preserves this fixer.
Since Φ(R) = 1, its image is the required subgroup of R/Φ(R).

The final corollary discharges the intrinsic premise of the existing
ambient reduction, retaining the full LocalInput and Sylow hypothesis.
The shared contract and the parent umbrella are unchanged.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 1.3.9(1), printed p.514, with the local setup of Proposition 1.3.4.
The coefficient-field transport uses the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Support`.
-/

@[expose] public section

open Subgroup BinaryLinear BinaryLinear.OuterCyclic
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.InnerPairCalculation
universe u
variable {Q : Type u} [Group Q]

/-- Transport the specified projective matrix model to its natural binary action. -/
theorem exists_linear_equiv (h : ClassicalGroup.IsPSL Q 4 2) :
    Nonempty (Q ≃* Lin) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact ⟨e.trans ((Atlas.fieldEquivPSL 4 f.symm).trans
    (projectiveEquivLinear (by decide : 0 < 4)))⟩

/-- The actual group order excludes the extraspecial complement of order 27. -/
theorem elementary_nine_of_linear_equiv (e : Q ≃* Lin)
    (R : Subgroup Q) (hR : XiOddQuotient 3 R) :
    IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
  rcases hR with he | ⟨_, hc, _⟩
  · exact he
  · have hd := R.card_subgroup_dvd_card
    rw [hc, Nat.card_congr e.toEquiv, card_linear] at hd
    norm_num at hd

private theorem normalizes_of_extension (R : Subgroup Q) (α : MulAut R) (q : Q)
    (he : ∀ x : R, (α x : Q) = MulAut.conj q x) :
    q ∈ normalizer (R : Set Q) := by
  intro x
  change x ∈ R ↔ MulAut.conj q x ∈ R
  constructor
  · intro hx
    rw [← he ⟨x, hx⟩]
    exact (α ⟨x, hx⟩).property
  · intro hx
    obtain ⟨r, hr⟩ := α.surjective ⟨MulAut.conj q x, hx⟩
    have hrx : (r : Q) = x := (MulAut.conj q).injective
      ((he r).symm.trans (congrArg Subtype.val hr))
    exact hrx ▸ r.property

/-- The canonical subspace fixer is preserved by every inner pair automorphism. -/
theorem invariant_subgroup_of_linear_equiv [Finite Q] (e : Q ≃* Lin)
    (S : Sylow 2 Q) (R : Subgroup Q) (hR : Nat.card R = 9)
    (hperm : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)) :
    ∃ K : Subgroup R, K ≠ ⊥ ∧ K ≠ ⊤ ∧
      ∀ α : MulAut R,
        (∃ q : Q, (∀ x : Q, MulAut.conj q x ∈ S ↔ x ∈ S) ∧
          ∀ x : R, (α x : Q) = MulAut.conj q x) →
        ∀ x ∈ K, α x ∈ K := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let R' := R.map e.toMonoidHom
  let eR : R ≃* R' := e.subgroupMap R
  have hcard : Nat.card R' = 9 := (Nat.card_congr eR.toEquiv).symm.trans hR
  have hperm' : (R' : Set Lin) * (S' : Set Lin) =
      (S' : Set Lin) * (R' : Set Lin) := by
    change ((R.map e.toMonoidHom : Subgroup Lin) : Set Lin) *
      (((S : Subgroup Q).map e.toMonoidHom : Subgroup Lin) : Set Lin) =
      (((S : Subgroup Q).map e.toMonoidHom : Subgroup Lin) : Set Lin) *
      ((R.map e.toMonoidHom : Subgroup Lin) : Set Lin)
    simpa only [coe_map, ← Set.image_mul, Sylow.coe_coe] using congrArg (Set.image e.toMonoidHom) hperm
  obtain ⟨W, hW0, hW1, hRW, hNW⟩ := pair_subspace S' R' hcard hperm'
  let K' := pointwiseFixer R' W
  obtain ⟨hK'b, hK't⟩ := pointwiseFixer_proper_nontrivial R' hcard W hW0 hW1 hRW
  let K := K'.comap eR.toMonoidHom
  refine ⟨K, ?_, ?_, ?_⟩
  · intro hb
    apply hK'b
    apply comap_injective (f := eR.toMonoidHom) eR.surjective
    simpa only [MonoidHom.comap_bot, MonoidHom.ker_eq_bot eR.toMonoidHom eR.injective] using hb
  · intro ht
    apply hK't
    apply comap_injective (f := eR.toMonoidHom) eR.surjective
    simpa only [comap_top] using ht
  · rintro α ⟨q, hqS, hqR⟩ x hx
    have hqNR := normalizes_of_extension R α q hqR
    have hqNS : q ∈ normalizer (S : Set Q) := fun x => (hqS x).symm
    have hqnR : e q ∈ normalizer (R' : Set Lin) := by
      rw [← map_equiv_normalizer_eq R e]
      exact mem_map_of_mem e.toMonoidHom hqNR
    have hqnS : e q ∈ normalizer (S' : Set Lin) := by
      change e q ∈ normalizer (((S : Subgroup Q).map e.toMonoidHom : Subgroup Lin) : Set Lin)
      rw [← map_equiv_normalizer_eq (S : Subgroup Q) e]
      exact mem_map_of_mem e.toMonoidHom hqNS
    have hqW := hNW ⟨hqnR, hqnS⟩
    have hα' (r : R') :
        ((MulAut.congr eR α) r : Lin) = MulAut.conj (e q) r := by
      change e (α (eR.symm r) : Q) = _
      rw [hqR]
      simp [MulAut.conj_apply, eR]
      exact congrArg Subtype.val (eR.apply_symm_apply r)
    have hx' := pointwiseFixer_invariant R' W (MulAut.congr eR α) (e q)
      hqW hα' (r := eR x) hx
    change eR (α (eR.symm (eR x))) ∈ K' at hx'
    change eR (α x) ∈ K'
    simpa only [eR.symm_apply_apply] using hx'


/-- Transport the fixer into the elementary complement’s Frattini quotient. -/
theorem innerPairInvariant_of_linear_equiv [Finite Q] (e : Q ≃* Lin)
    (S : Sylow 2 Q) (R : Subgroup Q) (hR : XiOddQuotient 3 R)
    (hperm : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)) :
    InnerPairInvariant (S : Subgroup Q) R := by
  obtain ⟨he, hc⟩ := elementary_nine_of_linear_equiv e R hR
  let _ := he
  let _ : Fact (IsPGroup 3 R) := ⟨hR.isPGroup⟩
  obtain ⟨K, hKb, hKt, hK⟩ := invariant_subgroup_of_linear_equiv e S R hc hperm
  let π := QuotientGroup.mk' (frattini R)
  have hπ : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    rw [QuotientGroup.ker_mk']
    exact frattini_eq_bot_of_isElementaryAbelian (p := 3)
  refine ⟨K.map π, ?_, ?_, ?_⟩
  · exact fun hb => hKb ((K.map_eq_bot_iff_of_injective hπ).mp hb)
  · intro ht
    apply hKt
    apply map_injective hπ
    rw [ht, map_top_of_surjective π (QuotientGroup.mk'_surjective _)]
  · intro α hα x hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨α r, hK α hα r hr, (quotientAut_apply_mk _ _ _).symm⟩

/-- The intrinsic L₄(2) inner Sylow-pair calculation, with no extra premise. -/
theorem linearFourInnerPairTheorem : LinearFourInnerPairTheorem.{u} := by
  intro Q _ _ hQ S R hR hperm
  obtain ⟨e⟩ := exists_linear_equiv hQ
  exact innerPairInvariant_of_linear_equiv e S R hR hperm

/-- The local irreducibility hypothesis forces a genuinely outer action on L₄(2). -/
theorem forced_outer [Finite Q]
    {T X P H B : Subgroup Q} (h : XiEmbedding.LocalInput 3 T X P H)
    (hT : IsSylowIn 2 T H) (hH : H = B ⊔ T)
    (hXB : X ≤ B) (hTB : T ≤ normalizer (B : Set Q))
    (hmodel : ClassicalGroup.IsPSL (XiQuotient B) 4 2) :
    ¬ T ≤ innerTwoQuotientNormalizer B :=
  forced_outer_of_innerPairTheorem linearFourInnerPairTheorem h hT hH hXB hTB hmodel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.InnerPairCalculation
