module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.Transport
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The Sylow pair used by the three-rank sieve

For a Sylow two-subgroup S of a component quotient Q and an odd complement
R, `pairAutomizer S R` consists of actual automorphisms of R which extend
to automorphisms of Q preserving S. The action of N_T(P) lands in this group.
Consequently, reducibility of every two-subgroup of the pair automizer
contradicts the intrinsic irreducibility hypothesis. Cyclicity of the pair
automizer also implies cyclicity of the original Aut_T(P).

`PairInput` records only the local data supplied before examining the
complete Theorem C catalogue. `pairInput_of_sylow` constructs it using the
explicit Sylow hypothesis, relative normality, and quotient transport.
The elementary-plane lemmas convert local order calculations into the actual
isomorphism required by the source. No family exclusion or classification
conclusion is assumed by the input record or proved by this module.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree
universe u
variable {Q : Type u} [Group Q]

/-- Automorphisms of R extending to automorphisms of Q that preserve S. -/
def pairAutomizer (S R : Subgroup Q) : Subgroup (MulAut R) where
  carrier a := ∃ b : MulAut Q, (∀ x, b x ∈ S ↔ x ∈ S) ∧
    ∀ x : R, (a x : Q) = b x
  one_mem' := ⟨1, fun _ => Iff.rfl, fun _ => rfl⟩
  mul_mem' := by
    rintro a c ⟨b, hb, he⟩ ⟨d, hd, hf⟩
    refine ⟨b * d, fun x => (hb (d x)).trans (hd x), fun x => ?_⟩
    change (a (c x) : Q) = b (d x)
    rw [he, hf]
  inv_mem' := by
    rintro a ⟨b, hb, he⟩
    refine ⟨b⁻¹, fun x => ?_, fun x => ?_⟩
    · simpa using (hb (b⁻¹ x)).symm
    · apply b.injective
      rw [← he]
      simp

/-- Every two-subgroup of the pair automizer preserves a proper nonzero
subgroup of the Frattini quotient. This is the local action exclusion needed
by the source; the invariant subgroup may depend on the acting two-group. -/
def PairReducible (S R : Subgroup Q) : Prop :=
  ∀ D : Subgroup (MulAut R), D ≤ pairAutomizer S R → IsPGroup 2 D →
    ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ D, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A

/-- A common invariant subgroup is one way to exclude all two-group actions. -/
theorem pairReducible_of_invariant (S R : Subgroup Q)
    (h : ∃ A : Subgroup (R ⧸ frattini R), A ≠ ⊥ ∧ A ≠ ⊤ ∧
      ∀ b ∈ pairAutomizer S R, ∀ x ∈ A, quotientAut (frattini R) b x ∈ A) :
    PairReducible S R := by
  obtain ⟨A, hAb, hAt, hA⟩ := h
  exact fun D hD _ => ⟨A, hAb, hAt, fun b hb => hA b (hD hb)⟩

/-- Cardinality gives coordinates for an elementary abelian complement. -/
theorem plane_of_elementary_card [Finite Q] {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p Q] (hcard : Nat.card Q = p ^ 2) :
    Nonempty (Q ≃* Plane p) := by
  classical
  have hpow : p ^ Module.finrank (ZMod p) (Additive Q) = p ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive Q)
    change Nat.card Q = _ at hsize
    simpa only [Nat.card_zmod, hcard] using hsize.symm
  have hdim : Module.finrank (ZMod p) (Additive Q) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt hpow
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive Q) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

/-- Eliminating the extraspecial order suffices to obtain the required plane. -/
theorem plane_of_odd_complement_card [Finite Q] {p : ℕ} [Fact p.Prime]
    (h : XiOddQuotient p Q) (hcard : Nat.card Q ≠ p ^ 3) :
    Nonempty (Q ≃* Plane p) := by
  rcases h with ⟨he, hc⟩ | ⟨_, hc, _⟩
  · let _ := he
    exact plane_of_elementary_card hc
  · exact (hcard hc).elim

variable {G : Type u} [Group G]

private theorem componentAction_maps_two_intersection {T L : Subgroup G}
    (hTL : T ≤ normalizer L) (t : T) {a : XiQuotient L}
    (ha : a ∈ quotientImage L T) :
    componentAction hTL t a ∈ quotientImage L T := by
  obtain ⟨x, hx, rfl⟩ := ha
  refine ⟨L.normalizerMonoidHom (inclusion hTL t) x, ?_, ?_⟩
  · change (t : G) * (x : G) * (t : G)⁻¹ ∈ T
    exact T.mul_mem (T.mul_mem t.property hx) (T.inv_mem t.property)
  · exact (quotientAut_apply_mk _ _ _).symm

theorem componentAction_preserves_two_intersection {T L : Subgroup G}
    (hTL : T ≤ normalizer L) (t : T) (a : XiQuotient L) :
    componentAction hTL t a ∈ quotientImage L T ↔ a ∈ quotientImage L T := by
  constructor
  · intro ha
    have hh := componentAction_maps_two_intersection hTL t⁻¹ ha
    simpa using hh
  · exact componentAction_maps_two_intersection hTL t

theorem normalizerAction_mem_pairAutomizer {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) (hTL : T ≤ normalizer L)
    (s : (T ⊓ normalizer P : Subgroup G)) :
    normalizerAction h hPL s ∈ pairAutomizer (quotientImage L T) (quotientImage L P) :=
  ⟨componentAction hTL ⟨s, s.property.1⟩,
    componentAction_preserves_two_intersection hTL _, normalizerAction_coe h hPL hTL s⟩

theorem not_pairReducible {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) (hTL : T ≤ normalizer L) :
    ¬ PairReducible (quotientImage L T) (quotientImage L P) := by
  intro hred
  let f := normalizerAction h hPL
  have hle : f.range ≤ pairAutomizer (quotientImage L T) (quotientImage L P) := by
    rintro b ⟨s, rfl⟩
    exact normalizerAction_mem_pairAutomizer h hPL hTL s
  have htwo : IsPGroup 2 f.range :=
    (h.two_group.to_le inf_le_left).of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨A, hAb, hAt, hA⟩ := hred f.range hle htwo
  exact (component_normalizer_irreducible h hPL A (fun s =>
    hA _ ⟨s, rfl⟩)).elim hAb hAt

theorem automizer_cyclic_of_pairAutomizer {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L) (hTL : T ≤ normalizer L)
    (hc : IsCyclic (pairAutomizer (quotientImage L T) (quotientImage L P))) :
    IsCyclic (automizer T P) := by
  let _ := hc
  let e := MulAut.congr (complementEquiv h hPL)
  let f : automizer T P →* pairAutomizer (quotientImage L T) (quotientImage L P) :=
    (e.toMonoidHom.comp (automizer T P).subtype).codRestrict _ (by
      intro a
      obtain ⟨s, hs⟩ := a.property
      change e a.val ∈ pairAutomizer (quotientImage L T) (quotientImage L P)
      rw [← hs]
      exact normalizerAction_mem_pairAutomizer h hPL hTL s)
  exact isCyclic_of_injective f (fun a b hab => Subtype.ext
    (e.injective (congrArg Subtype.val hab)))

/-- The local data supplied before consulting the complete Theorem C catalogue.
No irreducibility or classification conclusion is included. -/
structure PairInput (S : Sylow 2 Q) (R : Subgroup Q) : Prop where
  quasisimple : IsQuasisimple Q
  twoCore : pCore 2 Q = ⊥
  stronglyQuasithin : IsStronglyQuasithin Q
  rank : primeRank 3 Q = 2
  oddComplement : XiOddQuotient 3 R
  commutator : ⁅(⊤ : Subgroup Q), R⁆ = ⊤
  permutes : (R : Set Q) * (S : Set Q) = (S : Set Q) * (R : Set Q)

theorem component_quotient_commutator {P L : Subgroup G} (hPL : P ≤ L)
    (hcomm : ⁅L, P⁆ = L) :
    ⁅(⊤ : Subgroup (XiQuotient L)), quotientImage L P⁆ = ⊤ := by
  have hc : ⁅(⊤ : Subgroup L), P.subgroupOf L⁆ = ⊤ := by
    apply map_injective L.subtype_injective
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype,
      map_subgroupOf_eq_of_le hPL, hcomm]
  let q := QuotientGroup.mk' (pCore 2 L)
  have ht : (⊤ : Subgroup L).map q = ⊤ :=
    map_top_of_surjective q (QuotientGroup.mk'_surjective _)
  change ⁅(⊤ : Subgroup (XiQuotient L)), (P.subgroupOf L).map q⁆ = ⊤
  rw [← ht, ← map_commutator, hc]

theorem pairInput_of_sylow [Finite G] {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L) :
    ∃ S : Sylow 2 (XiQuotient L),
      (S : Subgroup (XiQuotient L)) = quotientImage L T ∧
      PairInput S (quotientImage L P) := by
  obtain ⟨S, hS⟩ := component_quotient_sylow hT hLH hLn
  refine ⟨S, hS, hq, pCore_quotient_pCore_eq_bot 2,
    (component_quotient_sqtk hH hLH).stronglyQuasithin,
    (component_quotient_rank h hH.stronglyQuasithin hLH hPL).2,
    h.odd_complement.of_mulEquiv (complementEquiv h hPL),
    component_quotient_commutator hPL hcomm, ?_⟩
  simpa only [← hS, Sylow.coe_coe] using component_quotient_permute h hPL

/-- A concrete elementary-plane identification descends back to the original complement. -/
theorem plane_of_quotient_plane {p : ℕ} {T X P H L : Subgroup G}
    (h : LocalInput p T X P H) (hPL : P ≤ L)
    (he : Nonempty (quotientImage L P ≃* Plane p)) : Nonempty (P ≃* Plane p) :=
  he.map fun e => (complementEquiv h hPL).trans e

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree
