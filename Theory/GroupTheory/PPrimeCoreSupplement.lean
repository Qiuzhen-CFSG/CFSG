module

public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# Quotients of prime-complement core supplements

If a subgroup M together with the p'-core generates a finite group G, then
the p'-core of M is exactly its intersection with the p'-core of G, and
M/O_p'(M) is isomorphic to G/O_p'(G). The subgroup M need not be normal.

The original quotient map restricts surjectively to M. Its kernel is the
core intersection, of order coprime to p. Apply the coprime-surjection core
identity both to this restriction and to the ambient quotient map. Their
compatibility identifies the core of M with that kernel; the first
isomorphism theorem gives the stated quotient equivalence.

This is the centralizer-supplement reduction at the start of
Alperin--Brauer--Gorenstein II.3 Lemma 2, article page 23. The statement is
independent of Q-groups and applies to every prime.

The final absorption theorem applies this core identity to U intersect M:
if that intersection supplements the core of U, then U intersect core(M)
lies in core(U). This form is used in the relative signalizer factorization
of Kurzweil–Stellmacher 11.2.6.
-/

namespace Subgroup

public theorem quotient_pPrimeCore_equiv_of_sup_eq_top
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (M : Subgroup G) (hM : pPrimeCore p G ⊔ M = ⊤) :
    pPrimeCore p M = (pPrimeCore p G).subgroupOf M ∧
      Nonempty ((M ⧸ pPrimeCore p M) ≃* (G ⧸ pPrimeCore p G)) := by
  let O := pPrimeCore p G
  let q := QuotientGroup.mk' O
  let f : M →* G ⧸ O := q.comp M.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hmap : M.map q = ⊤ := by
      have h := congrArg (fun H : Subgroup G => H.map q) hM
      have hO : (pPrimeCore p G).map q = ⊥ := QuotientGroup.map_mk'_self O
      simpa only [map_sup, hO, bot_sup_eq,
        map_top_of_surjective q (QuotientGroup.mk'_surjective O)] using h
    rw [MonoidHom.range_comp, M.range_subtype, hmap]
  have hqker : q.ker = O := QuotientGroup.ker_mk' O
  have hfker : f.ker = O.subgroupOf M := by
    ext x
    exact QuotientGroup.eq_one_iff (N := O) (x : G)
  have hfc : Nat.Coprime p (Nat.card f.ker) := by
    rw [hfker]
    rw [← Subgroup.card_map_of_injective (K := O.subgroupOf M) M.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
    exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (pPrimeCore_coprime_card (p := p) (G := G))
  have hqc : Nat.Coprime p (Nat.card q.ker) := by
    rw [hqker]
    exact pPrimeCore_coprime_card
  have hcoref := pPrimeCore_comap_eq_of_surjective_coprime p f hf hfc
  have hcoreq := pPrimeCore_comap_eq_of_surjective_coprime p q
    (QuotientGroup.mk'_surjective O) hqc
  have hcoreM : pPrimeCore p M = O.subgroupOf M := by
    rw [← hcoref]
    change (pPrimeCore p (G ⧸ O)).comap (q.comp M.subtype) = O.comap M.subtype
    rw [← Subgroup.comap_comap, hcoreq]
  refine ⟨hcoreM, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq (hcoreM.trans hfker.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- A core supplement absorbs the intersection with the other subgroup's core. -/
public theorem inf_pPrimeCore_map_le_of_supplement
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (U M : Subgroup G)
    (hU : U = (pPrimeCore q U).map U.subtype ⊔ (U ⊓ M)) :
    U ⊓ (pPrimeCore q M).map M.subtype ≤ (pPrimeCore q U).map U.subtype := by
  let V : Subgroup U := M.subgroupOf U
  have hsup : pPrimeCore q U ⊔ V = ⊤ := by
    apply Subgroup.map_injective (f := U.subtype) U.subtype_injective
    rw [Subgroup.map_sup]
    change (pPrimeCore q U).map U.subtype ⊔ (M.subgroupOf U).map U.subtype = _
    rw [Subgroup.subgroupOf_map_subtype, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simpa only [inf_comm] using hU.symm
  have hcore := (Subgroup.quotient_pPrimeCore_equiv_of_sup_eq_top q V hsup).1
  let f : V →* M :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    have hv : x.val.val = y.val.val := congrArg (fun z : M => (z : G)) h
    exact Subtype.ext (Subtype.ext hv)
  let C : Subgroup V := (pPrimeCore q M).comap f
  have hCcop : Nat.Coprime q (Nat.card C) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_comap_dvd_of_injective (pPrimeCore q M) f hf)
      pPrimeCore_coprime_card
  have hCle : C ≤ pPrimeCore q V := le_sSup ⟨inferInstance, hCcop⟩
  intro x hx
  obtain ⟨m, hm, rfl⟩ := hx.2
  let v : V := ⟨⟨m, hx.1⟩, m.property⟩
  have hv : v ∈ C := hm
  have hvcore : v.val ∈ pPrimeCore q U := by
    have hh := hCle hv
    rw [hcore] at hh
    exact hh
  exact ⟨v.val, hvcore, rfl⟩


end Subgroup
