module

public import Theory.Representation.BinaryOffender.ElementaryConjugateBudget
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Transport of elementary inner conjugate budgets

A group isomorphism transports an elementary automorphism subgroup and each
of its inner conjugators. Naturality of conjugation identifies the generated
subgroups, and the induced subgroup equivalence preserves binary rank.
In particular arbitrary automorphism conjugacy of actor representatives
preserves a budget whose conjugators must lie in the original group.

The concrete consumer is the PSL₂(11) calculation for the alternative
Guralnick–Malle Proposition 4.1 / Aschbacher–Smith K.2 exclusion.
-/

public section

namespace Representation.BinaryOffender
open Subgroup
variable {S T : Type*} [Group S] [Group T]

theorem rank_map_equiv (A : Subgroup S) (e : S ≃* T) :
    rank (A.map e.toMonoidHom) = rank A := by
  unfold rank
  rw [Nat.card_congr (A.equivMapOfInjective e.toMonoidHom e.injective).toEquiv]

theorem IsElementaryTwo.map_equiv {A : Subgroup S} (hA : IsElementaryTwo A)
    (e : S ≃* T) : IsElementaryTwo (A.map e.toMonoidHom) := by
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map e.toMonoidHom⟩
  intro hb
  apply hA.1
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ (⊥ : Subgroup T) := hb ▸ (mem_map_of_mem e.toMonoidHom hx)
  exact e.injective ((show e x = 1 from he).trans e.map_one.symm)

/-- Both the actor and its conjugators transport through a group isomorphism. -/
theorem inner_conjugate_span_map (e : S ≃* T) (A : Subgroup (MulAut S))
    {n : ℕ} (c : Fin n → S)
    (hc : (MulAut.conj : S →* MulAut S).range ≤
      ⨆ i, A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom) :
    (MulAut.conj : T →* MulAut T).range ≤
      ⨆ i, (A.map (MulAut.congr e).toMonoidHom).map
        (MulAut.conj (MulAut.conj (e (c i)))).toMonoidHom := by
  let f := (MulAut.congr e).toMonoidHom
  have hm (i : Fin n) :
      (A.map (MulAut.conj (MulAut.conj (c i))).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (MulAut.conj (e (c i)))).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro a
    change f (MulAut.conj (c i) * a * (MulAut.conj (c i))⁻¹) =
      MulAut.conj (e (c i)) * f a * (MulAut.conj (e (c i)))⁻¹
    simp only [map_mul, map_inv, f, MulEquiv.coe_toMonoidHom, MulAut.congr_conj]
  rintro _ ⟨x,rfl⟩
  have hx := mem_map_of_mem f (hc (show MulAut.conj (e.symm x) ∈
    (MulAut.conj : S →* MulAut S).range from ⟨e.symm x,rfl⟩))
  rw [Subgroup.map_iSup] at hx
  simp only [hm] at hx
  simpa only [f, MulEquiv.coe_toMonoidHom, MulAut.congr_conj, e.apply_symm_apply] using hx

theorem ElementaryInnerConjugateBudget.map {b : ℕ}
    (h : ElementaryInnerConjugateBudget S b) (e : S ≃* T) :
    ElementaryInnerConjugateBudget T b := by
  intro B hB
  let f := MulAut.congr e
  let A := B.map f.symm.toMonoidHom
  have hA : IsElementaryTwo A := hB.map_equiv f.symm
  have hAB : A.map f.toMonoidHom = B := (map_symm_eq_iff_map_eq A (H := B) (e := f)).mp rfl
  obtain ⟨n,c,hn,hc⟩ := h A hA
  refine ⟨n, fun i => e (c i), ?_, ?_⟩
  · simpa only [A, rank_map_equiv] using hn
  · have hm := inner_conjugate_span_map e A c hc
    change (MulAut.conj : T →* MulAut T).range ≤
      ⨆ i, (A.map f.toMonoidHom).map
        (MulAut.conj (MulAut.conj (e (c i)))).toMonoidHom at hm
    rwa [hAB] at hm

end Representation.BinaryOffender
