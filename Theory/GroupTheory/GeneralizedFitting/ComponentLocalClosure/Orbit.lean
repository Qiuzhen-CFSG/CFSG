module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.CenterlessProduct

/-!
# Direct products of local factors across component orbits

If the stabilizer of a centerless component normalizes a subgroup K inside
it, two conjugates of K in the same component agree. Indexing by the distinct
actual conjugates of K therefore embeds their containing components into the
component set. Distinct components commute; their trivial centers make them
independent. The canonical product homomorphism identifies the orbit join
with a nonempty finite direct power of K.

This is the component-orbit construction used for local overgroups in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 2.3.9(7), printed
pp.525–526. No normalization of the original component by the entire actor
is assumed.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem conjugate_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

/-- Stabilizer invariance identifies local factors in the same component. -/
theorem localFactor_conjugate_eq_of_component_conjugate_eq
    {L A K : Subgroup G}
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G))
    (a b : A)
    (he : L.map (MulAut.conj (a : G)).toMonoidHom =
      L.map (MulAut.conj (b : G)).toMonoidHom) :
    K.map (MulAut.conj (a : G)).toMonoidHom =
      K.map (MulAut.conj (b : G)).toMonoidHom := by
  have hL : (b : G)⁻¹ * a ∈ normalizer (L : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change L.map (MulAut.conj ((b : G)⁻¹ * a)).toMonoidHom = L
    rw [conjugate_mul, he, ← conjugate_mul]
    simp only [inv_mul_cancel]
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [h1, map_id]
  have hK := mem_normalizer_iff_map_conj_eq.mp
    (hinv ⟨A.mul_mem (A.inv_mem b.property) a.property, hL⟩)
  change K.map (MulAut.conj ((b : G)⁻¹ * a)).toMonoidHom = K at hK
  have heq := congrArg (fun J : Subgroup G =>
    J.map (MulAut.conj (b : G)).toMonoidHom) hK
  rw [← conjugate_mul] at heq
  simpa only [mul_inv_cancel_left] using heq

/-- The distinct local factors in a centerless component orbit form a direct
power of the original factor. The orbit is indexed by distinct actual
subgroups, so repetitions in the acting group do not introduce diagonal factors. -/
theorem componentOrbit_localFactor_equiv_power [Finite G]
    {L A K : Subgroup G} (hL : IsComponent G L) (hZ : center L = ⊥)
    (hKL : K ≤ L)
    (hinv : A ⊓ normalizer (L : Set G) ≤ normalizer (K : Set G)) :
    ∃ n : ℕ, 0 < n ∧ Nonempty ((Fin n → K) ≃* componentOrbit K A) := by
  classical
  let I := {J : Subgroup G // ∃ a : A, K.map (MulAut.conj (a : G)).toMonoidHom = J}
  let a : I → A := fun i => Classical.choose i.property
  have ha (i : I) : K.map (MulAut.conj (a i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  let C : I → Subgroup G := fun i => L.map (MulAut.conj (a i : G)).toMonoidHom
  have hCin : Function.Injective C := by
    intro i j hij
    apply Subtype.ext
    rw [← ha i, ← ha j]
    exact localFactor_conjugate_eq_of_component_conjugate_eq hinv (a i) (a j) hij
  have hCc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    have hc := (hL.map_conj (a i)).commutator_eq_bot_of_ne (hL.map_conj (a j))
      (fun he => hij (hCin he))
    exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) hx) y hy).symm
  have hCZ (i : I) : center (C i) = ⊥ := by
    let e : L ≃* C i := (MulAut.conj (a i : G)).subgroupMap L
    apply bot_unique
    intro x hx
    have hz : e.symm x ∈ center L := (centerCongr e.symm ⟨x, hx⟩).property
    rw [hZ, mem_bot] at hz
    exact mem_bot.mpr (e.symm.injective (hz.trans (map_one e.symm).symm))
  have hIC : (fun i : I => i.val) ≤ C := by
    intro i
    change i.val ≤ C i
    rw [← ha i]
    exact map_mono hKL
  have hind : iSupIndep (fun i : I => i.val) :=
    (iSupIndep_of_centerless_of_pairwise_commute C hCZ hCc).mono hIC
  have hc : Pairwise fun i j : I => ∀ x y : G, x ∈ i.val → y ∈ j.val → Commute x y := by
    intro i j hij x y hx hy
    exact hCc hij x y (hIC i hx) (hIC j hy)
  let : Fintype I := Fintype.ofFinite I
  let f : (∀ i : I, i.val) →* G := noncommPiCoprod hc
  have hf : Function.Injective f := injective_noncommPiCoprod_of_iSupIndep hind
  have hr : f.range = componentOrbit K A := by
    rw [noncommPiCoprod_range]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rw [← ha i]
      exact le_iSup (fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom) (a i)
    · refine iSup_le fun b => ?_
      exact le_iSup (fun i : I => i.val) ⟨_, b, rfl⟩
  let e₁ : (I → K) ≃* (∀ i : I, i.val) := MulEquiv.piCongrRight fun i =>
    ((MulAut.conj (a i : G)).subgroupMap K).trans (MulEquiv.subgroupCongr (ha i))
  let e₂ : (∀ i : I, i.val) ≃* componentOrbit K A :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  let : Nonempty I := ⟨⟨_, 1, rfl⟩⟩
  refine ⟨Fintype.card I, Fintype.card_pos, ⟨?_⟩⟩
  exact (MulEquiv.arrowCongr (Fintype.equivFin I).symm (MulEquiv.refl K)).trans (e₁.trans e₂)

end Theory.GroupTheory

end
