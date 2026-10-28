module
public import Theory.GroupTheory.IntersectingConjugates
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# A central kernel forces displacement centralization

Suppose intersecting conjugates of `W` commute. A nonidentity element of
`C_W(V)` belongs to every `V`-conjugate of `W`, so their generated subgroup
is abelian. Since `V` normalizes that span, the span contains `[V,A]` for
any `A ≤ W`. Thus `W` centralizes the actual displacement subgroup `[V,A]`.

This supplies the kernel argument used in the weak-closure step of
Aschbacher–Smith, Lemma 13.3.19, printed pp.895–896. The automorphism lemma
retains the same property for the literal conjugate subgroup.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- Intersecting-conjugate commutation is invariant under automorphisms. -/
theorem intersecting_conjugates_commute_map_equiv
    (V : Subgroup G)
    (hc : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (e : G ≃* G) (g : G)
    (hi : V.map e.toMonoidHom ⊓
      (V.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V.map e.toMonoidHom,
      (V.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have he : (V.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
      (V.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hi' : V ⊓ V.map (MulAut.conj (e.symm g)).toMonoidHom ≠ ⊥ := by
    intro h
    apply hi
    rw [← he, ← map_inf _ _ e.toMonoidHom e.injective, h, map_bot]
  have h := congrArg (fun A : Subgroup G => A.map e.toMonoidHom) (hc (e.symm g) hi')
  simpa only [map_commutator, map_bot, he] using h

/-- A nontrivial kernel element makes the conjugate span abelian; the seed
therefore centralizes every displacement into that span. -/
theorem centralizes_displacement_of_intersecting_conjugates
    (W V A : Subgroup G)
    (hc : ∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅W, W.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hker : W ⊓ centralizer (V : Set G) ≠ ⊥) (hAW : A ≤ W) :
    W ≤ centralizer ((⁅V, A⁆ : Subgroup G) : Set G) := by
  obtain ⟨b, hb⟩ := ne_bot_iff_exists_ne_one.mp hker
  have hb1 : (b : G) ≠ 1 := fun he => hb (Subtype.ext he)
  let _ := point_span_abelian_of_intersecting_conjugates_commute W b.property.1 hb1 hc
  have hVC : V ≤ centralizer ({(b : G)} : Set G) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (b.property.2 v hv)
  let _ := conjugateSpanBy_isMulCommutative_of_le (le_refl W) hVC
  have hW := (conjugateSpanBy_commutative_iff W V).mp inferInstance
  apply hW.trans
  apply centralizer_le
  exact (commutator_mono le_rfl (hAW.trans (le_conjugateSpanBy W V))).trans
    (le_normalizer_iff_commutator_le_right.mp (le_normalizer_conjugateSpanBy W V))

end Subgroup
