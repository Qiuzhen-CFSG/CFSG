module

public import Theory.Representation.SymplecticFourOrthogonalCover.SylowFlag.Stabilizers.Shears
public import Mathlib.RepresentationTheory.Irreducible

/-!
# Binary irreducibility of the actual Sp₄′ flag stabilizers

Transitivity on nonzero vectors excludes every proper nonzero binary invariant
subspace. Conjugation transports the actual stabilizer orbits to the moved line
and plane, with the original derived-group embedding and natural action.
Every theorem includes the binary endpoint Sp₄(2)′.

Source: Aschbacher–Smith, I.2.3(2), printed p.413 / PDF p.424.
-/

public section
noncomputable section
namespace Representation.SymplecticFourOrthogonalCover.SylowFlag
variable {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]

section General
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)

private theorem irreducible_of_transitive (hne : W ≠ ⊥)
    (h : ∀ x y : V, x ∈ W → y ∈ W → x ≠ 0 → y ≠ 0 →
      ∃ g : BinaryOffender.subspaceStabilizer ρ W, ρ g.val x = y) :
    IsIrreducible (BinaryOffender.stabilizerRepresentation ρ W) := by
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hs : S.toSubmodule ≠ ⊥ := fun he => hS (Subrepresentation.toSubmodule_injective he)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  apply le_antisymm le_top
  intro y _
  by_cases hy0 : y = 0
  · subst y
    exact S.toSubmodule.zero_mem
  obtain ⟨g,hg⟩ := h x.val y.val x.property y.property
    (fun he => hx0 (Subtype.ext he)) (fun he => hy0 (Subtype.ext he))
  have he : BinaryOffender.stabilizerRepresentation ρ W g x = y := Subtype.ext hg
  rw [← he]
  exact S.apply_mem_toSubmodule g hx

private theorem transitive_map (g : G)
    (h : ∀ x y : V, x ∈ W → y ∈ W → x ≠ 0 → y ≠ 0 →
      ∃ a : BinaryOffender.subspaceStabilizer ρ W, ρ a.val x = y)
    (x y : V) (hx : x ∈ W.map (ρ g)) (hy : y ∈ W.map (ρ g))
    (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ a : BinaryOffender.subspaceStabilizer ρ (W.map (ρ g)), ρ a.val x = y := by
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,rfl⟩ := hy
  have hu0 : u ≠ 0 := by intro he; apply hx0; rw [he,map_zero]
  have hv0 : v ≠ 0 := by intro he; apply hy0; rw [he,map_zero]
  obtain ⟨a,ha⟩ := h u v hu hv hu0 hv0
  have hm (w : V) : w ∈ W.map (ρ g) ↔ ρ g⁻¹ w ∈ W := by
    constructor
    · rintro ⟨z,hz,rfl⟩
      rwa [ρ.inv_self_apply]
    · intro hw
      exact ⟨ρ g⁻¹ w,hw,ρ.self_inv_apply g w⟩
  refine ⟨⟨(MulAut.conj g) a.val, ?_⟩, ?_⟩
  · intro w
    rw [hm,hm]
    simpa only [MulAut.conj_apply, map_mul, Module.End.mul_apply, ρ.inv_self_apply]
      using a.property (ρ g⁻¹ w)
  · rw [Transport.conjugate_action,ha]

private theorem map_ne_bot (hne : W ≠ ⊥) (g : G) : W.map (ρ g) ≠ ⊥ := by
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro he
  have hz : ρ g x = 0 := by
    have hm : ρ g x ∈ W.map (ρ g) := ⟨x,hx,rfl⟩
    rwa [he, Submodule.mem_bot] at hm
  exact hx0 ((ρ.apply_bijective g).injective (hz.trans (map_zero _).symm))
end General

omit [Algebra (ZMod 2) K] in
private lemma firstLine_ne_bot : firstLine (K := K) ≠ ⊥ := by
  intro he
  have hd := firstLine_finrank (K := K)
  rw [he,finrank_bot] at hd
  contradiction

omit [Algebra (ZMod 2) K] in
private lemma secondPlane_ne_bot : secondPlane (K := K) ≠ ⊥ := by
  intro he
  have hd := secondPlane_finrank (K := K)
  rw [he,finrank_bot] at hd
  contradiction

/-- Binary irreducibility for the actual stabilizer of the standard natural line. -/
theorem firstLine_stabilizer_irreducible : IsIrreducible
    (BinaryOffender.stabilizerRepresentation (binaryNatural (K := K))
      (firstLine.restrictScalars (ZMod 2))) :=
  irreducible_of_transitive _ _
    (by simpa only [ne_eq, Submodule.restrictScalars_eq_bot_iff] using firstLine_ne_bot (K := K))
    firstLine_transitive

/-- Binary irreducibility for the actual stabilizer of the standard natural plane. -/
theorem secondPlane_stabilizer_irreducible : IsIrreducible
    (BinaryOffender.stabilizerRepresentation (binaryNatural (K := K))
      (secondPlane.restrictScalars (ZMod 2))) :=
  irreducible_of_transitive _ _
    (by simpa only [ne_eq, Submodule.restrictScalars_eq_bot_iff] using secondPlane_ne_bot (K := K))
    secondPlane_transitive

/-- Conjugation transports binary irreducibility to every moved natural line. -/
theorem movedLine_stabilizer_irreducible (g : L (K := K)) : IsIrreducible
    (BinaryOffender.stabilizerRepresentation (binaryNatural (K := K))
      ((movedLine g).restrictScalars (ZMod 2))) := by
  have he : (movedLine g).restrictScalars (ZMod 2) =
      (firstLine.restrictScalars (ZMod 2)).map (binaryNatural g) := rfl
  rw [he]
  have hn : (firstLine (K := K)).restrictScalars (ZMod 2) ≠ ⊥ := by
    simpa only [ne_eq, Submodule.restrictScalars_eq_bot_iff] using firstLine_ne_bot (K := K)
  exact irreducible_of_transitive _ _ (map_ne_bot _ _ hn g)
    (transitive_map _ _ g firstLine_transitive)

/-- Conjugation transports binary irreducibility to every moved natural plane. -/
theorem movedPlane_stabilizer_irreducible (g : L (K := K)) : IsIrreducible
    (BinaryOffender.stabilizerRepresentation (binaryNatural (K := K))
      ((movedPlane g).restrictScalars (ZMod 2))) := by
  have he : (movedPlane g).restrictScalars (ZMod 2) =
      (secondPlane.restrictScalars (ZMod 2)).map (binaryNatural g) := rfl
  rw [he]
  have hn : (secondPlane (K := K)).restrictScalars (ZMod 2) ≠ ⊥ := by
    simpa only [ne_eq, Submodule.restrictScalars_eq_bot_iff] using secondPlane_ne_bot (K := K)
  exact irreducible_of_transitive _ _ (map_ne_bot _ _ hn g)
    (transitive_map _ _ g secondPlane_transitive)

end Representation.SymplecticFourOrthogonalCover.SylowFlag
