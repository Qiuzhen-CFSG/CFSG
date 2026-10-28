module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.WeakClosure
public import Theory.Representation.BinaryPermutation.FiveAction

/-!
# Actual conjugation coordinates for the terminal A₅ argument

The coordinates identify V with the binary five-point augmentation core and
intertwine the literal normalizer conjugation with coordinate permutations.
They imply that the actor kernel is exactly C_G(V). Containment of A₅ in the
actor image gives the two nonzero orbits needed by the weak-closure proof.

In the source marking, V₃ is the hyperplane perpendicular to the singular
point V₁, namely the core vectors with last coordinate zero. Its pointwise
fixer is trivial. Together with 13.2.3(2), this proves C_G(V₃) ≤ C_G(V),
and hence clause (g)(i) of F.9.8 for every local H.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), §B.3, Lemmas 13.2.3 and 13.3.11, and the final
paragraph of §13.6, printed p.935. The parent supplies the actual earlier
module coordinates and the source marking; no classification is assumed here.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction

open Subgroup BinaryPermutation BinaryPermutation.FiveGeometry

variable {G : Type*} [Group G] {V : Subgroup G}

/-- Actual coordinates for the full normalizer action, with its kernel
left unrestricted. The kernel is identified by `actor_eq_one_iff` below. -/
structure FiveCoordinates (V : Subgroup G) where
  equiv : V ≃* Multiplicative (core (Fin 5))
  actor : normalizer (V : Set G) →* Equiv.Perm (Fin 5)
  equivariant : ∀ (n : normalizer (V : Set G)) (x : V),
    (equiv (V.normalizerMonoidHom n x)).toAdd =
      coreRepresentation (Fin 5) (actor n) (equiv x).toAdd

namespace FiveCoordinates

/-- The model orbit calculation is transported through genuine conjugation. -/
theorem orbits (d : FiveCoordinates V)
    (hAlt : alternatingGroup (Fin 5) ≤ d.actor.range) :
    HasFiveModuleOrbits V d.equiv := by
  intro x y hx hy hq
  have hx0 : (d.equiv x).toAdd ≠ 0 := by
    intro h
    exact hx (d.equiv.injective (h.trans (map_one d.equiv).symm))
  have hy0 : (d.equiv y).toAdd ≠ 0 := by
    intro h
    exact hy (d.equiv.injective (h.trans (map_one d.equiv).symm))
  obtain ⟨a, ha⟩ := exists_even_transport _ _ hx0 hy0 hq
  obtain ⟨n, hn⟩ := hAlt a.property
  have heq : V.normalizerMonoidHom n x = y := by
    apply d.equiv.injective
    change (d.equiv (V.normalizerMonoidHom n x)).toAdd = (d.equiv y).toAdd
    rw [d.equivariant, hn, ha]
  exact ⟨n.val, n.property, congrArg Subtype.val heq⟩

/-- The normalizer actor has exactly the genuine centralizer as kernel. -/
theorem actor_eq_one_iff (d : FiveCoordinates V) (n : normalizer (V : Set G)) :
    d.actor n = 1 ↔ n.val ∈ centralizer (V : Set G) := by
  have hker : V.normalizerMonoidHom n = 1 ↔ n.val ∈ centralizer (V : Set G) := by
    change n ∈ V.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  constructor
  · intro hn
    apply hker.mp
    apply MulEquiv.ext
    intro x
    apply d.equiv.injective
    change (d.equiv (V.normalizerMonoidHom n x)).toAdd = (d.equiv x).toAdd
    rw [d.equivariant, hn]
    simp
  · intro hn
    have hauto := hker.mpr hn
    apply eq_one_of_fixes_hyperplane
    intro x _
    let y := d.equiv.symm (Multiplicative.ofAdd x)
    have heq : (d.equiv y).toAdd = x := by simp [y]
    have h := d.equivariant n y
    rw [hauto] at h
    simpa only [MulAut.one_apply, heq] using h.symm

/-- Pointwise fixation of the actual V₃ marking forces centralization of V. -/
theorem centralizer_hyperplane_le (d : FiveCoordinates V) (V₃ : Subgroup G)
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (d.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G)) :
    centralizer (V₃ : Set G) ≤ centralizer (V : Set G) := by
  intro c hc
  let n : normalizer (V : Set G) := ⟨c, hN (centralizer_le_normalizer _ hc)⟩
  apply (d.actor_eq_one_iff n).mp
  apply eq_one_of_fixes_hyperplane
  intro x hx
  let y := d.equiv.symm (Multiplicative.ofAdd x)
  have heq : (d.equiv y).toAdd = x := by simp [y]
  have hy : y.val ∈ V₃ := (hmark y).mpr (by rw [heq]; exact hx)
  have hnfix : V.normalizerMonoidHom n y = y := by
    apply Subtype.ext
    change c * y.val * c⁻¹ = y.val
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc y.val hy).symm
  have h := d.equivariant n y
  rw [hnfix, heq] at h
  exact h.symm

/-- Clause (g)(i) of F.9.8, with any actual H and V₁. In the A₅ case the
commutator is already trivial. The normalizer containment is 13.2.3(2). -/
theorem source_F_9_8_g_i (d : FiveCoordinates V) (V₃ H V₁ : Subgroup G)
    (hmark : ∀ x : V, x.val ∈ V₃ ↔ (d.equiv x).toAdd.val 4 = 0)
    (hN : normalizer (V₃ : Set G) ≤ normalizer (V : Set G)) :
    ⁅V, H ⊓ centralizer (V₃ : Set G)⁆ ≤ V₁ := by
  have hc : H ⊓ centralizer (V₃ : Set G) ≤ centralizer (V : Set G) :=
    inf_le_right.trans (d.centralizer_hyperplane_le V₃ hmark hN)
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr hc]
  exact bot_le

end FiveCoordinates
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
