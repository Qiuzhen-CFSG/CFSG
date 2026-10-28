module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.UnipotentSection
public import Theory.GroupTheory.PerfectCentralCoverLocalBound

/-!
# Unipotent lifts with a controlled central multiplication defect

Six additive root lifts need not satisfy the unipotent multiplication law.
If their errors lie in a normal subgroup `N` of the central kernel, their
images modulo `N` do satisfy that law. The six-coordinate bijection then
constructs a section of the literal unipotent subgroup in the quotient.
Its full preimage is a local lift whose intersection with the original
kernel is exactly `N`.

For G₂(3), a cyclic defect subgroup of order at most three therefore gives
the required three-primary upper bound by transfer. The existence of such
a defect subgroup is a separate root-relation calculation; additive root
lifts alone do not imply it.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (PDF p.419), and GLS3
§6.1, with Griess's exceptional multiplier calculation cited there as [Gr1].
The root coordinates are the attributed ATLAS port imported through
`MultiplierOrdinary.UnipotentSection` (LICENSES/ATLAS.txt).
-/

@[expose] public section

namespace Atlas.G2.MultiplierOrdinary.RootSections

variable {F E : Type*} [Field F] [Group E] {f : E →* Model F}

/-- The error in the literal A–F product law lies in `N`. -/
def ProductCompatibleModulo (L : RootSections f) (N : Subgroup E) : Prop :=
  ∀ t u, L.product t * L.product u * (L.product (unipotentProductParameters t u))⁻¹ ∈ N

/-- Lift the actual unipotent subgroup with kernel exactly the prescribed
normal error subgroup. This constructs the lift from the product law. -/
theorem exists_local_lift_of_product_modulo
    (L : RootSections f) (N : Subgroup E) [N.Normal] (hN : N ≤ f.ker)
    (hL : L.ProductCompatibleModulo N) :
    ∃ H : Subgroup E, H.map f = unipotent (K := F) ∧ H ⊓ f.ker = N := by
  let q := QuotientGroup.mk' N
  let g := QuotientGroup.lift N f hN
  have hg (x : E) : g (q x) = f x := rfl
  let M : RootSections g := {
    root := fun i => q.comp (L.root i)
    project := fun i => by
      apply MonoidHom.ext
      intro x
      exact DFunLike.congr_fun (L.project i) x }
  have hprod (t : Fin 6 → F) : M.product t = q (L.product t) := by
    simp only [product, M, MonoidHom.comp_apply, map_mul]
  have hM : M.ProductCompatible := by
    intro t u
    rw [hprod, hprod, hprod, ← map_mul]
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hL t u)
  obtain ⟨s, hs⟩ := M.exists_unipotent_section hM
  let H := s.range.comap q
  have hmap : H.map f = unipotent (K := F) := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      obtain ⟨u, hu⟩ := hy
      have hfu : f y = (u : Model F) := by
        rw [← hg, ← hu]
        exact DFunLike.congr_fun hs u
      rw [hfu]
      exact u.property
    · intro x hx
      obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N (s ⟨x, hx⟩)
      refine ⟨y, ?_, ?_⟩
      · exact ⟨⟨x, hx⟩, hy.symm⟩
      · rw [← hg, hy]
        exact DFunLike.congr_fun hs ⟨x, hx⟩
  refine ⟨H, hmap, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨u, hu⟩ := hx.1
    have hu1 : u = 1 := by
      apply Subtype.ext
      calc
        (u : Model F) = g (s u) := (DFunLike.congr_fun hs u).symm
        _ = f x := by rw [hu, hg]
        _ = 1 := hx.2
    apply (QuotientGroup.eq_one_iff _).mp
    change q x = 1
    rw [← hu, hu1, map_one]
  · intro x hx
    refine ⟨?_, hN hx⟩
    change q x ∈ s.range
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [hxq]
    exact s.range.one_mem

end Atlas.G2.MultiplierOrdinary.RootSections

end
