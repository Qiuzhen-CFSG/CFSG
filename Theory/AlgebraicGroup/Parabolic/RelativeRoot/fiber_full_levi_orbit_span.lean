module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_root_string_connectedness
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.fiber_levi_root_string_action
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_chevalley_torus_fiber_bridge
public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.sourceRelativeRootLayer_root_mem

/-!
Full Levi orbit spanning for a nonsingular relative-root fiber.  The orbit span
is invariant under the whole Levi representation, contains every parameter on
the initial fiber root by linearity of the root-vector coordinate, and then
contains every fiber root by the source root-string connectedness theorem and
the nonsingular Chevalley root-string action.  The canonical fiber-generator
span finishes the argument.  This is the orbit-span input for the abstract
generator-detection irreducibility criterion; no root-label transitivity is
assumed.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

public theorem RelativeRootFiberModule.full_levi_orbit_span
    (S : RelativeRootRepresentationSource K)
    (M : RelativeRootFiberModule S)
    (hNonsingular : ¬ IsUSingular S.classification (ringChar k))
    (z : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root } × k)
    (hz : z.2 ≠ 0) :
    Submodule.span k
      (Set.range fun l : Variety.Point S.L.carrierVariety =>
        (M.representation.action l).1 (M.rootVector z)) = ⊤ := by
  let W := Submodule.span k
    (Set.range fun l : Variety.Point S.L.carrierVariety =>
      (M.representation.action l).1 (M.rootVector z))
  change W = ⊤
  have hWinvariant : IsInvariantSubmodule M.representation W := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        apply Submodule.subset_span
        refine ⟨g * l, ?_⟩
        change (M.representation.action (g * l)).1 (M.rootVector z) =
          (M.representation.action g).1
            ((M.representation.action l).1 (M.rootVector z))
        rw [map_mul]
        rfl
    | zero => simp
    | add x y hx hy hxW hyW =>
        rw [map_add]
        exact W.add_mem hxW hyW
    | smul c x hx hxW =>
        rw [map_smul]
        exact W.smul_mem c hxW
  have hzW : M.rootVector z ∈ W := by
    apply Submodule.subset_span
    refine ⟨1, ?_⟩
    simp
  have hbase : ∀ t, M.rootVector (z.1, t) ∈ W := by
    intro t
    have hparam : (t * z.2⁻¹) * z.2 = t := by
      rw [mul_assoc, inv_mul_cancel₀ hz, mul_one]
    rw [← hparam, M.rootVector_smul]
    exact W.smul_mem _ hzW
  have hall : ∀ (γ : { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }) (t : k),
      M.rootVector (γ, t) ∈ W := by
    intro γ
    have hreach := S.fiber_root_string_connected z.1 γ
    induction hreach with
    | refl => exact hbase
    | tail hab hbc ih =>
        exact M.rootVector_mem_of_levi_root_string S hNonsingular W hWinvariant
          hbc ih
  apply top_unique
  rw [← relativeRootFiberQuotientGenerator_span_eq_top S M]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨γ, t⟩, rfl⟩
  exact hall γ t

end Theory.AlgebraicGroup
