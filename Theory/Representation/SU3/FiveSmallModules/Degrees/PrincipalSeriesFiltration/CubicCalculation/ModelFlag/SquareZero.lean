module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.Model

/-!
# The image/kernel flag of a square-zero intertwiner

On a 126-dimensional representation, an equivariant square-zero map of
rank 21 gives the invariant stages 0, image, kernel, and the whole space.
Rank-nullity on the literal successive quotients gives 21, 84, 21.
The first and last quotient actions are explicitly equivalent to the image
action. No simplicity or existence of such an intertwiner is asserted.

This is the linear-algebra assembly used by the cubic principal-series
calculation for Guralnick–Malle, Proposition 4.3, p.10.
-/

@[expose] public section
namespace Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  {ρ : Representation K G V}

def imageKernelStage (f : ρ.IntertwiningMap ρ) : ℕ → Subrepresentation ρ
  | 0 => ⊥
  | 1 => f.range
  | 2 => f.ker
  | _ => ⊤

theorem finrank_within_quotient [FiniteDimensional K V]
    (S T : Subrepresentation ρ) (h : S ≤ T) :
    Module.finrank K (T.toSubmodule ⧸ (within S T).toSubmodule) =
      Module.finrank K T.toSubmodule - Module.finrank K S.toSubmodule := by
  rw [Submodule.finrank_quotient, ← (withinEquiv S T h).finrank_eq]

/-- The stages and the dimensions refer to the given intertwiner on the
original representation, with no replacement of its quotient actions. -/
noncomputable def imageKernelFlag [FiniteDimensional K V]
    (f : ρ.IntertwiningMap ρ) (hsq : ∀ v, f (f v) = 0)
    (hd : Module.finrank K V = 126) (hr : Module.finrank K f.range.toSubmodule = 21) :
    ThreeStepFlag ρ := by
  have hn : f.range ≤ f.ker := by
    rintro v ⟨w, rfl⟩
    exact hsq w
  have hk : Module.finrank K f.ker.toSubmodule = 105 := by
    have h := f.toLinearMap.finrank_range_add_finrank_ker
    change Module.finrank K f.range.toSubmodule + Module.finrank K f.ker.toSubmodule = _ at h
    omega
  refine ⟨imageKernelStage f, rfl, rfl, ?_, ?_⟩
  · intro m hm
    interval_cases m
    · exact bot_le
    · exact hn
    · exact le_top
  · intro m hm
    interval_cases m
    · change Module.finrank K (f.range.toSubmodule ⧸ (within ⊥ f.range).toSubmodule) = 21
      rw [finrank_within_quotient _ _ bot_le, hr]
      change 21 - Module.finrank K (⊥ : Submodule K V) = 21
      simp
    · change Module.finrank K (f.ker.toSubmodule ⧸ (within f.range f.ker).toSubmodule) = 84
      rw [finrank_within_quotient _ _ hn, hk, hr]
    · change Module.finrank K ((⊤ : Subrepresentation ρ).toSubmodule ⧸
        (within f.ker ⊤).toSubmodule) = 21
      rw [finrank_within_quotient _ _ le_top, hk]
      change Module.finrank K (⊤ : Submodule K V) - 105 = 21
      simp [hd]

noncomputable def firstQuotientEquivRange (f : ρ.IntertwiningMap ρ) :
    (f.range.toSubmodule ⧸ (within ⊥ f.range).toSubmodule) ≃ₗ[K] f.range.toSubmodule :=
  Submodule.quotEquivOfEqBot _ (by
    ext v
    change (v.val = 0) ↔ v = 0
    constructor
    · exact fun h => Subtype.ext h
    · exact fun h => congrArg Subtype.val h)

theorem firstQuotientEquivRange_action (f : ρ.IntertwiningMap ρ) (g : G)
    (v : f.range.toSubmodule ⧸ (within ⊥ f.range).toSubmodule) :
    firstQuotientEquivRange f ((within ⊥ f.range).quotientRepresentation g v) =
      f.range.toRepresentation g (firstQuotientEquivRange f v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v => rfl

noncomputable def lastQuotientEquivRange (f : ρ.IntertwiningMap ρ) :
    ((⊤ : Subrepresentation ρ).toSubmodule ⧸ (within f.ker ⊤).toSubmodule) ≃ₗ[K]
      f.range.toSubmodule :=
  (Submodule.Quotient.equiv _ _ Submodule.topEquiv (by
    change (f.ker.toSubmodule.comap (⊤ : Submodule K V).subtype).map
      (⊤ : Submodule K V).subtype = f.ker.toSubmodule
    exact Submodule.map_comap_eq_of_surjective (fun v => ⟨⟨v, by trivial⟩, rfl⟩) _)).trans
      f.toLinearMap.quotKerEquivRange

@[simp] theorem lastQuotientEquivRange_mk (f : ρ.IntertwiningMap ρ) (v : (⊤ : Subrepresentation ρ).toSubmodule) :
    (lastQuotientEquivRange f (Submodule.Quotient.mk v)).val = f v.val := rfl

theorem lastQuotientEquivRange_action (f : ρ.IntertwiningMap ρ) (g : G)
    (v : (⊤ : Subrepresentation ρ).toSubmodule ⧸ (within f.ker ⊤).toSubmodule) :
    lastQuotientEquivRange f ((within f.ker ⊤).quotientRepresentation g v) =
      f.range.toRepresentation g (lastQuotientEquivRange f v) := by
  induction v using Submodule.Quotient.induction_on with
  | H v =>
    apply Subtype.ext
    exact f.isIntertwining _ _ g v.val

variable {W : Type*} [AddCommGroup W] [Module K W]
noncomputable def conjugateRangeEquiv (e : V ≃ₗ[K] W) (N : Module.End K W) :
    LinearMap.range (e.symm.conj N) ≃ₗ[K] LinearMap.range N :=
  e.submoduleMap _ |>.trans <| LinearEquiv.ofEq _ _ (by
    ext w
    constructor
    · rintro ⟨v, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm (N x), ⟨e.symm x, by simp⟩, by simp⟩)

end Representation.SU3.FiveSmallModules.Degrees.CubicCalculation.ModelFlag
