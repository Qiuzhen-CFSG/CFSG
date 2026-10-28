module

public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.G2DerivedPermutationFiltration.Extensions
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite factor-degree filtrations under contragredient duality

The coannihilator proves that the dual of a finite-dimensional simple
representation is simple. Dualizing each step of a filtration gives the exact
sequence `(V / S)* → V* → S*`: pullback along the literal quotient map identifies
the kernel of restriction. The existing exact-extension construction then
reverses the filtration, preserving the dimensions of all simple factors.

The concrete consumer is the pair of Hermitian point-module inductions for
M22, in the degree-table argument of Guralnick--Malle, Classification of
2F-modules I, Proposition 5.1, pp.15--16; see also Aschbacher--Smith,
Chapter K, printed pp.451--452 and 457. No splitting hypothesis is used.
-/

@[expose] public noncomputable section
namespace Representation
variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- Duality reverses an equivariant linear equivalence. -/
def Equiv.contragredient (e : ρ.Equiv σ) : σ.dual.Equiv ρ.dual :=
  .mk e.toLinearEquiv.dualMap (by
    intro g
    ext f v
    exact congrArg f (LinearMap.congr_fun (e.isIntertwining' g⁻¹) v).symm)

/-- The annihilator of an invariant subspace of the dual is invariant. -/
def dualCoannihilatorSubrep (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have h := hv (ρ.dual g⁻¹ f) (S.apply_mem_toSubmodule g⁻¹ hf)
    simpa only [dual_apply, inv_inv, Module.Dual.transpose_apply, LinearMap.comp_apply] using h

/-- Finite-dimensional contragredient duality preserves simplicity. -/
theorem isIrreducible_dual [FiniteDimensional k V] [IsIrreducible ρ] :
    IsIrreducible ρ.dual := by
  have hb : dualCoannihilatorSubrep (ρ := ρ) ⊥ = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.dualCoannihilator_bot
  have ht : dualCoannihilatorSubrep (ρ := ρ) ⊤ = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.dualCoannihilator_top
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h' := congrArg (dualCoannihilatorSubrep (ρ := ρ)) h
    rw [hb, ht] at h'
    exact bot_ne_top h'.symm
  · intro S
    rcases eq_bot_or_eq_top (dualCoannihilatorSubrep S) with h | h
    · right
      apply Subrepresentation.toSubmodule_injective
      have hc : S.toSubmodule.dualCoannihilator = ⊥ :=
        congrArg Subrepresentation.toSubmodule h
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule), hc]
      exact Submodule.dualAnnihilator_bot
    · left
      apply Subrepresentation.toSubmodule_injective
      have hc : S.toSubmodule.dualCoannihilator = ⊤ :=
        congrArg Subrepresentation.toSubmodule h
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule), hc]
      exact Submodule.dualAnnihilator_top

namespace FactorDegreeFiltration
/-- Transport a filtration along an equivariant linear equivalence. -/
theorem of_equiv {D : Set ℕ} (h : FactorDegreeFiltration D ρ) (e : ρ.Equiv σ) :
    FactorDegreeFiltration D σ :=
  h.transport (MonoidHom.id G) Function.surjective_id σ e.toLinearEquiv
    (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v)

/-- A simple module itself gives a one-step filtration. -/
theorem of_irreducible {D : Set ℕ} [IsIrreducible ρ]
    (hd : Module.finrank k V ∈ D) : FactorDegreeFiltration D ρ := by
  let S : Subrepresentation ρ := ⊥
  let e : S.quotientRepresentation.Equiv ρ :=
    .mk (S.toSubmodule.quotEquivOfEqBot rfl) (by
      intro g
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | H v => rfl)
  let : Subsingleton S.toSubmodule := inferInstanceAs (Subsingleton (⊥ : Submodule k V))
  refine .step S (.zero _) ?_ ?_
  · exact (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv inferInstance
  · rw [e.toLinearEquiv.finrank_eq]
    exact hd

/-- Reverse a finite filtration by taking annihilators. -/
theorem dual {D : Set ℕ} (h : FactorDegreeFiltration D ρ) :
    ∀ [FiniteDimensional k V], FactorDegreeFiltration D ρ.dual := by
  induction h with
  | zero τ => intro _; exact .zero _
  | @step X _ _ τ S previous simple degree ih =>
    intro hfin
    let := simple
    let : IsIrreducible S.quotientRepresentation.dual := isIrreducible_dual
    have hq : FactorDegreeFiltration D S.quotientRepresentation.dual :=
      of_irreducible (by rwa [Subspace.dual_finrank_eq])
    let i : S.quotientRepresentation.dual.IntertwiningMap τ.dual := {
      toLinearMap := S.toSubmodule.mkQ.dualMap
      isIntertwining' := by intro g; rfl }
    let f : τ.dual.IntertwiningMap S.toRepresentation.dual := {
      toLinearMap := S.toSubmodule.dualRestrict
      isIntertwining' := by intro g; rfl }
    apply of_exact hq ih i f
      (LinearMap.dualMap_injective_of_surjective S.toSubmodule.mkQ_surjective)
    intro φ
    constructor
    · intro hφ
      have hz : S.toSubmodule ≤ LinearMap.ker φ := by
        intro x hx
        exact LinearMap.congr_fun hφ ⟨x, hx⟩
      exact ⟨S.toSubmodule.liftQ φ hz, rfl⟩
    · rintro ⟨ψ, rfl⟩
      ext x
      change ψ (S.toSubmodule.mkQ x.val) = 0
      have hz : S.toSubmodule.mkQ x.val = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr x.property
      rw [hz, map_zero]
end FactorDegreeFiltration
end Representation
