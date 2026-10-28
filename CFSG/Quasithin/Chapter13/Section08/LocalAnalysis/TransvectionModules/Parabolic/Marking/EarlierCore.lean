module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.CoreBounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.ComponentSetup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.LocalProduct
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.Applicability
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.EarlierCore.FlagTransport

/-!
# Apply the earlier local identities in the ordinary A₆ case of 13.8.6

The given L-action extends to LT through the proved normalizer of the
concrete alternating natural image. The actual module and Sylow flag satisfy the ordinary hypotheses
of 13.5.4. The earlier theorem is a universal implication at the fixed
standing source configuration; its two consumed local clauses remain an
explicit input. The global hypotheses of §13.5 are the responsibility of
that input's supplier. This module does not assert 13.5.4 for arbitrary
natural semidirect products or assert the complete 13.8.6.

The two relative-normalizer residual conventions agree as literal subgroups.
Sylow containment and normalization identify I₂ with the source product and
prove O²(I₂)=L₂. A fixed-point-free cubic in the natural plane residual
proves V=[V,L₂] and V=⟨V₃^{L₂}⟩. The point residual similarly gives
V₃=⟨V₂^{L₁}⟩ for the compatible-cover marking. Applying the earlier local
clauses now supplies the normal closure and centralizer identities needed
by `source_core_bounds_and_generation`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, pp.876–877; Notation 13.3.3, p.885;
Remark 13.5.3 and Lemma 13.5.4, p.916; 13.8.6(2),(3), p.948.
-/

@[expose] public section
open Subgroup Module BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
variable {G : Type*} [Group G]

/-- The two consumed ordinary clauses of the universal earlier 13.5.4,
at the fixed genuine standing configuration `(G,T,L,V)`.

The antecedent retains the actual quotient and natural action, its faithful
kernel and fixed subgroup, and every dimensional and invariance condition
on the literal flag. The source residual here is O²(N_LT(W₂)) from
13.2.1. The group I is specified by the actual set product, not by an
assumed normal-closure identity. All flags and product subgroups are
universally quantified; no specialized local conclusion is a setup field.
The additional conclusions of 13.5.4 are not claimed by this interface.
-/
def Earlier1354 (T : Sylow 2 G) (L V : Subgroup G) : Prop :=
  (T : Subgroup G) ≤ normalizer (L : Set G) →
  ∀ (hLV : L ≤ normalizer (V : Set G))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (eV : V ≃* Multiplicative Natural),
    (∀ (l : L) (v : V),
      (eV (V.normalizerMonoidHom ⟨l.val, hLV l.property⟩ v)).toAdd =
        alternatingNaturalRepresentation (Fin 6) (eL (QuotientGroup.mk' (pCore 2 L) l))
          (eV v).toAdd) →
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 →
    V ⊓ centralizer (L : Set G) = ⊥ →
    ∀ (W₁ W₂ W₃ : Subgroup G),
      W₁ ≤ W₂ → W₂ ≤ W₃ → W₃ ≤ V →
      Nat.card W₁ = 2 → Nat.card W₂ = 4 → Nat.card W₃ = 8 →
      (T : Subgroup G) ≤ normalizer (W₁ : Set G) →
      (T : Subgroup G) ≤ normalizer (W₂ : Set G) →
      (T : Subgroup G) ≤ normalizer (W₃ : Set G) →
      ∀ I : Subgroup G,
        (I : Set G) = ((normalizer (W₁ : Set G)).pCoreIn 2 : Set G) *
          (residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (W₂ : Set G)) : Set G) →
        I = conjugateSpanBy ((normalizer (W₁ : Set G)).pCoreIn 2)
          (normalizer (W₂ : Set G)) ∧
        I ⊓ centralizer (W₂ : Set G) = I.pCoreIn 2

namespace NaturalSetup
variable [Finite G] {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃)

include d

/-- Prove applicability to the actual module and flag before specializing
the earlier implication. Both residual conventions and the product are discharged. -/
theorem apply_earlier (earlier : Earlier1354 T L V) :
    localI L V₁ V₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
      (normalizer (V₂ : Set G)) ∧
    localI L V₁ V₂ ⊓ centralizer (V₂ : Set G) = (localI L V₁ V₂).pCoreIn 2 := by
  have hprod : (localI L V₁ V₂ : Set G) =
      ((normalizer (V₁ : Set G)).pCoreIn 2 : Set G) *
        (residual ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₂ : Set G)) : Set G) := by
    rw [d.plane_residual_eq]
    exact d.localI_product
  exact earlier d.normalizes_L (le_sup_left.trans d.normalizes_V) d.model d.coordinate
    d.component_conjugation d.component_centralizer d.fixed_subgroup
    V₁ V₂ V₃ d.line_le_plane d.plane_le_seed d.seed_le
    d.flag_orders.1 d.flag_orders.2.1 d.flag_orders.2.2
    d.line_stable d.plane_stable d.seed_stable (localI L V₁ V₂) hprod

/-- The earlier identities are now available for the literal source L₂ and I₂. -/
theorem earlier_identities (earlier : Earlier1354 T L V) :
    localI L V₁ V₂ = conjugateSpanBy ((normalizer (V₁ : Set G)).pCoreIn 2)
      (normalizer (V₂ : Set G)) ∧
    residual (localI L V₁ V₂) = localResidual L V₂ ∧
    localI L V₁ V₂ ⊓ centralizer (V₂ : Set G) = (localI L V₁ V₂).pCoreIn 2 ∧
    localResidual L V₂ ≤ L ∧
    V = conjugateSpanBy V₃ (localResidual L V₂) ∧ V = ⁅V, localResidual L V₂⁆ :=
  ⟨(d.apply_earlier earlier).1, d.localI_residual, (d.apply_earlier earlier).2,
    localResidual_le L V₂, d.plane_generation⟩

/-- Conditional assembly of both core bounds and 13.8.6(3), with the earlier
13.5.4 implication as the sole local-theorem premise. All specialized identities
are proved, including the ordinary A₆ representation applicability. -/
theorem core_bounds_and_generation (earlier : Earlier1354 T L V)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    ⁅Source.K2 H V₂, localResidual L V₂⁆ ≤
      (Source.K2 H V₂).pCoreIn 2 ⊓ (localResidual L V₂).pCoreIn 2 ∧
    Source.U2 H V V₂ = ⁅Source.U2 H V V₂, localResidual L V₂⁆ ∧
    Source.U2 H V V₂ ≤ Source.UL L H V₃ := by
  obtain ⟨hI, hc⟩ := d.apply_earlier earlier
  obtain ⟨hgen, hcomm⟩ := d.plane_generation
  exact source_core_bounds_and_generation T H L (localI L V₁ V₂)
    (localResidual L V₂) V V₁ V₂ V₃ hTH d.line_stable d.plane_stable
    hI d.localI_residual.symm hc (localResidual_le L V₂) hgen hcomm

end NaturalSetup

/-- Final entry point from the given natural L-action and the Sylow flag.
The full LT action is constructed, and every specialized earlier identity
is discharged before the existing CoreBounds theorem is instantiated. -/
theorem ComponentSetup.core_bounds_and_generation [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : ComponentSetup T L V V₁ V₂ V₃) (earlier : Earlier1354 T L V)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) :
    ⁅Source.K2 H V₂, localResidual L V₂⁆ ≤
      (Source.K2 H V₂).pCoreIn 2 ⊓ (localResidual L V₂).pCoreIn 2 ∧
    Source.U2 H V V₂ = ⁅Source.U2 H V V₂, localResidual L V₂⁆ ∧
    Source.U2 H V V₂ ≤ Source.UL L H V₃ :=
  d.extend.core_bounds_and_generation earlier H hTH

/-- The two flag-generation identities used to transport Ṽ₃, already
available from the natural L-action alone. -/
theorem ComponentSetup.flag_generation [Finite G]
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (d : ComponentSetup T L V V₁ V₂ V₃) :
    V₃ = conjugateSpanBy V₂ (localResidual L V₁) ∧
    V₃ = ⁅V₃, localResidual L V₁⁆ ⊔ V₁ :=
  ⟨d.extend.seed_eq_plane_conjugateSpan, d.extend.seed_eq_commutator_sup_line⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.EarlierCore
