module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.DoubleFactor
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.MixedTransfer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.NormalThompson.Maximum.Singleton.HyperplaneTransfer

/-!
# Maximum elementary witnesses for all selected singleton factors

On the actual marked A₅ flag, either selected S₃ coordinate in the native
two-factor case has a maximum elementary subgroup of its full star preimage
with nontrivial star image. We combine the double-S₃ rank comparison with
the mixed transfer. The latter uses the flag's actual action kernel to
supply the earlier cubic quotient; no auxiliary kernel, quotient-offender
lifting or complementary-factor hypothesis remains.

The hyperplane branch uses its native fixed-part estimate, preserving the
decomposition of the moved space and the codimension-one clause. All three
witnesses retain only the moved-space order four supplied independently by
`qt-13-06-solvable-product-supports`. The support self-commutator identity
and the SQTK cover are unnecessary once these native branch inputs are given.

These are the literal witnesses consumed by the first, second and
hyperplane `thompson_of_maximum` theorems in `NormalThompson`. That parent
retains the final Thompson equality and the discharge of the support input.
This module imports only its lower normality and witness interfaces through
the branch modules, so the parent can import it without a cycle.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.2.4, printed pp.75–76; B.5.6(3),(5), p.105; and 13.6.13, p.929.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G] [Finite G]

/-- The selected first factor has a moving maximum in its full preimage,
for every native complementary factor. The source flag discharges the marked
action-kernel input of the mixed transfer. -/
theorem minimalSolvable_twoFactor_first_singleton_maximum
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.first ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.first).map c.first.subtype) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.first.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        E.map (starMk z v) ≠ ⊥ := by
  classical
  intro z v I H hcard
  by_cases h : Nonempty (c.second ≃* Equiv.Perm (Fin 3))
  · obtain ⟨e'⟩ := h
    exact minimalSolvable_twoFactor_first_maximum_of_s3_complement
      L (T : Subgroup G) z v (A5Module.markedZ_mem_Gv f.module)
      S hS hX c e e' hF hfix hcard
  · exact minimalSolvable_twoFactor_first_maximum_of_mixed_flag
      f S hS hfix hL hX c e hF hcard

/-- The selected second factor has a moving maximum in its full preimage,
for every native complementary factor. The source flag discharges the marked
action-kernel input of the mixed transfer. -/
theorem minimalSolvable_twoFactor_second_singleton_maximum
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    (hL : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      normalizer (Lv L (A5Module.markedV f.module) : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))))
    (e : c.second ≃* Equiv.Perm (Fin 3))
    (hF : X.subgroupOf (FFFactors.offenderActor
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module))) =
      (pResidual 2 c.second).map c.second.subtype) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        E.map (starMk z v) ≠ ⊥ := by
  classical
  intro z v I H hcard
  by_cases h : Nonempty (c.first ≃* Equiv.Perm (Fin 3))
  · obtain ⟨e'⟩ := h
    exact minimalSolvable_twoFactor_second_maximum_of_s3_complement
      L (T : Subgroup G) z v (A5Module.markedZ_mem_Gv f.module)
      S hS hX c e' e hF hfix hcard
  · exact minimalSolvable_twoFactor_second_maximum_of_mixed_flag
      f S hS hfix hL hX c e hF hcard

/-- The native hyperplane selection has the same literal witness. Its
second factor and residual selection are supplied by the native branch;
the fixed-part estimate discharges the rank comparison. -/
theorem minimalSolvable_hyperplane_singleton_maximum
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ f.module) (A5Module.markedV f.module))]
    (S : Sylow 2 (Gv (A5Module.markedV f.module)))
    (hS : (S : Subgroup (Gv (A5Module.markedV f.module))).map
      (Gv (A5Module.markedV f.module)).subtype = Tv (T : Subgroup G) (A5Module.markedV f.module))
    (hfix : Tv (T : Subgroup G) (A5Module.markedV f.module) ≤
      centralizer ({A5Module.markedZ f.module} : Set G))
    {X : Subgroup (Gstar (A5Module.markedZ f.module) (A5Module.markedV f.module))}
    (hX : MinimalSolvable L (T : Subgroup G)
      (A5Module.markedZ f.module) (A5Module.markedV f.module) X)
    (c : HyperplaneCase (FFFactors.offenderRepresentation
      (starRepresentation (A5Module.markedZ f.module) (A5Module.markedV f.module)))) :
    let z := A5Module.markedZ f.module
    let v := A5Module.markedV f.module
    let I := FFFactors.offenderActor (starRepresentation z v)
    let H := c.second.map I.subtype
    Nat.card (movedSubgroup z v H) = 4 →
      ∃ E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)),
        E.map (starMk z v) ≠ ⊥ := by
  exact marked_minimalSolvable_hyperplane_maximum_of_support
    f.module (T : Subgroup G) S hS hfix hX c

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
