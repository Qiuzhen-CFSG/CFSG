module

public import Theory.Representation.SL2CentralExtensionFixedSpace.Moved
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame

/-!
# §14.7 local module calculation

This file records the part of the final A₅ local calculation that is
independent of the chapter's component and coset geometry.  The quotient map
is the actual binary module map onto the natural two-dimensional module over
the field `F`; its kernel is fixed pointwise.  The upper-unipotent subgroup is
the literal Sylow subgroup of `SL₂(F)`.  Under these hypotheses the fixed
space is exactly the inverse image of the first coordinate line (the fixed
point calculation used in Lemma 14.7.65), and a marked complement of the
expected dimension gives the direct fixed-space decomposition.

`ModuleCover` constructs the genuine three-dimensional F₄ universal K*-cover
and its surjection onto the original marked U/V₁. It proves the fixed-kernel
dimension bound, the upper four-group's fixed-space/commutator identity, and
the rank-two displacement calculation on that original module.

`SourceEndgame` proves the centralizer step of 14.7.71, the splitting and
fixed-point exclusion of rank-two U₀ after the source generation identities,
and the elementary-quotient, commutator-generation and cover steps in 14.7.73.
Its conditional RuTwo constructor derives the six-dimensional indecomposable
action from the actual section and marked natural projection. The full
14.7.71–74 statements and the remaining local inputs to that constructor
remain obligations of this local analysis. The Ru1 transport retains the
same original quotient marking, and the center/natural Ru2 adapters use
the actual source flag and quotient map; their local premises remain explicit. The earlier critical-pair
and component inputs are owned by qt-14-07; its 14.7.75 assembly must still
discharge all source premises.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, Remark 14.7.64 and Lemma 14.7.65,
printed pp.1069–1070 (PDF pp.1086–1087).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure

open Matrix Matrix.SpecialLinearGroup Representation

variable {F W : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- Lemma 14.7.65: the upper-Sylow fixed space is the inverse image of the
first-coordinate line in the natural quotient. -/
public theorem fixedSpace_upper_unipotent_iff
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w) (w : W) :
    w ∈ Representation.SL2CentralExtension.upperFixed ρ ↔ p w 1 = 0 :=
  Representation.SL2CentralExtension.mem_upperFixed_iff ρ p hp he hk w

/-- The corresponding complement statement used when the marked local module
has the dimension of the defining field. -/
public theorem fixedSpace_upper_unipotent_decomposition
    [FiniteDimensional (ZMod 2) F]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w)
    (V : Submodule (ZMod 2) W)
    (hfix : V ≤ Representation.SL2CentralExtension.upperFixed ρ)
    (hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) F)
    (hdisj : Disjoint V p.ker) :
    Representation.SL2CentralExtension.upperFixed ρ = V ⊔ p.ker :=
  Representation.SL2CentralExtension.upperFixed_decomposition ρ p hp he hk V hfix hdim hdisj

/-- Both clauses of the module calculation in 14.7.65. Here B is the
marked image of L₁, and its commutator generation of V is the earlier natural
L₁-action. The commutator of the whole Sylow fixed space is derived. -/
public theorem fixedSpace_upper_unipotent_and_commutator
    [FiniteDimensional (ZMod 2) F]
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin 2) F) W)
    (p : W →ₗ[ZMod 2] (Fin 2 → F)) (hp : Function.Surjective p)
    (he : ∀ g w, p (ρ g w) = g • p w)
    (hk : ∀ w, p w = 0 → ∀ g, ρ g w = w)
    (B : Subgroup (SpecialLinearGroup (Fin 2) F)) (V : Submodule (ZMod 2) W)
    (hfix : V ≤ Representation.SL2CentralExtension.upperFixed ρ)
    (hdim : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) F)
    (hdisj : Disjoint V p.ker)
    (hgen : Representation.SL2CentralExtension.movedSpace ρ B V = V) :
    Representation.SL2CentralExtension.upperFixed ρ = V ⊔ p.ker ∧
      Representation.SL2CentralExtension.movedSpace ρ B
        (Representation.SL2CentralExtension.upperFixed ρ) = V :=
  Representation.SL2CentralExtension.upperFixed_and_movedSpace
    ρ p hp he hk B V hfix hdim hdisj hgen

end CFSG.Quasithin.Chapter14.Section07.LocalStructure
