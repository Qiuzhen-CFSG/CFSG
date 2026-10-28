module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.Action
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Complement
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Conjugator
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Transport

/-!
# Ambient preparation for weak closure in the PGL₂ shadow

The opening reduction constructs the genuine model preimage R₀, uses pair
fixed-subgroup generation to eliminate it, and chooses a new Sylow subgroup
without changing z, r, L, R or g. The resulting E is elementary of order four
and T_E is Sylow in C_G(E). Correcting g retains K′ and L′ and proves
that the actual marked elements satisfy g*z*g⁻¹ = r. Weak closure, once
established, transports along this same conjugation.

The index, exclusion and generation premises concern the actual transported
PSL₂ action. `Complement` identifies the source inner preimage and defines
the natural S₆ preimage through a genuine PSL₂–A₆ equivalence.

The marked Sylow geometry, weak-closure contradiction and symmetric marked
transvections remain to be constructed before the conditional helper requested
in Lemma 16.4.6 is complete. The records in `Configuration` describe those
outputs; no projection is offered as a proof of those source assertions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed pp.1184–1185. Left conjugation is used throughout.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup GorensteinWalter

variable {G F : Type*} [Group G] [Finite G] [Field F]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The opening source deductions, with only intrinsic action calculations
and the earlier noncontainment conclusion as extra premises. -/
theorem opening_reduction (h : IntersectionSetup T z L g R)
    (hnot : ¬ L ≤ normalizer ((centralizer (L : Set G)).conjBy g : Set G))
    (hr : r ∈ R) (hr2 : orderOf r = 2) (e : L ≃* PSL2 F)
    (M : Subgroup (MulAut (PSL2 F))) (hM : M.index = 2)
    (hout : modelAction h e ⟨r, hr⟩ ∉ M)
    (hgen : ∀ b : MulAut (PSL2 F), b ∈ M → orderOf b = 2 →
      (MulAut.congr e (involutionAction h hr)).fixedSubgroup ⊔ b.fixedSubgroup = ⊤) :
    R = zpowers r ∧ Nat.card R = 2 ∧
    ∃ S : Sylow 2 G, IntersectionSetup S z L g R ∧
      SylowIn ((S : Subgroup G) ⊓ normalizer (R : Set G))
        (normalizer (L : Set G) ⊓ normalizer (R : Set G)) ∧
      IsElementaryAbelian 2 (involutionPair z r) ∧ Nat.card (involutionPair z r) = 4 ∧
      SylowIn (commonCentralizer (S : Subgroup G) z r)
        (centralizer (involutionPair z r : Set G)) := by
  obtain ⟨hR, hcard⟩ := eq_zpowers_of_index_two_model h hnot hr hr2 e M hM hout hgen
    h.normalizer_structure.2.2.2
  obtain ⟨S, hS, hn, _⟩ := exists_normalizer_sylow h hcard
  exact ⟨hR, hcard, S, hS, hn, involutionPair_elementary hS hr hr2,
    involutionPair_card hS hr hr2, commonCentralizer_sylow hS hR hn⟩

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
