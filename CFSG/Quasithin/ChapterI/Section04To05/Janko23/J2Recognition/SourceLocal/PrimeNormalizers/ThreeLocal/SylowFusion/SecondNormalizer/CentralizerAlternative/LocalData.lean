module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.Quotient

/-!
# Local computations needed before recognizing the cubic quotient

For M = C_G(⟨y⟩), the selected geometry is intended to show that the
actual root four-group is Sylow in M, that its involutions fuse in M,
and that their M-centralizers have order twelve and exponent dividing six.
Sylow conjugacy then reaches every involution of M.

This record states those concrete local computations. It does not assert
their existence or either centralizer alternative. Its consumer descends
the full involution geometry to M/⟨y⟩ before applying recognition.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262;
*Finite Group Theory*, second edition, Exercise 16.6, pp.266–267.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- Pre-recognition geometry inside the literal cubic centralizer. In particular,
`involutions_conjugate` quantifies over all its involutions. -/
structure CubicLocalGeometry (S : InvolutionGeometry.SelectedGeometry D) (y : G) where
  root_sylow : ∃ P : Sylow 2 (cubicCentralizer y), (P : Subgroup _) = centralizerRoot S y
  u : cubicCentralizer y
  u_mem_root : u ∈ centralizerRoot S y
  u_order : orderOf u = 2
  centralizer_card : Nat.card (centralizer ({u} : Set (cubicCentralizer y))) = 12
  centralizer_pow : ∀ x : centralizer ({u} : Set (cubicCentralizer y)), x ^ 6 = 1
  involutions_conjugate : ∀ x : cubicCentralizer y, orderOf x = 2 → IsConj x u

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
