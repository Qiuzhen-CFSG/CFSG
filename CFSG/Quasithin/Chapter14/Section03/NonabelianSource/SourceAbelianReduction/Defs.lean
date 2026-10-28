module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Source

/-!
# The two local inputs to the final nonabelian rank-two argument

The first assertion is original 14.3.20 on the elementary factors of the
literal parabolic core. The second is 14.3.21(2), excluding conjugates of
the marked point outside RQ. Neither assertion includes core collapse,
abelianness of the conjugate span, or ambient recognition.

Source: Aschbacher--Smith, Quasithin Groups, printed pp.997--999.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

/-- Self-centralization of each marked elementary factor of the actual R. -/
def FactorSelfCentralizing (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ A : Subgroup G, IsElementaryAbelian 2 A →
    A ≤ (F.I₂ L).pCoreIn 2 → V ≤ A → Nat.card A = 16 →
    Nat.card (A ⊓ F.U : Subgroup G) = 8 →
    F.I₂ L ⊔ F.H.pCoreIn 2 ≤ normalizer (A : Set G) →
    A = centralizer (A : Set G)

/-- Original 14.3.21(2), before substituting Q=U. -/
def OutsidePointNonfusion (F : InvariantFlag T V 2) (L : Subgroup G) : Prop :=
  ∀ z ∈ F.Vi 1, z ≠ 1 → ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
    t ∉ (F.I₂ L).pCoreIn 2 ⊔ F.H.pCoreIn 2 → ¬ IsConj z t

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
