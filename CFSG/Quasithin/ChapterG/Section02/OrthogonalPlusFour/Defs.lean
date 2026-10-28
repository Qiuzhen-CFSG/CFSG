module

public import CFSG.Quasithin.ChapterG.Section02.CentralClosure

/-!
# The distinct middle layer in the plus-four almost-special argument

The replacement for irreducibility is precisely the four conclusions of
G.2.2. The middle layer is V_L(U ∩ Uᵍ), rather than U ∩ Uᵍ as in G.2.3.
All quotient images below use intersections with S; in particular their
definitions do not impose the generally false containment S₂ ≤ W.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.6, printed p.336, PDF p.347.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
variable {G : Type*} [Group G]

/-- Exactly the conclusions replacing irreducibility in G.2.6. -/
structure ClosureConclusions (D : Setup G) : Prop where
  central : D.tilde D.V ≤ D.tilde D.U ∧
    D.tilde D.U ≤ omegaOneAmbient ((center (D.tilde D.QH)).map (D.tilde D.QH).subtype)
  frattini : (frattini D.U).map D.U.subtype ≤ D.V₁
  normal : D.U ≤ D.T ∧ (D.U.subgroupOf D.T).Normal
  reduced : IsPReduced 2 ((D.tilde D.U).subgroupOf (D.tilde D.H))

/-- The genuine G.2.2 theorem supplies these conclusions whenever its
original irreducibility hypothesis is available. -/
theorem closureConclusions_of_hypothesis [Finite G] {D : Setup G} (h : D.Hypothesis) :
    ClosureConclusions D :=
  ⟨h.tilde_U_central, h.frattini_U_le_point, h.U_normal_in_T, h.tilde_U_reduced⟩

/-- The middle term specific to G.2.6. -/
def S₂ (D : Setup G) (g : G) : Subgroup G := D.VL ⊔ D.S₂ g

/-- The proposed core product, initially a generated subgroup. -/
def coreProduct (D : Setup G) (g : G) : Subgroup G :=
  D.W g ⊔ Setup.conjugate (D.W g) g

abbrev Quotient (D : Setup G) (g : G) :=
  D.S g ⧸ (S₂ D g).subgroupOf (D.S g)

/-- W/S₂ in the source means this quotient image, not a quotient of W
by a subgroup already known to lie in W. -/
def quotientImage (D : Setup G) (g : G)
    [((S₂ D g).subgroupOf (D.S g)).Normal] (A : Subgroup G) :
    Subgroup (Quotient D g) :=
  (A.subgroupOf (D.S g)).map (QuotientGroup.mk' ((S₂ D g).subgroupOf (D.S g)))

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
