module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.Reduction
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered.Transport
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Derived
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CentralCover

/-!
# Two-closure and abelian quotient of the original covered symplectic Borel

The determinant characters prove two-closure of the literal derived Borel.
Normal Sylow subgroups lift through central kernels, so the Borel preimage in
the component of X/O₂(X) is also two-closed. The two-group kernel of the map
from the original overlap preserves its quotient by the two-core. This proves
the odd-index clause on the original overlap without any extra hypothesis.

The intrinsic central-cover calculation uses a Weyl reflection to put the
commutator of the two lifted torus generators in the two-core. Applied to the
actual component in X/O₂(X), it proves abelianness of the central Borel quotient.
The same two-group-kernel transport gives `symplectic_coveredBorel` on the
original overlap. Its application to `hallControl_of_coveredBorel` supplies
solvability, abelian odd Hall subgroups and the Sylow Frattini factorization.
The two quotients X/O₂(X) and X/J remain distinct throughout.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, E.2.2(2b), pp.215--216,
and the Borel calculation and Frattini argument in 4.4.13, pp.623--624.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall
open ChapterB SymplecticCovered
variable {X : Type*} [Group X] [Finite X]
variable {F : Type*} [Field F] [Finite F]

/-- The actual Borel preimage in the component of X/O₂(X) is two-closed. -/
theorem symplectic_centralBorel_odd_index
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {n : ℕ}
    (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F) :
    Odd (pCore 2 ((sp4DerivedBorel F).comap (actorToModel S hP e))).index := by
  exact OddHall.odd_pCore_index_comap_of_central_kernel (actorToModel S hP e)
    (actorToModel_surjective S hP e) (actorToModel_central S hP hc e)
    (sp4DerivedBorel F)
    (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.derivedBorel_twoClosed hF).odd_index

/-- The original covered overlap has a normal Sylow two-subgroup. -/
theorem symplectic_coveredBorel_odd_index
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {n : ℕ}
    (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) :
    Odd (pCore 2 (K.subgroupOf (minimalParabolicMax S hP))).index := by
  let q := (overlapToCover S hP e he).pCoreQuotientEquiv
    (overlapToCover_surjective S hP e he) (overlapToCover_kernel_two S hP e he)
  rw [index_eq_card, Nat.card_congr q.toEquiv, ← index_eq_card]
  exact symplectic_centralBorel_odd_index S hP hc hF e

/-- Abelianness of the central Borel quotient supplies the remaining covered-Borel clause. -/
theorem symplectic_coveredBorel_of_abelian_centralBorel
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {n : ℕ}
    (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F)
    (ha : IsMulCommutative
      (((sp4DerivedBorel F).comap (actorToModel S hP e)) ⧸
        pCore 2 ((sp4DerivedBorel F).comap (actorToModel S hP e)))) :
    CoveredBorelControl S hP K := by
  exact OddHall.TwoClosedAbelianQuotient.of_surjective_two_kernel
    (overlapToCover S hP e he) (overlapToCover_surjective S hP e he)
    (overlapToCover_kernel_two S hP e he)
    ⟨symplectic_centralBorel_odd_index S hP hc hF e, ha⟩

/-- Apply the same original marking and source clauses to the Hall-control reduction. -/
theorem symplectic_hallControl_of_abelian_centralBorel
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses (minimalParabolicMax S hP) K S)
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F)
    (ha : IsMulCommutative
      (((sp4DerivedBorel F).comap (actorToModel S hP e)) ⧸
        pCore 2 ((sp4DerivedBorel F).comap (actorToModel S hP e)))) :
    HallControl S hP :=
  hallControl_of_coveredBorel S hP hK hc
    (symplectic_coveredBorel_of_abelian_centralBorel S hP hc hF e he ha)

variable [CharP F 2]

/-- The source central kernel and the intrinsic symplectic calculation discharge
the abelianness premise on the actual component in X/O₂(X). -/
theorem symplectic_centralBorel_abelian
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F) :
    IsMulCommutative
      (((sp4DerivedBorel F).comap (actorToModel S hP e)) ⧸
        pCore 2 ((sp4DerivedBorel F).comap (actorToModel S hP e))) := by
  exact Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.central_preimage_quotient_abelian
    hn hF (actorToModel S hP e) (actorToModel_surjective S hP e)
    (actorToModel_central S hP hc e)

/-- The original covered Borel is two-closed with abelian odd quotient.
The literal derived carrier, Borel marking and source central kernel suffice. -/
theorem symplectic_coveredBorel
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hc : SingleClauses (minimalParabolicMax S hP) K S) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) :
    CoveredBorelControl S hP K :=
  symplectic_coveredBorel_of_abelian_centralBorel S hP hc hF e he
    (symplectic_centralBorel_abelian S hP hc hn hF e)

/-- Hall control in the derived symplectic branch, with the central-cover
premise discharged on the same source component and original Borel marking. -/
theorem symplectic_hallControl
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) {K : Subgroup X}
    (hK : K.IsCComponent) (hc : SingleClauses (minimalParabolicMax S hP) K S)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : sourceImage (minimalParabolicMax S hP) K ≃* Sp4Derived F)
    (he : (componentOverlap (minimalParabolicMax S hP) K).map e.toMonoidHom =
      sp4DerivedBorel F) :
    HallControl S hP :=
  hallControl_of_coveredBorel S hP hK hc
    (symplectic_coveredBorel S hP hc hn hF e he)

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall
