module

public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.CoreCalculation
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.NormalSylow

/-!+# Semilinear models and local actions for the actual diagram kernel

The faithful semilinear action has image the geometrically defined diagram
kernel. Restricting that same action identifies every subgroup of the kernel
with its inverse image in the semilinear group; the equivalence evaluates to
the original automorphism, so it also covers the actual intermediate outer
extensions of PSL₃.

The matrix calculation supplies the coefficient formula required by the
normal-Sylow argument. Consequently relative normality of S in SBⱼ forces
innerness on the literal local core quotient without any additional action
formula premise. The Chapter F consumer supplies linear-field containment
from preservation of the geometric diagram types and combines this with
the two-core calculation.

Source: Aschbacher–Smith F.1.12, printed pp.263–264 (PDF pp.274–275).
-/

public section
open scoped MatrixGroups
open Matrix
namespace Matrix.PSL3.LinearThree.OuterExtensions

variable (F : Type*) [Field F] [Finite F]

/-- The faithful model's image is exactly the intrinsic geometric diagram kernel. -/
theorem semilinearAction_range_eq_diagramTrivial {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    (semilinearAction F).range = diagramTrivial F := by
  rw [semilinearAction_range, diagramTrivial_eq_linearField F hn hF]

variable [CharP F 2]

/-- Restrict the faithful action to the inverse image of the actual extension.
Its exposed body retains the literal action map as the forward inclusion. -/
@[expose] noncomputable def semilinearExtensionEquiv {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (MulAut PSL(3,F))) (hdiagram : E ≤ diagramTrivial F) :
    E.comap (semilinearAction F) ≃* E :=
  ((E.comap (semilinearAction F)).equivMapOfInjective
    (semilinearAction F) (semilinearAction_injective F)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self
        (hdiagram.trans_eq (semilinearAction_range_eq_diagramTrivial F hn hF).symm)))

/-- The model equivalence induces the original ambient automorphism. -/
theorem semilinearExtensionEquiv_apply {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (E : Subgroup (MulAut PSL(3,F))) (hdiagram : E ≤ diagramTrivial F)
    (x : E.comap (semilinearAction F)) :
    (semilinearExtensionEquiv F hn hF E hdiagram x).val =
      semilinearAction F x.val := rfl

variable (E : Subgroup (MulAut PSL(3,F)))
    (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)

/-- The actual local matrix calculation discharges the normal-Sylow input,
using the field coefficient of the same original ambient actor. -/
theorem hasLocalActorFormula (hlinear : E ≤ ExtensionBorel.linearField F)
    (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ Subgroup.normalizer (localIn F E hinner point : Set E)) :
    NormalSylow.HasLocalActorFormula F E hinner hlinear S point hSL := by
  intro s
  exact localBlockAction_semilinear F E hinner hlinear point ⟨s, hSL s.property⟩

/-- Relative normality in SBⱼ forces innerness on the actual local core quotient.
The semilinear action formula is proved, not an additional hypothesis. -/
theorem localQuotientAction_inner_of_normal
    (hlinear : E ≤ ExtensionBorel.linearField F) (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ Subgroup.normalizer (localIn F E hinner point : Set E))
    (hnormal : ((S : Subgroup E).subgroupOf ((S : Subgroup E) ⊔
      localBorel F E hinner S point)).Normal) :
    ((localQuotientAction F E hinner point).comp (Subgroup.inclusion hSL)).range ≤
      MulAut.innerSubgroup (localIn F E hinner point ⧸ pCore 2 (localIn F E hinner point)) :=
  NormalSylow.localQuotientAction_inner_of_normal F E hinner hlinear S point hSL hnormal
    (hasLocalActorFormula F E hinner hlinear S point hSL)

end Matrix.PSL3.LinearThree.OuterExtensions
