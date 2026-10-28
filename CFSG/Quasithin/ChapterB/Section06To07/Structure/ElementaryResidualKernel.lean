module
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.Solvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.Frattini.PGroup

/-!
# The canonical minimal-parabolic core is a reduced elementary-residual kernel

A nontrivial core-free quotient has kernel in the original canonical core.
The core descends to the quotient's canonical core. B.6.8 identifies its
image over O₂ with the Frattini subgroup of the quotient residual. An
elementary residual has trivial Frattini subgroup, so the quotient core is
trivial and the original core is precisely the supplied kernel.

Source: the first step of Aschbacher–Smith13.2.9, printedp.880.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]

/-- The original core equals the kernel of a nontrivial reduced elementary-residual image. -/
theorem minimalParabolic_core_eq_kernel_of_elementary_residual
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (q : G →* D) (hq : Function.Surjective q) (hcore : pCore 2 D = ⊥)
    (hne : q.ker ≠ ⊤) (hs : Group.IsSolvable D)
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p (pResidual 2 D)] :
    minimalParabolicCore T hP = q.ker := by
  obtain ⟨hk,hP'⟩ := minimalParabolic_reduced_image T hP q hq hcore hne
  let S := T.mapSurjective hq
  let π := QuotientGroup.mk' (pCore 2 D)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hiπ : Function.Injective π := by
    apply (MonoidHom.ker_eq_bot_iff π).mp
    rw [QuotientGroup.ker_mk',hcore]
  have hm := map_pResidual_of_surjective 2 π hπ
  let : IsElementaryAbelian p ((pResidual 2 D).map π) := IsElementaryAbelian.map π
  let : IsElementaryAbelian p (pResidual 2 (D ⧸ pCore 2 D)) := hm ▸ inferInstance
  let : Fact (IsPGroup p (pResidual 2 (D ⧸ pCore 2 D))) :=
    ⟨IsElementaryAbelian.isPGroup p _⟩
  obtain ⟨r,_,_,hr,_,hF,_⟩ := minimalParabolic_solvable_structure S hP' hs
  have hJ : minimalParabolicCore S hP' = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ hiπ).mp
    change minimalParabolicCoreImage S hP' = ⊥
    rw [hF,← hr,frattiniAmbient,frattini_eq_bot_of_isElementaryAbelian (p := p) (R := pResidual 2 (D ⧸ pCore 2 D)),Subgroup.map_bot]
  apply le_antisymm ?_ hk
  have hmap := minimalParabolicCore_map_core T hP q hq hk
  rw [hJ] at hmap
  exact (Subgroup.map_eq_bot_iff _).mp hmap

end CFSG.Quasithin.ChapterB
