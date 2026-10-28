module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree.BlockStructure
public import Theory.SpecificGroups.PSL3.LinearThreeFlags
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Locals
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.DiagramLocals

/-!
# Local cores and quotient actions in linear-three automorphism extensions

These adapters keep the local blocks from `BlockStructure` inside an actual
subgroup of Aut(PSL₃). Both cores and both SL₂ quotients use the original
matrix projection and the faithful inner embedding. Preservation of the two
geometric parabolic types identifies the diagram kernel with the faithful
linear-field model. At q = 2 this entire kernel is inner, so there is no
proper diagram-trivial extension.

For either local factor, the matrix kernel calculation proves equality
O₂(LᵢS) = O₂(Lᵢ), compared in the common ambient extension. Relative normality
of S in SBⱼ kills its coefficient action and forces innerness on Lⱼ/O₂(Lⱼ).
The final nonbinary theorem combines the actual extension model, both core
equalities and that implication, discharging the geometric coverage and
semilinear formula inputs. It applies in particular to the source's outer
two-group extensions. The parent retains the final amalgam classification
and extension-elimination argument.

Source: Aschbacher–Smith F.1.12, printed pp.263–264 (PDF pp.274–275).
-/

public section
open Matrix
open scoped MatrixGroups
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.OuterExtensions
open Theory.GroupTheory.AutomorphismExtensionBorel
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.OuterExtensions

variable (F : Type*) [Field F]

/-- The linear-field form of the binary collapse, preserved for existing clients. -/
theorem binary_linearField_extension_eq_inner (hF : Nat.card F = 2)
    (E : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)
    (hE : E ≤ Matrix.PSL3.ExtensionBorel.linearField F) :
    E = MulAut.innerSubgroup PSL(3,F) :=
  extension_eq_inner_of_card_two F hF E hinner hE

/-- At q = 2 the actual geometric diagram kernel is the inner subgroup. -/
theorem binary_diagramTrivial_eq_inner [Finite F] (hF : Nat.card F = 2) :
    diagramTrivial F = MulAut.innerSubgroup PSL(3,F) :=
  diagramTrivial_eq_inner_of_card_two F hF

/-- No proper actual diagram-trivial extension exists in the binary case. -/
theorem binary_diagramTrivial_extension_eq_inner [Finite F] (hF : Nat.card F = 2)
    (E : Subgroup (MulAut PSL(3,F))) (hinner : MulAut.innerSubgroup PSL(3,F) ≤ E)
    (hdiagram : E ≤ diagramTrivial F) : E = MulAut.innerSubgroup PSL(3,F) :=
  diagramTrivial_extension_eq_inner_of_card_two F hF E hinner hdiagram

variable [Finite F] [CharP F 2]
variable (E : Subgroup (MulAut PSL(3,F))) (hE : MulAut.innerSubgroup PSL(3,F) ≤ E)

/-- The embedded point-local two-core is the same original root plane. -/
theorem pointLocal_extension_core_coordinates :
    (pCore 2 (localIn F E hE true)).map (localIn F E hE true).subtype =
      ((pointRadical F).map (pointLocal F).subtype).map (innerEmbedding E hE) := by
  rw [local_core_map]
  change ((pCore 2 (pointLocal F)).map (pointLocal F).subtype).map _ = _
  rw [pointLocal_twoCore_eq]

/-- The embedded line-local two-core is the same original root plane. -/
theorem lineLocal_extension_core_coordinates :
    (pCore 2 (localIn F E hE false)).map (localIn F E hE false).subtype =
      ((lineRadical F).map (lineLocal F).subtype).map (innerEmbedding E hE) := by
  rw [local_core_map]
  change ((pCore 2 (lineLocal F)).map (lineLocal F).subtype).map _ = _
  rw [lineLocal_twoCore_eq]

/-- The point quotient in the extension still reads the lower-right matrix block. -/
theorem pointLocal_extension_quotient_matrix (g : pointLocalSL F) :
    (localQuotientEquiv F E hE true (QuotientGroup.mk' _
      (localEquiv F E hE true (pointLocalProjectEquiv F g)))).val =
      !![g.val.val 1 1, g.val.val 1 2; g.val.val 2 1, g.val.val 2 2] := by
  exact (congrArg (fun x : SL(2,F) => x.val)
    (localQuotientEquiv_mk F E hE true (pointLocalProjectEquiv F g))).trans
      (pointLocalCoreQuotientEquiv_project_val F g)

/-- The line quotient in the extension still reads the upper-left matrix block. -/
theorem lineLocal_extension_quotient_matrix (g : lineLocalSL F) :
    (localQuotientEquiv F E hE false (QuotientGroup.mk' _
      (localEquiv F E hE false (lineLocalProjectEquiv F g)))).val =
      !![g.val.val 0 0, g.val.val 0 1; g.val.val 1 0, g.val.val 1 1] := by
  exact (congrArg (fun x : SL(2,F) => x.val)
    (localQuotientEquiv_mk F E hE false (lineLocalProjectEquiv F g))).trans
      (lineLocalCoreQuotientEquiv_project_val F g)

/-- On the same local factors, the actual LᵢS quotient-action kernel is its two-core.
No normality in the full automorphism extension is asserted. -/
theorem local_extension_action_kernel (S : Subgroup E) (point : Bool)
    (hSL : S ≤ Subgroup.normalizer (localIn F E hE point)) (hS : IsPGroup 2 S) :
    (Subgroup.pCoreJoinAction 2 hSL).ker =
      pCore 2 (localIn F E hE point ⊔ S : Subgroup E) :=
  localJoinAction_kernel F E hE S point hSL hS

/-- The two cores in a diagram-trivial extension are equal under the literal
inclusions into E. Normalization is required only for the local join. -/
theorem diagramTrivial_extension_twoCore_eq {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hdiagram : E ≤ diagramTrivial F)
    (S : Subgroup E) (point : Bool)
    (hSL : S ≤ Subgroup.normalizer (localIn F E hE point : Set E)) :
    (pCore 2 (localIn F E hE point ⊔ S : Subgroup E)).map
      (localIn F E hE point ⊔ S).subtype =
      (pCore 2 (localIn F E hE point)).map (localIn F E hE point).subtype :=
  local_join_twoCore_eq F E hE
    (hdiagram.trans_eq (diagramTrivial_eq_linearField F hn hF)) point S hSL

/-- For the actual Sⱼ = S ∩ Lⱼ and Bⱼ = N_{Lⱼ}(Sⱼ), relative normality
S ◁ SBⱼ forces innerness of the original action on Lⱼ/O₂(Lⱼ). -/
theorem diagramTrivial_extension_quotientAction_inner {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hdiagram : E ≤ diagramTrivial F)
    (S : Sylow 2 E) (point : Bool)
    (hSL : (S : Subgroup E) ≤ Subgroup.normalizer (localIn F E hE point : Set E))
    (hnormal : ((S : Subgroup E).subgroupOf ((S : Subgroup E) ⊔
      localBorel F E hE S point)).Normal) :
    ((localQuotientAction F E hE point).comp (Subgroup.inclusion hSL)).range ≤
      MulAut.innerSubgroup (localIn F E hE point ⧸ pCore 2 (localIn F E hE point)) :=
  localQuotientAction_inner_of_normal F E hE
    (hdiagram.trans_eq (diagramTrivial_eq_linearField F hn hF)) S point hSL hnormal

/-- The extended point-local core is the original embedded root plane. -/
theorem pointLocal_diagramTrivial_extension_core {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hdiagram : E ≤ diagramTrivial F)
    (S : Subgroup E)
    (hSL : S ≤ Subgroup.normalizer (localIn F E hE true : Set E)) :
    (pCore 2 (localIn F E hE true ⊔ S : Subgroup E)).map
      (localIn F E hE true ⊔ S).subtype =
      ((pointRadical F).map (pointLocal F).subtype).map (innerEmbedding E hE) := by
  rw [diagramTrivial_extension_twoCore_eq F E hE hn hF hdiagram S true hSL]
  exact pointLocal_extension_core_coordinates F E hE

/-- The extended line-local core is the original embedded root plane. -/
theorem lineLocal_diagramTrivial_extension_core {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hdiagram : E ≤ diagramTrivial F)
    (S : Subgroup E)
    (hSL : S ≤ Subgroup.normalizer (localIn F E hE false : Set E)) :
    (pCore 2 (localIn F E hE false ⊔ S : Subgroup E)).map
      (localIn F E hE false ⊔ S).subtype =
      ((lineRadical F).map (lineLocal F).subtype).map (innerEmbedding E hE) := by
  rw [diagramTrivial_extension_twoCore_eq F E hE hn hF hdiagram S false hSL]
  exact lineLocal_extension_core_coordinates F E hE

/-- The nonbinary outer-extension calculations used on p.264 of F.1.12.
The extension is identified through its actual action; both local core
equalities and the selected inner quotient action have no calculation premises. -/
theorem nonbinary_extension_calculations {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (hdiagram : E ≤ diagramTrivial F)
    (S : Sylow 2 E)
    (hSL : ∀ point, (S : Subgroup E) ≤
      Subgroup.normalizer (localIn F E hE point : Set E))
    (j : Bool) (hnormal : ((S : Subgroup E).subgroupOf ((S : Subgroup E) ⊔
      localBorel F E hE S j)).Normal) :
    (∃ e : E.comap (semilinearAction F) ≃* E,
      ∀ x, (e x).val = semilinearAction F x.val) ∧
    (∀ point, (pCore 2 (localIn F E hE point ⊔ (S : Subgroup E) : Subgroup E)).map
      (localIn F E hE point ⊔ (S : Subgroup E)).subtype =
      (pCore 2 (localIn F E hE point)).map (localIn F E hE point).subtype) ∧
    ((localQuotientAction F E hE j).comp (Subgroup.inclusion (hSL j))).range ≤
      MulAut.innerSubgroup (localIn F E hE j ⧸ pCore 2 (localIn F E hE j)) := by
  have hn0 : 0 < n := lt_trans Nat.zero_lt_one hn
  exact ⟨⟨semilinearExtensionEquiv F hn0 hF E hdiagram,
      semilinearExtensionEquiv_apply F hn0 hF E hdiagram⟩,
    fun point => diagramTrivial_extension_twoCore_eq F E hE hn0 hF hdiagram S point (hSL point),
    diagramTrivial_extension_quotientAction_inner F E hE hn0 hF hdiagram S j (hSL j) hnormal⟩

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.LinearThree.OuterExtensions
