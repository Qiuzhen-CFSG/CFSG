module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.CubicImage
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Inputs

/-!
# The actual cubic residual quotient in the marked A₅ module

Restricting the marking to O²(C_L(v)) gives exactly the cubic image. The
original action-kernel identity makes the restricted kernel a two-group;
its odd image kills the whole two-core, proving equality of these kernels.
The resulting explicit quotient isomorphism gives order three. The displayed
cubic fixes a, and the marking supplies its ambient conjugator from z.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926,
with the binary permutation-module conventions of §B.3.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] {L V : Subgroup G} (s : Marking L V)

theorem residual_le_L : Lv L (markedV s) ≤ L := by
  rintro x ⟨d, hd, rfl⟩
  exact d.property.1

def residualAction : Lv L (markedV s) →* alternatingGroup (Fin 5) :=
  s.action.comp (inclusion (residual_le_L s))

theorem residualAction_mem_cubic (x : Lv L (markedV s)) :
    residualAction s x ∈ ResidualCoordinates.cubicGroup := by
  obtain ⟨d, hd, he⟩ := x.property
  let f : ↥(L ⊓ Gv (markedV s)) →* ResidualCoordinates.stabilizer :=
    (s.action.comp (inclusion inf_le_left)).codRestrict _ (stabilizer_fixes_v s)
  have hh := ResidualCoordinates.residual_le_cubic
    (map_pResidual_le 2 f (mem_map.mpr ⟨d, hd, rfl⟩))
  have hx : residualAction s x = (f d).val := by
    apply congrArg s.action
    exact Subtype.ext he.symm
  rw [hx]
  exact hh

variable [Finite G]

theorem residualAction_range : (residualAction s).range = ResidualCoordinates.cubicGroup := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact residualAction_mem_cubic s x
  · rw [ResidualCoordinates.cubicGroup_eq_zpowers]
    apply zpowers_le.mpr
    obtain ⟨d, hd, he⟩ := exists_residual_cubic s
    exact ⟨⟨d, ⟨d, hd, rfl⟩⟩, he⟩

noncomputable def residualCubicAction : Lv L (markedV s) →* ResidualCoordinates.cubicGroup :=
  (residualAction s).codRestrict _ (residualAction_mem_cubic s)

theorem residualCubicAction_surjective : Function.Surjective (residualCubicAction s) := by
  intro g
  have hg : g.val ∈ (residualAction s).range := by
    rw [residualAction_range s]
    exact g.property
  obtain ⟨x, hx⟩ := hg
  exact ⟨x, Subtype.ext hx⟩

omit [Finite G] in
theorem residualAction_kernel (hk : s.action.ker = pCore 2 L) :
    (residualAction s).ker = pCore 2 (Lv L (markedV s)) := by
  apply le_antisymm
  · have hp : IsPGroup 2 (residualAction s).ker := by
      change IsPGroup 2 (s.action.ker.comap (inclusion (residual_le_L s)))
      rw [hk]
      exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
    exact le_sSup ⟨inferInstance, hp⟩
  · intro x hx
    have h3 : IsPGroup 3 ResidualCoordinates.cubicGroup :=
      IsPGroup.of_card (n := 1) ResidualCoordinates.cubicGroup_card
    have hd := (pCore_isPGroup.map (residualAction s)).disjoint_of_coprime h3
      (by decide : Nat.Coprime 2 3)
    exact disjoint_def.mp hd (mem_map.mpr ⟨x, hx, rfl⟩) (residualAction_mem_cubic s x)

omit [Finite G] in
theorem residualCubicAction_kernel (hk : s.action.ker = pCore 2 L) :
    (residualCubicAction s).ker = pCore 2 (Lv L (markedV s)) := by
  rw [← residualAction_kernel s hk]
  ext x
  change (⟨residualAction s x, _⟩ : ResidualCoordinates.cubicGroup) = 1 ↔ residualAction s x = 1
  exact Subtype.ext_iff

noncomputable def residualQuotientEquiv (hk : s.action.ker = pCore 2 L) :
    Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s)) ≃* ResidualCoordinates.cubicGroup :=
  (QuotientGroup.quotientMulEquivOfEq (residualCubicAction_kernel s hk).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residualCubicAction_surjective s))

theorem residualQuotient_card (hk : s.action.ker = pCore 2 L) :
    Nat.card (Lv L (markedV s) ⧸ pCore 2 (Lv L (markedV s))) = 3 := by
  rw [Nat.card_congr (residualQuotientEquiv s hk).toEquiv]
  exact ResidualCoordinates.cubicGroup_card

omit [Finite G] in
theorem markedA_mem_centralizer : markedA s ∈ V ⊓ centralizer (Lv L (markedV s) : Set G) := by
  refine ⟨map_mem s _, mem_centralizer_iff.mpr ?_⟩
  intro c hc
  have he := s.equivariant (inclusion (residual_le_L s) ⟨c, hc⟩) a
  have ha := ResidualCoordinates.cubic_fixes_a (residualCubicAction s ⟨c, hc⟩)
  change act (residualAction s ⟨c, hc⟩) a = a at ha
  change MulAut.conj c (markedA s) =
    s.map (Multiplicative.ofAdd (act (residualAction s ⟨c, hc⟩) a)) at he
  rw [ha] at he
  exact mul_inv_eq_iff_eq_mul.mp he

omit [Finite G] in
theorem markedA_conjugate_and_centralizes :
    (∃ c : G, MulAut.conj c (markedZ s) = markedA s) ∧
      markedA s ∈ V ⊓ centralizer (Lv L (markedV s) : Set G) := by
  obtain ⟨c, _, hc⟩ := exists_a_conjugator s
  exact ⟨⟨c, hc⟩, markedA_mem_centralizer s⟩

/-- Application to the literal module and action kernel of every marked flag. -/
theorem FlagMarking.residualQuotient_card {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (f : FlagMarking T L V V₁ V₂) :
    Nat.card (Lv L (markedV f.module) ⧸ pCore 2 (Lv L (markedV f.module))) = 3 :=
  A5Module.residualQuotient_card f.module f.action_kernel

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
