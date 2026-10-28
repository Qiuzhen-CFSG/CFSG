module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import Theory.GroupTheory.PResidual.FrattiniControl
public import CFSG.Quasithin.ChapterC.Section01.BlockBasics

/-!
# Whole-core structure in the Frattini-small MS93 branch

For the original normal two-perfect component K, a Frattini-small ambient
commutator equals the moving part of Ω₁(Z(O₂(H))). The intrinsic core of K
is therefore elementary and central in O₂(K). This proves the structural
first branch of MS93 (3.6) before natural-module recognition; the other
branch and the bound on critical distance remain separate source arguments.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), first paragraph, p.870.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.MSCentralOrbit
variable {H : Type*} [Group H] [Finite H]

/-- The Frattini-small branch identifies the whole intrinsic core and proves
both central elementary clauses of the short-group definition. -/
theorem intrinsic_core_of_frattini_small (K : Subgroup H) [K.Normal]
    (hperfect : IsPPerfect 2 K)
    (hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    (blockU K).map K.subtype = ⁅omegaCenterIn (pCore 2 H),K⁆ ∧
      IsElementaryAbelian 2 (blockU K) ∧
      blockU K ≤ centralizer (pCore 2 K : Set K) := by
  have hXQ : omegaCenterIn (pCore 2 H) ≤ pCore 2 H := by
    intro x hx
    exact ((mem_omegaCenterIn_iff _ _).mp hx).1
  have he : (blockU K).map K.subtype = ⁅omegaCenterIn (pCore 2 H),K⁆ :=
    (commutatorCore_eq_intrinsic K hperfect).symm.trans
      (commutator_eq_of_le_frattini_sup_of_isPPerfect (pCore 2 H) K
        (omegaCenterIn (pCore 2 H)) pCore_isPGroup hperfect hXQ hsmall)
  have hUX : (blockU K).map K.subtype ≤ omegaCenterIn (pCore 2 H) := by
    rw [he]
    exact commutator_le_left _ _
  have helem : IsElementaryAbelian 2 (blockU K) := by
    let i : blockU K →* omegaCenterIn (pCore 2 H) := {
      toFun x := ⟨x.val.val,hUX (mem_map_of_mem K.subtype x.property)⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact IsElementaryAbelian.of_injective i (fun _ _ h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : omegaCenterIn (pCore 2 H) => (z : H)) h)))
  refine ⟨he,helem,?_⟩
  have hQKQ : (pCore 2 K).map K.subtype ≤ pCore 2 H :=
    le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
  intro u hu y hy
  have hx := (mem_omegaCenterIn_iff _ _).mp
    (hUX (mem_map_of_mem K.subtype hu))
  apply Subtype.ext
  exact hx.2.1 y (hQKQ (mem_map_of_mem K.subtype hy))

end CFSG.Quasithin.ChapterC.MSCentralOrbit
