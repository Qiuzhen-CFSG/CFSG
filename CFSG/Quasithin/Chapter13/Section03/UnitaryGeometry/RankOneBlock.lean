module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import Theory.Representation.G2BinaryNondegeneratePlane.Movement

/-!
# The L₂(4)-block contradiction in the unitary geometry

The perpendicular E₁₆ is centralized by the component's Sylow two-subgroup.
The actual cubic marking shows that it has no fixed points there, so it misses
the component center and injects into the literal block module. A Sylow fixes
only four vectors in the defining L₂(4) module, contradicting its order sixteen.

This is the final rank-one alternative in Aschbacher–Smith, Lemma13.3.12,
printed p.890. Placement inside U(K), the Sylow intersection and the original
G₂ chart remain the earlier source data; no chief-count conclusion is used.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterC

theorem not_L2Four_block_of_fixed_sixteen
    {L : Type*} [Group L] [Finite L] (hL : IsL2EvenBlock L 2)
    (P : Sylow 2 L) (E : Subgroup L) (hE : E≤blockU L)
    (hEP : E≤centralizer (P:Set L)) (hcard : Nat.card E=16)
    (a : L) (hfix : ∀e∈E,Commute a e→e=1) : False := by
  have hd : Disjoint E (center L) := by
    rw [disjoint_def]
    intro e he hz
    exact hfix e he (mem_center_iff.mp hz a)
  have hb := hL.card_le_of_sylow_fixed_disjoint_center P E hE hEP hd
  rw [hcard] at hb
  norm_num at hb

/-- The literal perpendicular-space marking supplies the fixed-point-free cubic
needed to exclude the rank-one block in 13.3.12. -/
theorem not_L2Four_block_of_perpendicular_marking
    {L : Type*} [Group L] [Finite L] (hL : IsL2EvenBlock L 2)
    (P : Sylow 2 L) (E : Subgroup L) (hE : E≤blockU L)
    (hEP : E≤centralizer (P:Set L))
    (e : E ≃* Multiplicative (Atlas.G2.Natural.BinaryNondegeneratePlane.form.orthogonal
      Atlas.G2.Natural.BinaryNondegeneratePlane.plane))
    (a : L) (ha : a∈normalizer (E:Set L))
    (he : ∀x:E,((e (E.normalizerMonoidHom ⟨a,ha⟩ x)).toAdd : Atlas.G2.Natural.BinaryNondegeneratePlane.W)=
      Atlas.G2.Natural.BinaryNondegeneratePlane.rho Atlas.G2.Natural.BinaryNondegeneratePlane.cubic
        ((e x).toAdd : Atlas.G2.Natural.BinaryNondegeneratePlane.W)) : False := by
  have hcard : Nat.card E=16 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Atlas.G2.Natural.BinaryNondegeneratePlane.form.orthogonal
      Atlas.G2.Natural.BinaryNondegeneratePlane.plane)=16
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2),Nat.card_zmod,
      Atlas.G2.Natural.BinaryNondegeneratePlane.finrank_orthogonal]
    decide
  apply not_L2Four_block_of_fixed_sixteen hL P E hE hEP hcard a
  intro x hx hax
  let y : E := ⟨x,hx⟩
  have hconj : E.normalizerMonoidHom ⟨a,ha⟩ y=y := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    change a*x*a⁻¹=x
    rw [hax.eq,mul_inv_cancel_right]
  have hxy := he y
  rw [hconj] at hxy
  have hp := (Atlas.G2.Natural.BinaryNondegeneratePlane.mem_plane _).mp
    ((Atlas.G2.Natural.BinaryNondegeneratePlane.cubic_fixed_iff _).mp hxy.symm)
  have ho := (Atlas.G2.Natural.BinaryNondegeneratePlane.mem_orthogonal _).mp (e y).toAdd.property
  have hz : ((e y).toAdd : Atlas.G2.Natural.BinaryNondegeneratePlane.W)=0 := by
    ext i
    fin_cases i <;> simp [hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,ho.1,ho.2]
  have hy : e y=1 := Multiplicative.toAdd.injective (Subtype.ext hz)
  exact congrArg Subtype.val (e.injective (hy.trans (map_one e).symm))
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
