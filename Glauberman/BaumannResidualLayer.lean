module
public import Glauberman.BaumannRankOneGeneration
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.AbelianSupplementIntersection

/-!
# The residual omega layer in a normally generating Baumann group

Let Z be the central omega of the ordinary, all-abelian Thompson subgroup
of a Sylow two-subgroup. Suppose the Baumann subgroup normally generates
the group and ZU is an elementary normal layer whose residual displacement
lies in U. Two-perfect commutator idempotence identifies that displacement
with D = [U,O²(G)]. The smaller layer ZD is normal and contains the full
normal closure of Z. Independently, that closure is Z times its own
residual commutator; no fixed central subgroup is discarded.

Two opposite Baumann conjugates have central omega intersection Z intersect
Z(G). If the core centralizes D and the two corresponding fixed parts span
D, abelian supplement intersection splits Z into its central part and its
intersection with D. This puts the whole core in the Baumann subgroup and
proves that Baumann is the Sylow subgroup.

Source: the Baumann argument invoked in MS93 (5.1), printed p.913; compare
Stellmacher (1997), (2.3), p.20. The latter uses elementary Thompson groups,
whereas every theorem here retains the original all-abelian convention.
The actual original-degree application is CriticalReduction.RootProductResidualLayer.
The core-centralization and spanning premises in the final criterion remain
separate mathematical obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect group moves an elementary extension only through the moved
part of its prescribed lower layer. -/
theorem residual_layer_eq
    (W U : Subgroup G) [W.Normal] [U.Normal] [IsElementaryAbelian 2 W]
    (hUW : U ≤ W) (hmove : ⁅W,pResidual 2 G⁆ ≤ U) :
    ⁅W,pResidual 2 G⁆ = ⁅U,pResidual 2 G⁆ := by
  apply le_antisymm ?_ (commutator_mono hUW le_rfl)
  rw [←commutator_isPPerfect_idempotent (pResidual 2 G) W
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 W) le_normalizer_of_normal]
  exact commutator_mono hmove le_rfl

/-- The original central omega has a normal enlargement by the residual
commutator of U; the entire fixed part is retained in the omega subgroup. -/
theorem baumann_residual_enlargement
    (S : Sylow 2 G) (U : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ U : Subgroup G)]
    [(omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ U : Subgroup G).Normal]
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤)
    (hmove : ⁅omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ U,
      pResidual 2 G⁆ ≤ U) :
    let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
    let D := ⁅U,pResidual 2 G⁆
    ⁅Z ⊔ U,pResidual 2 G⁆ = D ∧
    (Z ⊔ D).Normal ∧ IsElementaryAbelian 2 (Z ⊔ D : Subgroup G) ∧
    normalClosure (Z : Set G) ≤ Z ⊔ D := by
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  let D := ⁅U,pResidual 2 G⁆
  have he : ⁅Z ⊔ U,pResidual 2 G⁆ = D :=
    residual_layer_eq (Z ⊔ U) U le_sup_right hmove
  have hDU : D ≤ U := commutator_le_left _ _
  have hn : (Z ⊔ D).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←baumann_residual_supplement_of_normalClosure_top S hgen]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_left.mpr
      exact ((commutator_mono (sup_le_sup_left hDU Z) le_rfl).trans_eq he).trans le_sup_right
    · exact (le_inf
        ((show baumannSubgroup (S : Subgroup G) ≤ centralizer (Z : Set G) from inf_le_right).trans
          (Subgroup.centralizer_le_normalizer _))
        (show baumannSubgroup (S : Subgroup G) ≤ normalizer (D : Set G) from
          le_normalizer_of_normal)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : (Z ⊔ D).Normal := hn
  exact ⟨he,hn,IsElementaryAbelian.of_le (sup_le_sup_left hDU Z),
    normalClosure_le_normal (show Z ≤ Z ⊔ D from le_sup_left)⟩

/-- Normal generation by Baumann expresses the full Thompson omega closure
as the original omega times its own residual commutator. -/
theorem baumann_omega_closure_eq_sup_residual
    (S : Sylow 2 G)
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤) :
    let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
    let C := normalClosure (Z : Set G)
    C = Z ⊔ ⁅C,pResidual 2 G⁆ := by
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  let C := normalClosure (Z : Set G)
  let D := ⁅C,pResidual 2 G⁆
  have hZC : Z ≤ C := le_normalClosure
  have hDC : D ≤ C := commutator_le_left _ _
  let : (Z ⊔ D).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←baumann_residual_supplement_of_normalClosure_top S hgen]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_left.mpr
      exact (commutator_mono (sup_le hZC hDC) le_rfl).trans le_sup_right
    · exact (le_inf
        ((show baumannSubgroup (S : Subgroup G) ≤ centralizer (Z : Set G) from inf_le_right).trans
          (Subgroup.centralizer_le_normalizer _))
        (show baumannSubgroup (S : Subgroup G) ≤ normalizer (D : Set G) from
          le_normalizer_of_normal)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact le_antisymm (normalClosure_le_normal (show Z ≤ Z ⊔ D from le_sup_left))
    (sup_le hZC hDC)

omit [Finite G] in
/-- Opposite fixed spaces in the residual layer finish the Baumann Sylow
step, retaining the whole core and the full central omega intersection. -/
theorem baumann_eq_sylow_of_residual_fixed_span
    (S : Sylow 2 G) (D : Subgroup G)
    [IsElementaryAbelian 2
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ D : Subgroup G)]
    [(omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊔ D : Subgroup G).Normal]
    [D.Normal]
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤)
    (hsupp : baumannSubgroup (S : Subgroup G) ⊔ pCore 2 G = (S : Subgroup G))
    (hcore : D ≤ centralizer (pCore 2 G : Set G))
    (x : G)
    (hopp : (baumannSubgroup (S : Subgroup G) ⊔
      (baumannSubgroup (S : Subgroup G)).map (MulAut.conj x).toMonoidHom) ⊔ pCore 2 G = ⊤)
    (hspan : D ≤
      (D ⊓ omegaCenterIn (thompsonSubgroup (S : Subgroup G))) ⊔
      (D ⊓ (omegaCenterIn (thompsonSubgroup (S : Subgroup G))).map
        (MulAut.conj x).toMonoidHom)) :
    pCore 2 G ≤ centralizer
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G)) : Set G) ∧
    baumannSubgroup (S : Subgroup G) = (S : Subgroup G) := by
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  let W := Z ⊔ D
  let e := (MulAut.conj x).toMonoidHom
  have hW : W.map e = W := Normal.map_conj_eq _ x
  have hD : D.map e = D := Normal.map_conj_eq _ x
  have hZX : Z.map e ≤ W := hW ▸ map_mono (show Z ≤ W from le_sup_left)
  have hsup : Z.map e ⊔ D = W := by rw [←hD,←Subgroup.map_sup,hW]
  have hsplit : Z = (Z ⊓ Z.map e) ⊔ (Z ⊓ D) :=
    eq_inf_sup_inf_of_abelian_supplement W Z (Z.map e) D le_sup_left hZX le_sup_right
      (hsup.symm ▸ (show Z ≤ W from le_sup_left)) hspan
  have hinter := baumann_opposite_omega_intersection S hgen x hopp
  change Z ⊓ Z.map e = Z ⊓ center G at hinter
  have hc : pCore 2 G ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hsplit,hinter]
    apply sup_le
    · intro z hz q _
      exact (mem_center_iff.mp hz.2 q)
    · exact inf_le_right.trans hcore
  refine ⟨hc,?_⟩
  apply le_antisymm inf_le_left
  exact hsupp.symm.le.trans (sup_le le_rfl
    (le_inf (pCore_isPGroup.le_sylow_of_normal S) hc))
end Glauberman
