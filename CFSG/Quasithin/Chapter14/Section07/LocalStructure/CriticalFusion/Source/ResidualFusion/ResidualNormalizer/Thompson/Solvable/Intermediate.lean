module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ChiefObstruction.PointCommutator
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Stellmacher.ElementaryAbelianMaxOrder

/-!+# The actual intermediate group in the solvable Thompson endgame

Set Y = DR₁ and A = J(Y)R₁. The original R₁ is Sylow in A, and A has
characteristic two by Sylow-overgroup inheritance. Its Thompson subgroup
is still J(Y), since it contains every maximum elementary subgroup of Y.
If J(Y) is solvable, so is A, by its normal subgroup J(Y) and two-group
quotient. These are the hypotheses needed to apply B.2.16 to A.

The centralizer C_A(E) equals O₂(Y), since O₂(Y) lies in R₁. We do not
identify this with O₂(A) before the quotient argument has been proved.
The original natural-action proof of U ≤ O₂(K) discharges the returning
point premise. Finally O²(J(Y)) lies in D and is nontrivial in the contrary
branch. Thus any subgroup normalized by A whose normalizer lies in N_G(L)
gives the final contradiction. In the source this subgroup is W₀(R₁,V).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed pp.1070–1071, PDF pp.1087–1088.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace ResidualNormalizer

/-- The group denoted JR₁ in the last paragraph of the source proof. -/
def JR (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G := J L F ⊔ F.Ri L 1

/-- The two-residual of J, embedded in the original ambient group. -/
def JResidual (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup G :=
  (pResidual 2 (J L F)).map (J L F).subtype

omit [Finite G] in
theorem JR_le_Y : JR L F ≤ Y L F := sup_le J_le_Y le_sup_right

/-- The old core, regarded as a subgroup of the actual intermediate group. -/
def coreInJR (L : Subgroup G) (F : InvariantFlag T V 3) : Subgroup (JR L F) :=
  ((Y L F).pCoreIn 2).subgroupOf (JR L F)

instance coreInJR_normal : (coreInJR L F).Normal :=
  normal_subgroupOf_of_le_normalizer (JR_le_Y.trans
    ((Y L F).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (Y L F) (pCore 2 (Y L F)))))

/-- The quotient whose S₃ identification is still required from B.2.16. -/
abbrev JRQuotient (L : Subgroup G) (F : InvariantFlag T V 3) :=
  JR L F ⧸ coreInJR L F

omit [Finite G] in
theorem JR_normalizes_J : JR L F ≤ normalizer (J L F : Set G) :=
  JR_le_Y.trans Y_normalizes_J

omit [Finite G] in
theorem JResidual_le_J : JResidual L F ≤ J L F := map_subtype_le _

theorem JResidual_twoPerfect : IsPPerfect 2 (JResidual L F) :=
  isPPerfect_embedded_pResidual 2 _

/-- Passing from Y to JR₁ does not change the maximum elementary generators. -/
theorem JR_thompson_eq_J : Stellmacher.elementaryAbelianMaxJ (JR L F) = J L F := by
  have hfamily : Stellmacher.elementaryAbelianMaxSubgroups (JR L F) =
      Stellmacher.elementaryAbelianMaxSubgroups (Y L F) := by
    ext A
    constructor
    · intro hA
      refine ⟨hA.1.trans JR_le_Y, hA.2.1, ?_⟩
      intro B hBY hBe
      obtain ⟨C, hC⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (Y L F)
      exact (hC.2.2 B hBY hBe).trans
        (hA.2.2 C ((le_sSup hC : C ≤ J L F).trans le_sup_left) hC.2.1)
    · intro hA
      exact ⟨(le_sSup hA : A ≤ J L F).trans le_sup_left, hA.2.1,
        fun B hB hBe => hA.2.2 B (hB.trans JR_le_Y) hBe⟩
  exact congrArg sSup hfamily

end ResidualNormalizer

namespace Data
open ResidualNormalizer
variable (d : Data T L V F W)

omit d [Finite G] [AddCommGroup W] [Module (ZMod 2) W] in
theorem residual_thompsonJoin_sylow
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    Chapter1.IsSylowIn 2 (F.Ri L 1) (JR L F) :=
  hSylow.restrict le_sup_right JR_le_Y

include d

/-- Characteristic two holds in the precise Sylow overgroup used by 14.7.31. -/
theorem residual_thompsonJoin_characteristicTwo
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    HasCharacteristicTwo (JR L F) := by
  obtain ⟨P, hP⟩ := hSylow
  apply (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (JR_le_Y (L := L) (F := F)))).mp
  apply centralizer_pCore_le_of_sylow_le P ((JR L F).subgroupOf (Y L F))
    _ d.residual_Y_characteristicTwo
  intro x hx
  exact (le_sup_right : F.Ri L 1 ≤ JR L F)
    (hP ▸ mem_map_of_mem (Y L F).subtype hx)

/-- The same statement in the F* convention required by B.2.16. -/
theorem residual_thompsonJoin_generalizedFitting
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    generalizedFitting (JR L F) = pCore 2 (JR L F) :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2
    (d.residual_thompsonJoin_characteristicTwo hSylow)

omit d [AddCommGroup W] [Module (ZMod 2) W] in
/-- Solvability of J suffices: its quotient in JR₁ is an image of R₁. -/
theorem residual_thompsonJoin_solvable (hsol : Group.IsSolvable (J L F)) :
    Group.IsSolvable (JR L F) := by
  let A := JR L F
  let N := (J L F).subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer JR_normalizes_J
  let := hsol
  have hN : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show J L F ≤ A from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show J L F ≤ A from le_sup_left)).injective
  have hgen : N ⊔ (F.Ri L 1).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show J L F ≤ A from le_sup_left),
      map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ A from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hp := isPGroup_quotient_of_sup_eq_top N ((F.Ri L 1).subgroupOf A)
    ((T.isPGroup'.to_le residual_R_le_sylow).comap_subtype) hgen
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr
    ⟨hN, @IsNilpotent.to_isSolvable _ _ hp.isNilpotent⟩

omit d [Finite G] [AddCommGroup W] [Module (ZMod 2) W] in
theorem residual_Y_core_le_R
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    (Y L F).pCoreIn 2 ≤ F.Ri L 1 := by
  obtain ⟨P, hP⟩ := hSylow
  exact (pCoreIn_le_sylow _ P).trans_eq hP

/-- C_JR₁(E) is the OLD core. Identifying it with the new core requires the
separate quotient calculation; it is not an instance of core monotonicity. -/
theorem residual_thompsonJoin_centralizer
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    JR L F ⊓ centralizer (E F : Set G) = (Y L F).pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_right _ JR_le_Y).trans
      (d.residualSpan_centralizer_eq_core hSylow).le
  · exact le_inf ((residual_Y_core_le_R hSylow).trans le_sup_right)
      ((d.residualSpan_centralizer_eq_core hSylow).symm.le.trans inf_le_right)

theorem residual_thompsonJoin_normalizes_E :
    JR L F ≤ normalizer (E F : Set G) := JR_le_Y.trans d.residual_Y_normalizes_E

/-- The original module is elementary and relatively normal in JR₁. -/
theorem residual_thompsonJoin_elementary_normal
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F)) :
    IsElementaryAbelian 2 ((E F).subgroupOf (JR L F)) ∧
      ((E F).subgroupOf (JR L F)).Normal := by
  let := (d.residualSpan_reduced hSylow).elementary
  have he := IsElementaryAbelian.map (p := 2) (A := (E F).subgroupOf (Y L F))
    (Y L F).subtype
  rw [map_subgroupOf_eq_of_le
    (show E F ≤ Y L F from d.residualSpan_le_D.trans le_sup_left)] at he
  let := he
  exact ⟨IsElementaryAbelian.subgroupOf ((d.residualSpan_le_R hSylow).trans le_sup_right),
    normal_subgroupOf_of_le_normalizer d.residual_thompsonJoin_normalizes_E⟩

/-- This application discharges Preparation's earlier U-containment premise
using the original natural action, rather than a new containment hypothesis. -/
theorem returning_point_U_le_thompsonJoin_core
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (g : G) (hg : conjugate (F.Vi 1) g ≤ E F) :
    conjugate F.U g ≤ (JR L F).pCoreIn 2 :=
  d.returning_point_conjugate_U_le_thompson_core hSylow d.U_le_K_core g hg

omit d [AddCommGroup W] [Module (ZMod 2) W] in
/-- The quotient Y/D is a two-group, so the two-perfect O²(J) lies in D. -/
theorem residual_thompson_residual_le_D : JResidual L F ≤ D F := by
  let A := Y L F
  let N := (D F).subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (D F).le_normalizer residual_R_normalizes_D)
  have hgen : N ⊔ (F.Ri L 1).subgroupOf A = ⊤ := by
    apply map_injective A.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show D F ≤ A from le_sup_left),
      map_subgroupOf_eq_of_le (show F.Ri L 1 ≤ A from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hp := isPGroup_quotient_of_sup_eq_top N ((F.Ri L 1).subgroupOf A)
    ((T.isPGroup'.to_le residual_R_le_sylow).comap_subtype) hgen
  let f := (QuotientGroup.mk' N).comp (inclusion (JResidual_le_J.trans J_le_Y))
  have hf := (JResidual_twoPerfect (L := L) (F := F)).hom_eq_one_of_isPGroup hp f
  intro x hx
  exact (QuotientGroup.eq_one_iff (N := N) ⟨x, J_le_Y (JResidual_le_J hx)⟩).mp
    (DFunLike.congr_fun hf ⟨x, hx⟩)

/-- The residual, not the core, is the nontrivial subgroup in the final line. -/
theorem residual_thompson_residual_ne_bot
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F)) : JResidual L F ≠ ⊥ := by
  intro hz
  have hr : pResidual 2 (J L F) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (J L F).subtype_injective).mp hz
  apply d.residual_thompson_not_isPGroup hDM hSylow hBaum hD
  intro x
  obtain ⟨n, hn⟩ := isPGroup_quotient_pResidual (G := J L F) 2
    (QuotientGroup.mk' (pResidual 2 (J L F)) x)
  refine ⟨n, ?_⟩
  apply mem_bot.mp
  rw [← hr]
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pResidual 2 (J L F)) (x ^ 2 ^ n) = 1
  rw [map_pow]
  exact hn

/-- The final residual contradiction applies to any suitable normalized
subgroup. The W₀ application must still prove BOTH normalizer containments. -/
theorem false_of_thompsonJoin_normalizer_bound
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    (B : Subgroup G) (hB : JR L F ≤ normalizer (B : Set G))
    (hBM : normalizer (B : Set G) ≤ normalizer (L : Set G)) : False := by
  have hp : IsPGroup 2 (JResidual L F) := T.isPGroup'.to_le
    ((le_inf residual_thompson_residual_le_D
      (JResidual_le_J.trans (le_sup_left.trans (hB.trans hBM)))).trans hDM)
  have he := (JResidual_twoPerfect (L := L) (F := F)).hom_eq_one_of_isPGroup hp
    (MonoidHom.id (JResidual L F))
  apply d.residual_thompson_residual_ne_bot hDM hSylow hBaum hD
  apply bot_unique
  intro x hx
  exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
