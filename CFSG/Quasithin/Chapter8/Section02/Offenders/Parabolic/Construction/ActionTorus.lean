module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Preparation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Quotient
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus.Models

/-!
# The selected actor and quotient-torus fixed points

Source: Aschbacher–Smith, Proposition 8.2.2(7–8), printed pp.714–715
(PDF pp.731–732), using E.2.11–14, printed pp.224–228.

`selected_action_data` embeds the native actor and its centralizer, reuses
the checked cubic-action theorem, verifies the exact local quadratic-ratio
premise of E.2.14(7), and applies E.2.13(7) to the intrinsic section P/Z.
Its outputs are the literal A, B and Z consumed by the parent construction.
The parent derives the actor-rank identity, strict action ratio and C_V(A) ≤ B.

For fixed points, an arbitrary subgroup of order 2^k−1 in Aut_{M∩I}(V)
is lifted to M∩I through its two-group action kernel. Its image under the
separate star projection has the same order, so E.2.14(9) applies. The
fixed-subgroup comparison uses the original conjugation action. There is
no assumed action of I/O₂(I) on V and no assumed inclusion of the kernels.
Cyclicity is unnecessary because the source torus clause covers every
subgroup of the stated order.

The final theorem uses the selected Sylow and center markings in I/O₂(I),
the actual model/Borel equivalences and two explicit matrix centralizer
facts. Earlier universal E.2 inputs remain explicit under this conditional
contract. Their producers and the selection branch must be discharged by
qt-8-02-parabolic-source-construction; this module does not assert the full
unconditional Proposition 8.2.2. Existing modules and the independent
selection branch are preserved.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open ChapterE BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

/-- The fixed subgroup in the original ambient group, for the actual action. -/
noncomputable def automizerFixedGroup (V : Subgroup G) [IsElementaryAbelian 2 V]
    (X : Subgroup (Automizer V)) : Subgroup G :=
  (fixedSpace (automizerRepresentation V) X).toAddSubgroup.toSubgroup'.map V.subtype

/-- Fixed vectors for the induced conjugation image are exactly C_V(D). -/
theorem automizerFixedGroup_induced (V D : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : D ≤ normalizer (V : Set G)) :
    automizerFixedGroup V (inducedAutomizer V D) = V ⊓ centralizer (D : Set G) := by
  apply le_antisymm
  · rintro x ⟨v, hv, rfl⟩
    exact ⟨v.property, (mem_fixedSpace_inducedAutomizer V D hn (Additive.ofMul v)).mp hv⟩
  · intro x hx
    exact ⟨⟨x, hx.1⟩, (mem_fixedSpace_inducedAutomizer V D hn (Additive.ofMul ⟨x, hx.1⟩)).mpr hx.2, rfl⟩

/-- The action half of the conditional construction, with the universal
earlier source inputs applied to the same selected pair and conjugator. -/
theorem selected_action_data [Finite G] (K : GroupClass)
    (e11 : E211NormalizerClause (G := G) K)
    (e13 : E213SectionClause (G := G) K) (e14 : E214RankClause (G := G) K)
    (H T M V I : Subgroup G) [IsElementaryAbelian 2 V] (k : ℕ)
    (h28 : HypothesisE28 K H T M V) (hF : Family H T M V I k)
    (hchar : HasCharacteristicTwo H) (hTI : LocalTI H M V)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I)
    (hZ : V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥)
    (S : Sylow 2 I)
    (hlocal : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
    (hNI : I ⊓ normalizer (V : Set G) ≤ M)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype)) :
    let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let B := V ⊓ (pCore 2 I).map I.subtype
    let Z := V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom
    A = offenderNormalizer V (i.val)⁻¹ ∧ A ⊓ centralizer (V : Set G) = Z ∧
      ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ ∧
      (rank (inducedAutomizer V A) ≤ 2 * k → rank (inducedAutomizer V A) = 2 * k) ∧
      I ⊓ centralizer (A ⊔ B : Subgroup G) ≤ (pCore 2 I).map I.subtype := by
  have hVI : V ≤ I := hgen ▸ le_sup_left
  refine ⟨selected_actor_normalizer I M V hVI S i hlocal
      (e11 H T M V I k h28 hF i hgen S hlocal),
    selected_actor_kernel I M V hVI S i hlocal,
    selected_actor_cubic I M V hVI S i hlocal, ?_, ?_⟩
  · exact e14 H T M V I k h28 hF hchar hTI i hgen hZ
      (selected_quadraticRatio_gt_one M I V hNI hq)
  · exact selected_pair_centralizer_bound I M V hVI S i hlocal
      (e13 H T M V I k h28 hF hchar i hgen S hlocal)

/-- Transport E.2.14(9) from the star quotient to the literal automizer.
The model centralizer bound is discharged from markings in the final theorem. -/
theorem selected_torus_fixed [Finite G] (K : GroupClass)
    (e14 : E214TorusClause (G := G) K)
    (H T M V I : Subgroup G) [IsElementaryAbelian 2 V] (k : ℕ)
    (h28 : HypothesisE28 K H T M V) (hF : Family H T M V I k)
    (hchar : HasCharacteristicTwo H) (hTI : LocalTI H M V)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I)
    (hZ : V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥)
    (hc : localCore M I = pCore 2 I)
    (hn : M ⊓ I ≤ normalizer (V : Set G))
    (hr : RankOneAlternative (Star M I) (starImage M I M) k)
    (hC : IsPGroup 2 ↥(starImage M I M ⊓ centralizer (starImage M I V : Set (Star M I))))
    (hk : 1 < k) (X : Subgroup (inducedAutomizer V (M ⊓ I)))
    (hX : Nat.card X = 2 ^ k - 1) :
    automizerFixedGroup V (X.map (inducedAutomizer V (M ⊓ I)).subtype) =
      V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom := by
  have ho : Odd (Nat.card X) := by
    rw [hX]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide, by omega⟩) odd_one
  obtain ⟨D, hD, hinj, hcard, _⟩ := selected_odd_lift M I V hn hc hC X ho
  have hDM : D.map (selectedStarMap M I) ≤ starImage M I M := by
    rintro _ ⟨d, _, rfl⟩
    exact mem_map_of_mem _ d.property.1
  have hmodel : Nonempty (Star M I ≃* PSL2
      (BinaryGaloisField k)) ∨
      ∃ m : ℕ, 0 < m ∧ k = 2 * m + 1 ∧
        Nonempty (Star M I ≃* SuzukiMatrixGroup m) := by
    rcases hr.models.2 with ⟨m, _, _, hk1, _⟩ | ⟨_, he⟩ | hsz
    · omega
    · exact Or.inl he
    · exact Or.inr hsz
  have hfixed := e14 H T M V I k h28 hF hchar hTI i hgen hZ hmodel hk
    (D.map (selectedStarMap M I)) hDM (hcard.trans hX) D rfl hinj
  rw [← hD, selected_lift_action_image, automizerFixedGroup_induced]
  · exact hfixed
  · exact (map_subtype_le D).trans hn

/-- Proposition 8.2.2(8), conditional only on the earlier E.2.14(9) and
matrix-model inputs, applied to the actual selected markings. Every subgroup
of the stated order in the action image is covered, without a cyclicity input. -/
theorem selected_torus_fixed_of_core_markings [Finite G] (K : GroupClass)
    (e14 : E214TorusClause (G := G) K) (models : RankOneBorelCenterModels)
    (H T M V I : Subgroup G) [IsElementaryAbelian 2 V] (k : ℕ)
    (h28 : HypothesisE28 K H T M V) (hF : Family H T M V I k)
    (hchar : HasCharacteristicTwo H) (hTI : LocalTI H M V)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I)
    (hZ : V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥)
    (hc : localCore M I = pCore 2 I)
    (hn : M ⊓ I ≤ normalizer (V : Set G))
    (hr : RankOneAlternative (I ⧸ pCore 2 I) (coreImage I M) k)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (hlocal : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
    (hcenter : coreImage I V = embeddedCenter (coreImage I T))
    (hk : 1 < k) (Xbar : Subgroup (Automizer V))
    (hXM : Xbar ≤ inducedAutomizer V (M ⊓ I)) (hX : Nat.card Xbar = 2 ^ k - 1) :
    automizerFixedGroup V Xbar = V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom := by
  let e := coreQuotientEquiv M I hc
  have hcancel : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
    ext x
    exact e.symm_apply_apply x
  have hrstar := hr.map e.symm
  rw [← starImage_map_coreQuotientEquiv M I M hc, map_map, hcancel, map_id] at hrstar
  have hC := selected_borel_center_two_of_core_markings models M I V T k hk hc hrstar S hS
    (hlocal.sylow_le_normalizer.trans hlocal.normalizer_le) hcenter
  have hcard : Nat.card (Xbar.subgroupOf (inducedAutomizer V (M ⊓ I))) = 2 ^ k - 1 :=
    (Nat.card_congr (subgroupOfEquivOfLe hXM).toEquiv).trans hX
  have hfixed := selected_torus_fixed K e14 H T M V I k h28 hF hchar hTI i hgen hZ hc hn
    hrstar hC hk (Xbar.subgroupOf (inducedAutomizer V (M ⊓ I))) hcard
  rwa [map_subgroupOf_eq_of_le hXM] at hfixed

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
