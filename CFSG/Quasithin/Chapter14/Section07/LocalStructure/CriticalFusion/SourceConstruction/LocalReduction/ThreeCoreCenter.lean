module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreContainment

/-!
# The original point in the selected normal three-core lifts

A normal two-perfect cubic lift with strict normalizer intersection is
exactly L₁: point containment gives one inclusion, and the identical cubic
star images give the other through the full two-core, which normalizes L₁.

For a minimal solvable local J, the marked Heisenberg center lift Z and
L₁T generate a proper subgroup. Their two cubic images and a two-group
cannot generate a group whose three-core contains the marked order-27
subgroup. Minimality therefore places Z in N_G(L). Applying the cubic
result identifies Z with L₁, proving relative normality in J and the exact
center-image identity. Both quotient kernels are retained.

The final theorem applies the containment and center arguments to the
original selected minimal witness. The elementary-nine and Heisenberg
terminal exclusions, component reductions, and full 14.7.52 alternatives
remain required; these statements do not assert their completion.

Source: Aschbacher–Smith, 14.5.20 assertions (!!) and the center-lift step,
printed p.1019; 14.7.9 and 14.7.27, printed pp.1045,1054–1055,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- A normal two-perfect cubic lift with strict normalizer intersection is
exactly the original point residual, with the whole star kernel retained. -/
theorem local_solvable_normal_cubic_lift_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (Y : Subgroup J) [Y.Normal] (hp : IsPPerfect 2 Y)
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hi : (Y.map J.subtype).pCoreIn 2 < Y.map J.subtype ⊓ normalizer (L : Set G)) :
    Y = (F.Li L 1).subgroupOf J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := (F.Li L 1).subgroupOf J
  have hAY := local_three_lift_contains_point h structural J hJ Y
    (IsPGroup.of_card (n := 1) (by simpa using hc)) hi
  have hY : Nat.card (Y.map q) = 3 :=
    (Nat.card_congr (coreQuotientEquivImage 2 Y).toEquiv).symm.trans hc
  have hA : Nat.card (A.map q) = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have he : A.map q = Y.map q := eq_of_le_of_card_ge (map_mono hAY) (by rw [hA,hY])
  have hn : q.ker ≤ normalizer (A : Set J) := by
    rw [QuotientGroup.ker_mk']
    let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
    apply (pCore_isPGroup.le_sylow_of_normal S).trans
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁ h structural hx
  exact le_antisymm
    (isPPerfect_le_of_map_le_of_kernel_normalizes q Y A hp
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hn he.ge) hAY

private theorem cubic_pair_join_ne_top
    {D : Type*} [Group D] [Finite D]
    (X B C S : Subgroup D) (hX : 9 < Nat.card X) (hXP : X ≤ pCore 3 D)
    (hB : Nat.card B = 3) (hC : Nat.card C = 3)
    (hBC : B ≤ normalizer (C : Set D)) (hS : IsPGroup 2 S)
    (hSB : S ≤ normalizer (B : Set D)) (hSC : S ≤ normalizer (C : Set D)) :
    C ⊔ B ⊔ S ≠ ⊤ := by
  intro he
  let A := C ⊔ B
  have hSA : S ≤ normalizer (A : Set D) :=
    (le_inf hSC hSB).trans (normalizer_inf_normalizer_le_normalizer_sup C B)
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←he]
    exact sup_le A.le_normalizer hSA))
  have hquot : IsPGroup 2 (D ⧸ A) := isPGroup_quotient_of_sup_eq_top A S hS he
  have hPA : pCore 3 D ≤ A := by
    let q := QuotientGroup.mk' A
    have hz : (pCore 3 D).map q = ⊥ := by
      have hd := ((pCore_isPGroup (p := 3) (G := D)).map q).disjoint_of_coprime
        (hquot.to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
      simpa using hd.eq_bot
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes C B hBC
  have hpos := Nat.card_pos (α := (C ⊓ B : Subgroup D))
  have hle : Nat.card A ≤ 9 := by
    change Nat.card (C ⊔ B : Subgroup D) ≤ 9
    rw [hC,hB] at hc
    nlinarith
  exact (not_le_of_gt hX) ((card_le_of_le (hXP.trans hPA)).trans hle)

/-- In a minimal original solvable local, the selected Heisenberg center
lift equals L₁. In particular its actual star image is the center and L₁
is normal in the whole original local, without a point-normality premise. -/
theorem local_minimal_solvable_heisenberg_center_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (hmin : ∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < J →
      D ≤ normalizer (L : Set G))
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e : X ≃* HeisenbergPrime 3) (Y : Subgroup J) [Y.Normal]
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype) :
    ((F.Li L 1).subgroupOf J).Normal ∧
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) =
      ((center X).map X.subtype).map (pCore 3 (HStar J)).subtype ∧
    ∃ Z : Subgroup J, Z = (F.Li L 1).subgroupOf J ∧ Z < Y ∧
      Z.Normal ∧ IsPPerfect 2 Z ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Z.subtype).ker = pCore 2 Z ∧
      Nat.card (Z ⧸ pCore 2 Z) = 3 ∧ Nonempty ((Z ⧸ pCore 2 Z) ≃* center X) ∧
      pCore 2 Z ≠ ⊥ := by
  obtain ⟨Z,hZY,hZn,hZp,hZm,hZk,hZc,hZe,hZQ,_⟩ :=
    local_solvable_heisenberg_center_lift h structural J hJ X hX e Y hm
  let := hZn
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := (F.Li L 1).subgroupOf J
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hSA : (S : Subgroup J) ≤ normalizer (A : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁ h structural hx
  have hXc : 9 < Nat.card (X.map (pCore 3 (HStar J)).subtype) := by
    rw [card_map_of_injective (pCore 3 (HStar J)).subtype_injective,
      Nat.card_congr e.toEquiv,HeisenbergPrime.card]
    decide
  have hZim : Nat.card (Z.map q) = 3 :=
    (Nat.card_congr (coreQuotientEquivImage 2 Z).toEquiv).symm.trans hZc
  let : (Z.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hne := cubic_pair_join_ne_top (X.map (pCore 3 (HStar J)).subtype)
    (A.map q) (Z.map q) ((S : Subgroup J).map q) hXc (map_subtype_le X)
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2 hZim
    le_normalizer_of_normal (S.isPGroup'.map q)
    ((map_mono hSA).trans (le_normalizer_map q)) le_normalizer_of_normal
  let D := Z ⊔ A ⊔ (S : Subgroup J)
  have hDne : D ≠ ⊤ := by
    intro he
    apply hne
    rw [←Subgroup.map_sup,←Subgroup.map_sup,show Z ⊔ A ⊔ (S : Subgroup J) = D from rfl,he,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hDlt : D.map J.subtype < J :=
    lt_of_le_of_ne (map_subtype_le D) (fun he => hDne
      (map_injective J.subtype_injective (by
        simpa only [←MonoidHom.range_eq_map,range_subtype] using he)))
  have hDmap : D.map J.subtype = Z.map J.subtype ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) := by
    rw [show D = Z ⊔ A ⊔ (S : Subgroup J) from rfl,Subgroup.map_sup,Subgroup.map_sup,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hJ),Sylow.coe_subtype,
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ),sup_assoc]
  have hZM : Z.map J.subtype ≤ normalizer (L : Set G) :=
    (hDmap ▸ le_sup_left).trans (hmin _ (hDmap ▸ le_sup_right) hDlt)
  have hi := local_lift_intersection_of_cubic_sublift h structural J hJ Z Z le_rfl hZM hZk hZc
  have heq := local_solvable_normal_cubic_lift_eq_point h hab structural previous faithful
    J hJ hs Z hZp hZc hi
  exact ⟨heq ▸ hZn,heq ▸ hZm,Z,heq,hZY,hZn,hZp,hZk,hZc,hZe,hZQ⟩

/-- The original solvable witness now has point containment in every
selected normal lift. In the Heisenberg branch the same point is normal
in the whole minimal local and is exactly the marked residual center. -/
theorem local_minimal_solvable_threeCore_point_and_center
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ (I : Subgroup G), I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
    ∃ (X : Subgroup (pCore 3 (HStar I))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup I),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
      Y.map (QuotientGroup.mk' (pCore 2 I)) = X.map (pCore 3 (HStar I)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
      (F.Li L 1).subgroupOf I ≤ Y ∧
      (Y.map I.subtype).pCoreIn 2 < Y.map I.subtype ⊓ normalizer (L : Set G) ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I)) ∨
        (Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3) ∧
          ((F.Li L 1).subgroupOf I).Normal ∧
          ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I)) =
            ((center X).map X.subtype).map (pCore 3 (HStar I)).subtype)) := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,_,hi,he⟩ :=
    local_minimal_solvable_threeCore_reduction h hab structural previous faithful J hJ hs
  let := hYn
  let eX : (Y ⧸ pCore 2 Y) ≃* X := (coreQuotientEquivImage 2 Y).trans
    ((MulEquiv.subgroupCongr hm).trans
      (equivMapOfInjective X (pCore 3 (HStar I)).subtype
        (pCore 3 (HStar I)).subtype_injective).symm)
  have h3 : IsPGroup 3 (Y ⧸ pCore 2 Y) :=
    ((pCore_isPGroup (p := 3) (G := HStar I)).to_subgroup X).of_equiv eX.symm
  refine ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,
    local_three_lift_contains_point h structural I hI Y h3 hi,hi,?_⟩
  rcases he with he | ⟨he,_,_⟩
  · exact Or.inl he
  · obtain ⟨hn,hcenter,_⟩ := local_minimal_solvable_heisenberg_center_eq_point
      h hab structural previous faithful I hI hIs hmin X hX (eX.symm.trans he.some) Y hm
    exact Or.inr ⟨he,hn,hcenter⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
