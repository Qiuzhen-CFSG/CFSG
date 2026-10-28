module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.SolvableNineKernel
public import Theory.GroupTheory.PGroup.NormalNineFixedLine

/-!
# The fixed point line in the original normal nine-lift

The three-core moves the quotient-centralizing cubic line in the normal
nine-image. Its fixed subgroup in that image is therefore cubic. Lift this
fixed subgroup normally inside the original two-perfect Y, retaining the
whole star-map kernel. Since Y lies in N_G(L), so does the lift. The checked
normal-cubic identification makes this lift exactly L₁. Hence L₁ is normal
in J and its actual star image is the fixed line of the three-core.

This line and the moved quotient-centralizing cubic are disjoint and generate
the original nine-image. A three-core element outside that image centralizes
the point and moves the other line. Selecting an actor whose enlarged group
is T-invariant, and handling its possible order nine, remain required.

The minimal solvable witness now has normal point residual in both the
elementary-nine and Heisenberg branches. The final application retains the
original G, T, L, V and flag, together with the exact point two-core kernel.
No solvable exclusion or final 14.7.52 classification is asserted here.

Source: Aschbacher–Smith, 14.5.20, printed p.1019, and 14.7.27–29,
printed pp.1054–1055, refs/quasithin.pdf.
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

/-- The three-core fixed line in the normal nine-image is precisely the
original point image, and its normal lift is the original point residual. -/
theorem local_solvable_nine_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    ((F.Li L 1).subgroupOf J).Normal ∧
      ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) =
        Y.map (QuotientGroup.mk' (pCore 2 J)) ⊓
          centralizer (pCore 3 (HStar J) : Set (HStar J)) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let P := pCore 3 (HStar J)
  let N := Y.map q
  let Z := N ⊓ centralizer (P : Set (HStar J))
  let : N.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Z.Normal := inferInstance
  have hkq : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have h9 : Nat.card N = 9 := by
    rw [←Nat.card_congr (coreQuotientEquivImage 2 Y).toEquiv,
      Nat.card_congr e.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hN : IsPGroup 3 N := IsPGroup.of_card (n := 2) h9
  have hmove : ¬ P ≤ centralizer (N : Set (HStar J)) := by
    intro hc
    obtain ⟨C,hCY,_,_,_,_,_,_,hout⟩ := local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful J hJ hs Y hYp hAY e hr
    exact hout (hc.trans ((centralizer_le (map_mono hCY)).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hZ : Nat.card Z = 3 := normal_nine_fixed_line_card P N pCore_isPGroup hN h9 hmove
  obtain ⟨W,hWY,hWp,hWm,hWN,hWK,hWk,hWe⟩ := exists_three_lift_within_normal
    q hkq Y Z ⊤ inf_le_left le_normalizer_of_normal (hN.to_le inf_le_left)
  let : W.Normal := normalizer_eq_top_iff.mp (top_unique (by simpa using hWN))
  have hcW : Nat.card (W ⧸ pCore 2 W) = 3 := (Nat.card_congr hWe.some.toEquiv).trans hZ
  have hWM : W.map J.subtype ≤ normalizer (L : Set G) :=
    (map_mono hWY).trans (local_solvable_nine_lift_containment
      h hab structural previous faithful J hJ hs Y hYp hAY e)
  have hi := local_lift_intersection_of_cubic_sublift h structural J hJ W W le_rfl hWM hWk hcW
  have heq := local_solvable_normal_cubic_lift_eq_point
    h hab structural previous faithful J hJ hs W hWp hcW hi
  exact ⟨heq ▸ inferInstanceAs W.Normal,heq ▸ hWm⟩

/-- The literal nine-image splits into the point and quotient-centralizing
cubics. A three-core actor outside that image fixes the point and moves the
other line. This does not assert an order-three lift or T-stability of its join. -/
theorem local_solvable_nine_split_and_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) (Y : Subgroup J) [Y.Normal]
    (hYp : IsPPerfect 2 Y) (hAY : (F.Li L 1).subgroupOf J ≤ Y)
    (e : (Y ⧸ pCore 2 Y) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))
    (hr : pResidual 2 (HStar J) = pCore 3 (HStar J)) :
    let q := QuotientGroup.mk' (pCore 2 J)
    let A := ((F.Li L 1).subgroupOf J).map q
    ∃ C : Subgroup J, C ≤ Y ∧ IsPPerfect 2 C ∧
      (T : Subgroup G) ≤ normalizer (C.map J.subtype : Set G) ∧
      (q.comp C.subtype).ker = pCore 2 C ∧ Nat.card (C.map q) = 3 ∧
      ⁅L,C.map J.subtype⁆ ≤ L.pCoreIn 2 ∧
      normalizer (C.map J.subtype : Set G) ≤ normalizer (L : Set G) ∧
      Disjoint A (C.map q) ∧ A ⊔ C.map q = Y.map q ∧
      ∃ y : HStar J, y ∈ pCore 3 (HStar J) ∧ y ∉ Y.map q ∧
        y ∈ centralizer (A : Set (HStar J)) ∧
        y ∉ normalizer (C.map q : Set (HStar J)) := by
  classical
  let q := QuotientGroup.mk' (pCore 2 J)
  let A := ((F.Li L 1).subgroupOf J).map q
  let N := Y.map q
  obtain ⟨hn,hfixed⟩ := local_solvable_nine_point_normal
    h hab structural previous faithful J hJ hs Y hYp hAY e hr
  let := hn
  let : A.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  obtain ⟨C,hCY,hCp,hTC,hCk,h3C,hcomm,hbound,hout⟩ :=
    local_solvable_nine_centralizing_line_moved
      h hab structural previous faithful J hJ hs Y hYp hAY e hr
  have h3A : Nat.card A = 3 :=
    (local_solvable_point_kernel h hab structural previous faithful J hJ hs).2
  have hne : A ≠ C.map q := by
    intro he
    apply hout
    rw [←he]
    exact le_normalizer_of_normal
  have hdis : Disjoint A (C.map q) := by
    have hd : Nat.card (A ⊓ C.map q : Subgroup (HStar J)) ∣ 3 :=
      h3A ▸ card_dvd_of_le (inf_le_left : A ⊓ C.map q ≤ A)
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h1 | h3
    · exact disjoint_iff.mpr (card_eq_one.mp h1)
    · have hAeq : A ⊓ C.map q = A := eq_of_le_of_card_ge inf_le_left (by rw [h3,h3A])
      have hCeq : A ⊓ C.map q = C.map q := eq_of_le_of_card_ge inf_le_right (by rw [h3,h3C])
      exact (hne (hAeq.symm.trans hCeq)).elim
  let eN := (coreQuotientEquivImage 2 Y).symm.trans e
  let : IsMulCommutative N := IsMulCommutative.of_comm fun a b =>
    eN.injective (by simp only [map_mul,mul_comm])
  have h9 : Nat.card N = 9 := by
    rw [Nat.card_congr eN.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  have hgen : A ⊔ C.map q = N := by
    apply eq_of_le_of_card_ge (sup_le (map_mono hAY) (map_mono hCY))
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A (C.map q)
      le_normalizer_of_normal hdis,h3A,h3C,h9]
  obtain ⟨y,hyP,hyC⟩ := Set.not_subset.mp hout
  have hyN : y ∉ N := by
    intro hy
    exact hyC (((le_centralizer N).trans
      ((centralizer_le (map_mono hCY)).trans (Subgroup.centralizer_le_normalizer _))) hy)
  have hAP : A ≤ centralizer (pCore 3 (HStar J) : Set (HStar J)) := by
    rw [show A = N ⊓ centralizer (pCore 3 (HStar J) : Set (HStar J)) from hfixed]
    exact inf_le_right
  exact ⟨C,hCY,hCp,hTC,hCk,h3C,hcomm,hbound,hdis,hgen,y,hyP,hyN,
    le_centralizer_iff.mp hAP hyP,hyC⟩

/-- The selected original minimal solvable local has normal point residual in either model branch. -/
theorem local_minimal_solvable_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ∃ I : Subgroup G, I ≤ J ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal := by
  obtain ⟨I,hIJ,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful J hJ hs
  let := hYn
  refine ⟨I,hIJ,hI,hIs,hmin,?_⟩
  rcases he with ⟨he,hr⟩ | ⟨he,hn,_⟩
  · exact (local_solvable_nine_point_normal h hab structural previous faithful
      I hI hIs Y hYp hAY he.some hr).1
  · exact hn

/-- Apply the split to the actual selected minimal witness. The alternative
retains its Heisenberg marking; neither model is assumed at this consumer. -/
theorem original_solvable_nine_split_or_heisenberg
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I ≤ F.H ∧ I ∈ F.Hz L (normalizer (L : Set G)) ∧
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      ∃ Y : Subgroup I, Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 I ∧
        (F.Li L 1).subgroupOf I ≤ Y ∧
        ((QuotientGroup.mk' (pCore 2 I)).comp Y.subtype).ker = pCore 2 Y ∧
        ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
            (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar I) = pCore 3 (HStar I) ∧
          let q := QuotientGroup.mk' (pCore 2 I)
          let A := ((F.Li L 1).subgroupOf I).map q
          ∃ C : Subgroup I, C ≤ Y ∧ IsPPerfect 2 C ∧
            (T : Subgroup G) ≤ normalizer (C.map I.subtype : Set G) ∧
            (q.comp C.subtype).ker = pCore 2 C ∧ Nat.card (C.map q) = 3 ∧
            ⁅L,C.map I.subtype⁆ ≤ L.pCoreIn 2 ∧
            normalizer (C.map I.subtype : Set G) ≤ normalizer (L : Set G) ∧
            Disjoint A (C.map q) ∧ A ⊔ C.map q = Y.map q ∧
            ∃ y : HStar I, y ∈ pCore 3 (HStar I) ∧ y ∉ Y.map q ∧
              y ∈ centralizer (A : Set (HStar I)) ∧
              y ∉ normalizer (C.map q : Set (HStar I))) ∨
          Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  obtain ⟨I,hIH,hI,hIs,hmin,X,hX,Y,hYn,hYp,hYr,hm,hk,hAY,hi,he⟩ :=
    local_minimal_solvable_threeCore_point_and_center h hab structural previous faithful
      F.H (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hs
  let := hYn
  rcases he with ⟨he,hr⟩ | ⟨he,hn,_⟩
  · exact ⟨I,hIH,hI,hIs,hmin,
      (local_solvable_nine_point_normal h hab structural previous faithful
        I hI hIs Y hYp hAY he.some hr).1,Y,hYn,hYp,hYr,hAY,hk,
      Or.inl ⟨he,hr,local_solvable_nine_split_and_actor h hab structural previous faithful
        I hI hIs Y hYp hAY he.some hr⟩⟩
  · exact ⟨I,hIH,hI,hIs,hmin,hn,Y,hYn,hYp,hYr,hAY,hk,Or.inr he⟩

/-- At the original point normalizer, a solvable witness yields a minimal
escaping local which normalizes L₁, with the literal cubic image and full
two-core kernel. No local normality or marking is an additional premise. -/
theorem original_solvable_minimal_point_normal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hs : Group.IsSolvable F.H) :
    ∃ I : Subgroup G, I ≤ F.H ∧ ∃ hI : I ∈ F.Hz L (normalizer (L : Set G)),
      Group.IsSolvable I ∧
      (∀ D : Subgroup G, F.Li L 1 ⊔ (T : Subgroup G) ≤ D → D < I →
        D ≤ normalizer (L : Set G)) ∧
      ((F.Li L 1).subgroupOf I).Normal ∧
      I ≤ normalizer (F.Li L 1 : Set G) ∧
      ((QuotientGroup.mk' (pCore 2 I)).comp
        (inclusion (F.Li_one_le_of_mem_Hz hI))).ker =
        pCore 2 (F.Li L 1) ∧
      Nat.card (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = 3 := by
  obtain ⟨I,hIH,hI,hIs,hmin,hn⟩ := local_minimal_solvable_point_normal
    h hab structural previous faithful F.H
      (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) hs
  let := hn
  have hnorm : I ≤ normalizer (F.Li L 1 : Set G) := by
    have hh := ((F.Li L 1).subgroupOf I).le_normalizer_map I.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hI)] using hh
  exact ⟨I,hIH,hI,hIs,hmin,hn,hnorm,
    local_solvable_point_kernel h hab structural previous faithful I hI hIs⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
