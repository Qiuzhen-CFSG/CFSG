module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicLinearAction
public import Theory.Representation.ConjugatePointNatural
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Natural geometry of the nonsolvable cubic completion

The proved faithful quotient D/C_D(W) is marked at both original cubic
vertices: P maps to the line parabolic and YT to the point parabolic.
Conjugation on the literal elementary subgroup W = ⟨V₁ᴰ⟩ descends through
this quotient. The point is fixed by YT and its P-span is exactly V₂,
so H.5.5 gives actual equivariant natural coordinates on W.

In particular |W| = 8. Since an escaping Y cannot normalize V₂, its
V₂-span is larger than the plane and hence equals W. Thus W ≤ U and
⟨Wᴴ⟩ = U. Natural transitivity and this abelian span imply that intersecting
conjugates of W commute. This supplies the symmetric abelian geometry
needed in the remaining ambient exclusion, without an additional 14.4.14
premise. The last theorem applies all these deductions to the actual
order-four chief interval, retaining the original star kernel and cubic.

The ambient critical-pair exclusion of this nonsolvable case, solvability
of D, and the later containment and residual classification are still needed.
EarlierFaithfulClassification is the independent 14.3.4 input, with its
existing producer and final discharge at the original source parents.

Source: Aschbacher–Smith, H.5.5, printed p.386; proof of 14.5.8,
printed pp.1014–1015; its use in 14.7.20, printed p.1049,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u

private theorem goldschmidt_linear_marking
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (e : D ≃* Matrix.PSL3Two.PSL) :
    ∃ f : D ≃* Matrix.PSL3Two.SL,
      A.map f.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      B.map f.toMonoidHom = Matrix.PSL3Two.pointParabolicSL := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  let : Group.IsSolvable B := SymmetricThreeTwoCore.solvable ht.quotient_right.some
  have hns : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    exact not_isSolvable_psl3_two
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hproper (P : Subgroup D) [Group.IsSolvable P] : P ≠ ⊤ := by
    intro he
    have hp : Function.Surjective P.subtype := by
      intro x
      exact ⟨⟨x,he ▸ mem_top x⟩,rfl⟩
    exact hns (Group.isSolvable_of_surjective (f := P.subtype) hp)
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hnot (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
      (he : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))) : ¬ IsPGroup 2 P := by
    intro hp
    have hPS := S.is_maximal' hp hSP
    have hi := SymmetricThreeTwoCore.sylow_index_three he.some (S.subtype hSP)
    change (S : Subgroup D).relIndex P = 3 at hi
    rw [hPS,relIndex_self] at hi
    omega
  obtain ⟨f,hSf,hAf⟩ := Matrix.PSL3Two.exists_sylow_line_marking e S A hSA
    (hproper A) (hnot A hSA ht.quotient_left)
  have hBf : B.map f.toMonoidHom = Matrix.PSL3Two.pointParabolicSL := by
    have hBP : B.map f.toMonoidHom ≠ ⊤ := by
      intro hz
      apply hproper B
      exact f.mapSubgroup.injective (hz.trans f.mapSubgroup.map_top.symm)
    have hBtwo : ¬ IsPGroup 2 (B.map f.toMonoidHom) := fun hh =>
      hnot B hSB ht.quotient_right (hh.of_equiv (f.subgroupMap B).symm)
    rcases Matrix.PSL3Two.parabolic_of_borel_le_of_not_two _
      (hSf ▸ map_mono hSB) hBP hBtwo with hh | hh
    · exact hh
    · have heq : A = B := f.mapSubgroup.injective (hAf.trans hh.symm)
      have hAtop : A = ⊤ := by simpa only [←heq,sup_idem] using ht.generated
      exact (hproper A hAtop).elim
  exact ⟨f,hAf,hBf⟩

open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The surviving nonsolvable action has natural coordinates on the literal
point span. One quotient marking identifies both original vertices, and the
coordinates intertwine the original ambient conjugation. -/
theorem cubic_generated_component_natural_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
      (f : W ≃* Multiplicative BinaryLinearThree.Vector),
      (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
        Matrix.PSL3Two.pointParabolicSL ∧
      ∀ (g : D) (w : W),
        (f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
          BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e₀⟩ := cubic_generated_component_action_quotient_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,ht,_⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  obtain ⟨e,hA,hB⟩ := goldschmidt_linear_marking ht e₀
  let π := e.toMonoidHom.comp q
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  let : IsElementaryAbelian 2 W :=
    (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.1
  have hker : π.ker ≤ (centralizer (W : Set G)).subgroupOf D := by
    intro g hg
    have hq : q g = 1 := e.injective (show e (q g) = e 1 from hg.trans e.map_one.symm)
    have hgC : g ∈ C := (QuotientGroup.eq_one_iff g).mp hq
    apply mem_centralizer_iff.mpr
    intro w hw
    have hc := mem_centralizer_iff.mp hgC (⟨w,hWD hw⟩ : D) hw
    exact congrArg Subtype.val hc
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let := h.chosen.elementary
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hplane : conjugateSpanBy (F.Vi 1) (F.P L) = F.Vi 2 := by
    apply le_antisymm
    · exact conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
        (F.P_le_G₂ (by decide) L h.chosen.normalizes)
    · rw [←plane_eq_point_residual_span h structural]
      apply conjugateSpanBy_mono le_rfl
      rw [plane_parabolic_eq_join h structural]
      exact le_sup_left
  have hBZ : Y ⊔ (T : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
    (sup_le hYH (F.invariant 1)).trans (normalizer_le_centralizer_of_card_two _ hc)
  obtain ⟨f,hf⟩ := Representation.ConjugatePointNatural.exists_natural_coordinates
    D W (F.Vi 1) (F.P L) (Y ⊔ (T : Subgroup G))
    (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _) z hZ hz1
    π hπ hker le_sup_left (by rwa [←map_map]) (by rwa [←map_map]) hBZ rfl
    (by rw [hplane]; simpa using F.card 2 (by decide))
  exact ⟨e,f,hA,hB,hf⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_natural
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
      (f : W ≃* Multiplicative BinaryLinearThree.Vector),
      (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
        Matrix.PSL3Two.pointParabolicSL ∧
      ∀ (g : D) (w : W),
        (f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
          BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  apply cubic_generated_component_natural_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- In the nonsolvable branch the natural point span is exactly the
Y-span of the original plane. Its full point-normalizer span is the same
original abelian U, so intersecting conjugates of this new seed commute. -/
theorem cubic_generated_component_span_geometry_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
      W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
      IsMulCommutative (conjugateSpanBy W F.H) ∧
      ∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := h.chosen.elementary
  let := hab
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e,f,_,_,hf⟩ := cubic_generated_component_natural_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  have hW8 : Nat.card W = 8 := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    norm_num [Nat.card_fun]
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hPW : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    apply conjugateSpanBy_mono le_rfl
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  let S := conjugateSpanBy (F.Vi 2) Y
  have hSW : S ≤ W := conjugateSpanBy_le hPW
    (hYD.trans (le_normalizer_conjugateSpanBy _ _))
  have h4 : 4 ≤ Nat.card S := by
    simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using
      card_le_of_le (le_conjugateSpanBy (F.Vi 2) Y)
  have hn4 : Nat.card S ≠ 4 := by
    intro hc
    have hPS : F.Vi 2 = S := eq_of_le_of_card_ge (le_conjugateSpanBy _ _)
      (by rw [hc,F.card 2 (by decide)]; rfl)
    apply hout
    apply point_plane_normalizer_le h structural Y hYL
    rw [hPS]
    exact le_normalizer_conjugateSpanBy _ _
  have hS8 : Nat.card S = 8 := by
    have hd : Nat.card S ∣ 8 := hW8 ▸ card_dvd_of_le hSW
    have hm : Nat.card S ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have heq : Nat.divisors 8 = {1,2,4,8} := by decide
    rw [heq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  have hWS : W = S := (eq_of_le_of_card_ge hSW (by rw [hW8,hS8])).symm
  have hWU : W ≤ F.U := by
    rw [hWS]
    exact conjugateSpanBy_le ((F.le_seed 2).trans (le_conjugateSpanBy _ _))
      (hYH.trans (le_normalizer_conjugateSpanBy _ _))
  let := F.localKernel_tilde_seed_elementary
  have hspan : conjugateSpanBy W F.H = F.U := by
    apply le_antisymm
    · exact conjugateSpanBy_le hWU (le_normalizer_conjugateSpanBy _ _)
    · rw [F.U_eq_plane_span L (by decide) h.chosen.normalizes
        (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))]
      exact conjugateSpanBy_mono hPW le_rfl
  have habW : IsMulCommutative (conjugateSpanBy W F.H) := hspan.symm ▸ hab
  refine ⟨hW8,hWS,hWU,hspan,habW,?_⟩
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzW : z ∈ W := le_conjugateSpanBy _ _ (hZ ▸ mem_zpowers z)
  have htrans : ∀ x ∈ W, x ≠ 1 → ∃ n ∈ normalizer (W : Set G),
      (MulAut.conj n) z = x := by
    intro x hx hx1
    let zW : W := ⟨z,hzW⟩
    let xW : W := ⟨x,hx⟩
    have hzn : (f zW).toAdd ≠ 0 := by
      intro hh
      have hfz : f zW = 1 := hh
      exact hz1 (congrArg Subtype.val (f.injective (hfz.trans f.map_one.symm)))
    have hxn : (f xW).toAdd ≠ 0 := by
      intro hh
      have hfx : f xW = 1 := hh
      exact hx1 (congrArg Subtype.val (f.injective (hfx.trans f.map_one.symm)))
    obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hzn hxn
    obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective C)) a
    refine ⟨g,(le_normalizer_conjugateSpanBy _ _) g.property,?_⟩
    have hh := hf g zW
    change e (q g) = a at hg
    change (f (W.normalizerMonoidHom
      (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW)).toAdd =
        BinaryLinearThree.W (e (q g)) (f zW).toAdd at hh
    rw [hg] at hh
    have hfx : f (W.normalizerMonoidHom
        (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW) = f xW :=
      Multiplicative.toAdd.injective (hh.trans ha)
    exact congrArg Subtype.val (f.injective hfx)
  have hc := (point_span_abelian_iff_intersecting_conjugates_commute W hzW hz1 htrans).mp
    (show IsMulCommutative (conjugateSpanBy W (centralizer ({z} : Set G))) from
      (F.H_eq_centralizer (by decide) z hZ) ▸ habW)
  exact hc

/-- The original full point-normality interface. -/
theorem cubic_generated_component_span_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
      W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
      IsMulCommutative (conjugateSpanBy W F.H) ∧
      ∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  apply cubic_generated_component_span_geometry_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- The literal order-four chief interval supplies all inputs to natural
recognition. In the nonsolvable branch both vertices are marked and the
actual point span has the same abelian point-normalizer span as V. -/
theorem extraspecial_four_interval_cubic_natural
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      Group.IsSolvable D ∨
        Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
        W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
        (∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
          ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥) ∧
        ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
          (f : W ≃* Multiplicative BinaryLinearThree.Vector),
          (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
          (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
            Matrix.PSL3Two.pointParabolicSL ∧
          ∀ (g : D) (w : W),
            (f (W.normalizerMonoidHom
              (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
              BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  classical
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  refine ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,?_⟩
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  by_cases hs : Group.IsSolvable D
  · exact Or.inl hs
  right
  obtain ⟨J,hJD,hJ,_⟩ := cubic_generated_nonsolvable_component
    h hab structural previous faithful hn Y hYH hYp hYT hout he hs
  obtain ⟨hcW,hWY,hWU,hspan,_,hcomm⟩ := cubic_generated_component_span_geometry
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  exact ⟨hcW,hWY,hWU,hspan,hcomm,cubic_generated_component_natural
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
