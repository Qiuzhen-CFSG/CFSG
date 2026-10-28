module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.ActionBounds
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ProjectiveIndices
public import Theory.SpecificGroups.PSL3.CubicComponentAction
public import Theory.SpecificGroups.PSL3.ExtensionBorel.Linear
public import Theory.GroupTheory.PCorePrimeToIndex

/-!
# A marked cubic extension of a normal linear-three component

A complementary cubic acting on a normal c-component with PSL₃(4) quotient
has an inner-diagonal action, by the SQTK cubic-rank bound. Its image is
PGL₃(4), and the kernel is exactly the component's intrinsic two-core.
The resulting projection agrees with the original component marking.

This is the common group calculation for the legacy and corrected-source
nonblock constructions. It selects no representation extension.
Source: Aschbacher--Smith A.3.18 and the conclusion of original 4.3.2,
printed pp.51--53 and 618--619.
-/

open CFSG.Quasithin Subgroup Theory.GroupTheory
open Theory.GroupAction.ComponentRankAction
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]

section
variable {H S : Type*} [Group H] [Finite H] [Group S]
 {B : Subgroup H} [B.Normal] [Group.IsPerfect B]

private theorem split_action_injective (hz : center B = ⊥) (hr : 2 ≤ primeRank 3 B)
  (hb : primeRank 3 H ≤ 2) (a : H) (ha : orderOf a = 3)
  (hgen : B ⊔ zpowers a = ⊤) (e : B ⧸ center B ≃* S) :
  Function.Injective (normalAction B e) := by
  have hcop : Nat.Coprime 3 (Nat.card (centralizer (B : Set H))) :=
    centralizer_coprime B (by simp [hz]) hr hb
  have hd : B.index ∣ 3 := by
    have hh := B.relIndex_dvd_card (K := zpowers a)
    rwa [Nat.card_zpowers, ha, ← relIndex_sup_left (zpowers a) B, hgen,
      relIndex_top_right] at hh
  have hi : B ⊓ centralizer (B : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    have hx' : (⟨x,hx.1⟩ : B) ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx.2 y y.property)
    rw [hz, mem_bot] at hx'
    exact congrArg Subtype.val hx'
  have hc : Nat.card (centralizer (B : Set H)) ∣ 3 := by
    have hh := B.relIndex_dvd_index_of_normal (centralizer (B : Set H))
    rw [← inf_relIndex_right, hi, relIndex_bot_left] at hh
    exact hh.trans hd
  have hc1 : Nat.card (centralizer (B : Set H)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hc dvd_rfl
  rw [← MonoidHom.ker_eq_bot_iff, normalAction_ker]
  exact Subgroup.card_eq_one.mp hc1
end

private theorem marked_extension (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple H)
    {B : Subgroup H} [B.Normal] (hB : IsComponent H B)
    (hz : center B = ⊥) (hF : Nat.card F = 4)
    (e : B ⧸ center B ≃* PSL(3,F))
    (a : H) (ha : orderOf a = 3) (haB : a ∉ B) (hgen : B ⊔ zpowers a = ⊤) :
    ∃ E : H ≃* Matrix.ProjGenLinGroup (Fin 3) F,
      ∀ x : H, (pglEquivInnerDiagonal F (E x)).val = normalAction B e x := by
  let := hB.2
  have hZ : IsPGroup 2 (center B) := by rw [hz]; exact IsPGroup.of_subsingleton 2 _
  have hfa : normalAction B e a ∈ innerDiagonal F :=
    Matrix.PSL3.CubicComponentAction.cubic_innerDiagonal hB hZ
      (hH.stronglyQuasithin 3 Nat.prime_three (by decide)) (by decide : 0 < 2)
      hF (by decide : Even 2) e ⟨a, by rw [B.normalizer_eq_top]; trivial⟩
      (Subtype.ext (ha ▸ pow_orderOf_eq_one a))
  let f := normalAction B e
  have hi : MulAut.innerSubgroup PSL(3,F) ≤ f.range := by
    rw [← normalAction_component_image B e]
    exact map_le_range _ _
  have hle : f.range ≤ innerDiagonal F := by
    rw [MonoidHom.range_eq_map, ← hgen, Subgroup.map_sup,
      normalAction_component_image, MonoidHom.map_zpowers]
    exact sup_le (inner_le_innerDiagonal F) (zpowers_le.mpr hfa)
  have hz3 : Nat.Coprime 3 (Nat.card (center B)) := by rw [hz]; simp
  have hr : 1 < primeRank 3 B := lt_of_lt_of_le (by decide : 1 < 2)
    (Matrix.PSL3.CubicComponentAction.component_rank hZ hF (by decide : Even 2) e)
  have hne : f.range ≠ MulAut.innerSubgroup PSL(3,F) := by
    intro he
    exact outside_action_not_inner hz3 hr (hH.stronglyQuasithin 3 Nat.prime_three
      (by decide)) e a ha haB (he ▸ (show f a ∈ f.range from ⟨a,rfl⟩))
  have he : f.range = innerDiagonal F := by
    apply actionImage_eq_of_index_three _ _ _ hi hle hne
    rw [← Nat.card_congr (pglEquivInnerDiagonal F).toEquiv,
      card_pgl_three_eq_three_mul_psl (by rw [hF])]
    congr 1
    exact Nat.card_congr (MonoidHom.ofInjective (inner_injective F)).toEquiv
  have hinj := split_action_injective hz (by omega : 2 ≤ primeRank 3 B)
    (hH.stronglyQuasithin 3 Nat.prime_three (by decide)) a ha hgen e
  let E := (MonoidHom.ofInjective hinj).trans
    ((MulEquiv.subgroupCongr he).trans (pglEquivInnerDiagonal F).symm)
  refine ⟨E, ?_⟩
  intro x
  simp only [E, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

/-- A normal c-component with PSL₃(4) quotient and a complementary cubic
gives the marked PGL₃(4) extension, with its exact intrinsic two-core. -/
theorem cubic_extension_of_normal_component (hH : IsSQTK CFSG.KnownSimple.IsKnownSimple H)
    {B : Subgroup H} [B.Normal] (hB : B.IsCComponent)
    [IsQuasisimple (B ⧸ pCore 2 B)] (hF : Nat.card F = 4)
    (e : B ⧸ pCore 2 B ≃* PSL(3,F))
    (a : H) (ha : orderOf a = 3) (haB : a ∉ B) (hgen : B ⊔ zpowers a = ⊤) :
    ∃ φ : H →* Matrix.ProjGenLinGroup (Fin 3) F,
      Function.Surjective φ ∧ φ.ker = B.pCoreIn 2 ∧
      pCore 2 H = B.pCoreIn 2 ∧ ∀ b : B, φ b = Matrix.ProjectiveSpecialLinearGroup.toPGL
          (e (QuotientGroup.mk' (pCore 2 B) b)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := twoCoreComponent B
  let := twoCore_normal B
  have hC := twoCore_isComponent hB
  let := hC.2
  let ec : C ≃* PSL(3,F) := (twoCoreComponentEquiv hB).trans e
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  have hz : center C = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hx' : ec x ∈ center PSL(3,F) := ((centerCongr ec) ⟨x,hx⟩).property
    rw [Group.IsPerfect.center_quotient_center_eq_bot SL(3,F), mem_bot] at hx'
    exact mem_bot.mpr (ec.map_eq_one_iff.mp hx')
  let ez : C ⧸ center C ≃* PSL(3,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans ec
  have ha' := twoCore_actor Nat.prime_three (by decide) a ha haB
  obtain ⟨E,hE⟩ := marked_extension (twoCore_sqtk hH) hC hz hF ez (q a)
    ha'.1 ha'.2 (twoCore_join a hgen)
  let φ := E.toMonoidHom.comp q
  have hd : B.index ∣ 3 := by
    have hh := B.relIndex_dvd_card (K := zpowers a)
    rwa [Nat.card_zpowers, ha, ← relIndex_sup_left (zpowers a) B, hgen,
      relIndex_top_right] at hh
  have hcore : pCore 2 H = B.pCoreIn 2 := le_antisymm
    (pCore_le_map_pCore_of_prime_not_dvd_index B (fun hh => by
      have : 2 ∣ 3 := hh.trans hd
      norm_num at this))
    (pCoreIn_le_of_subnormal 2 hB.subnormal)
  refine ⟨φ, E.surjective.comp (QuotientGroup.mk'_surjective _), ?_, hcore, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ E.injective, QuotientGroup.ker_mk']
    exact hcore
  · intro b
    apply (pglEquivInnerDiagonal F).injective
    apply Subtype.ext
    rw [pglEquiv_component]
    change (pglEquivInnerDiagonal F (E (q b))).val = _
    rw [hE]
    have hc := action_on_component C ez (q.subgroupMap B b)
    refine hc.trans (congrArg MulAut.conj ?_)
    change e ((cComponentTwoCoreQuotientEquiv hB).symm (q.subgroupMap B b)) = _
    exact congrArg e ((cComponentTwoCoreQuotientEquiv hB).symm_apply_apply
      (QuotientGroup.mk' (pCore 2 B) b))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
end
