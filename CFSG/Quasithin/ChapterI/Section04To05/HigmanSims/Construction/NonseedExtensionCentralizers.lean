module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExtensionNormalization
public import Theory.GroupTheory.AbelianIndexTwoCenter
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CoreElementaryBound

/-!
# The two original elementary-sixteen extensions are self-centralizing

Each displayed sixteen has index two in the full centralizer of its eight.
That centralizer has center precisely the eight, so it is nonabelian. The
abelian index-two lemma therefore computes the full centralizer of each
sixteen in the original group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem extension_self_centralizing (E A : Subgroup G)
    (hE8 : Nat.card E = 8) (hEA : E ≤ A) [IsMulCommutative A]
    (hA16 : Nat.card A = 16) (hK32 : Nat.card (centralizer (E : Set G)) = 32)
    (hZ : (center (centralizer (E : Set G))).map
      (centralizer (E : Set G)).subtype = E) :
    centralizer (A : Set G) = A := by
  let K := centralizer (E : Set G)
  have hAK : A ≤ K := by
    intro a ha e he
    exact setLike_mul_comm (hEA he) ha
  let AK := A.subgroupOf K
  let : IsMulCommutative AK :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (setLike_mul_comm (show ((a : K) : G) ∈ A from a.property)
        (show ((b : K) : G) ∈ A from b.property)))⟩⟩
  have hAc : Nat.card AK = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv).trans hA16
  have hi : AK.index = 2 := by
    have hh := AK.card_mul_index
    rw [hAc, hK32] at hh
    omega
  have hn : ¬ IsMulCommutative K := by
    intro hh
    let := hh
    have hz : center K = ⊤ := center_eq_top
    have hc := congrArg (fun S : Subgroup G => Nat.card S) hZ
    rw [card_map_of_injective K.subtype_injective, hz, card_top, hK32, hE8] at hc
    omega
  have hc := centralizer_eq_of_abelian_index_two AK hi hn
  apply le_antisymm ?_ A.le_centralizer
  intro x hx
  have hxK : x ∈ K := centralizer_le hEA hx
  have hxC : (⟨x, hxK⟩ : K) ∈ centralizer (AK : Set K) := by
    intro a ha
    exact Subtype.ext (hx a ha)
  rw [hc] at hxC
  exact hxC

private theorem extension_core_intersection (h : TypeAt z V)
    (E : pointCoreEights z) (A : Subgroup G) (hEA : E.val ≤ A)
    [IsElementaryAbelian 2 A] : A ⊓ (involutionCentralizer z).pCoreIn 2 = E.val := by
  let Q := (involutionCentralizer z).pCoreIn 2
  have hEcap : E.val ≤ A ⊓ Q := le_inf hEA E.property.1
  apply (eq_of_le_of_card_ge hEcap ?_).symm
  let D := (A ⊓ Q : Subgroup G).subgroupOf Q
  let j : D →* A := {
    toFun x := ⟨x, x.property.1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) he
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective j hj
  have hs : CoreShape Q := (h.centralizer_core.of_equiv
    (MulEquiv.subgroupCongr h.centralizer_fitting)).of_equiv
      ((pCore 2 (involutionCentralizer z)).equivMapOfInjective
        (involutionCentralizer z).subtype (involutionCentralizer z).subtype_injective)
  have hb := hs.elementary_card_le_eight D inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ Q ≤ Q from inf_le_right)).toEquiv] at hb
  rw [E.property.2.2.2]
  exact hb

/-- The original construction yields the same two literal extensions with
full ambient self-centralizers, while retaining their original point core,
central lift, known involution class, and complete extension classification. -/
theorem TypeAt.exists_selfcentralizing_nonseed_extensions (h : TypeAt z V) :
    ∃ (u c b : G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧ E.val ∉ pointCoreSeedOrbit u V ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      orderOf c = 4 ∧ c ^ 2 = u ∧
      c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
        ((involutionCentralizer u).pCoreIn 2).subtype ∧
      b ^ 2 = 1 ∧ IsConj b z ∧ ¬ Commute b c ∧ b * c * b⁻¹ = c⁻¹ ∧
      (center (centralizer (E.val : Set G))).map
        (centralizer (E.val : Set G)).subtype = E.val ∧
      let A := E.val ⊔ zpowers b
      let B := E.val ⊔ zpowers (c * b)
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E.val ∧
      (involutionCentralizer u).pCoreIn 2 ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ (involutionCentralizer u).pCoreIn 2 = E.val ∧
      B ⊓ (involutionCentralizer u).pCoreIn 2 = E.val ∧
      (∀ F : Subgroup G,
        (E.val ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768,
    hc4, hc2, hcZ, hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN, hall⟩ :=
    h.exists_core_normalized_nonseed_eight_extensions
  let := hAe
  let := hBe
  exact ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768,
    hc4, hc2, hcZ, hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    extension_self_centralizing E.val _ E.property.2.2.2 le_sup_left hA16 hK32 hcenter,
    extension_self_centralizing E.val _ E.property.2.2.2 le_sup_left hB16 hK32 hcenter,
    extension_core_intersection huT E _ le_sup_left,
    extension_core_intersection huT E _ le_sup_left, hall⟩

end CFSG.Quasithin.HigmanSims
