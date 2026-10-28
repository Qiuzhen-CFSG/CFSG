module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Normalizer.LocalStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.Normalizer.Affine
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Counting.SectionFive.MaximalFixed

/-!
# A maximal three-point subgroup has a distinguished normalizer

Let W be maximal among p-subgroups fixing at least three cosets. Its normalizer
is doubly transitive on the fixed set by the Bender–Witt lemma. If that normalizer
had trivial distinguished circle, source 16.6(e) and the affine calculation
would make each nonempty subgroup fixed set odd. A Sylow p-overgroup in a
pair stabilizer is larger than W, since otherwise Section 3 supplies a
distinguished normalizing swap. Normalizer growth inside that p-group gives
a larger subgroup normalizing W and fixing exactly two points, a contradiction.

Source: GLS IV, Chapter 2, Lemma 16.7, middle paragraphs.
-/

noncomputable section
namespace BenderSuzuki.ZD.Section16.NativeSource
open Subgroup Theory.GroupTheory PFAppendixIII PFchapter1section1 MulAction
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Maximality is in the original ambient p-subgroup lattice and counts literal cosets. -/
public theorem maximal_fixed_normalizer_circle_ne_bot
    (h : IsProductDisconnected Z M) (ha : ResidualAction Z M)
    (hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (W : Subgroup G)
    (hmax : Maximal (fun Q : Subgroup G => IsPGroup p Q ∧
      2 < Nat.card (theorem4bFixedPoints M Q)) W) :
    localCircleIn Z (normalizer (W : Set G)) ≠ ⊥ := by
  intro hbot
  let N := normalizer (W : Set G)
  have hnobot (s : G) (hs : s ∈ Z) (hsN : s ∈ N) : False := by
    have hm : s ∈ localCircleIn Z N := by
      rw [localCircleIn_eq_closure]
      exact subset_closure ⟨hs, hsN⟩
    rw [hbot, mem_bot] at hm
    exact (h.involutions s hs).ne_one hm
  have hcircle : closure (N.subtype ⁻¹' Z) = ⊥ := by
    apply le_antisymm ?_ bot_le
    apply (closure_le _).mpr
    intro s hs
    exact (hnobot s hs s.property).elim
  obtain ⟨hcomp, hcyc⟩ := hlocal N hcircle
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M W) := hmax.1.2
  let F := theorem4bFixedPoints M W
  let : Nonempty F := (Nat.card_pos_iff.mp (show 0 < Nat.card F from lt_of_lt_of_le (by decide : 0 < 3) hthree)).1
  let : MulAction N F := normalizerFixedPointAction G (G ⧸ M) W
  have htwo : IsMultiplyPretransitive N F 2 := normalizerFixedPointAction_twoPretransitive W
    (chapter1_bender_normalizer_two_pretransitive hp ha.two_transitive W hmax)
  let a : F := Classical.choice inferInstance
  have hcard : (3 : Cardinal) ≤ Cardinal.mk F := by
    rw [← Nat.cast_card]
    exact_mod_cast hthree
  obtain ⟨b, hba, _⟩ := Cardinal.exists_ne_ne_of_three_le hcard a a
  let D := stabilizer G (a : G ⧸ M) ⊓ stabilizer G (b : G ⧸ M)
  have hab : (a : G ⧸ M) ≠ b := fun he => hba (Subtype.ext he.symm)
  have hWD : W ≤ D := fun x hx => ⟨a.property x hx, b.property x hx⟩
  let WD := W.subgroupOf D
  have hWDp : IsPGroup p WD := hmax.1.1.of_equiv (subgroupOfEquivOfLe hWD).symm
  obtain ⟨S, hWS⟩ := hWDp.exists_le_sylow
  let R := (S : Subgroup D).map D.subtype
  have hWR : W ≤ R := by
    intro x hx
    exact ⟨⟨x, hWD hx⟩, hWS hx, rfl⟩
  have hRD : R ≤ D := map_subtype_le _
  have hRp : IsPGroup p R := S.isPGroup'.map D.subtype
  have hWRlt : W < R := by
    refine lt_of_le_of_ne hWR ?_
    intro he
    obtain ⟨s, hs, hsR, _⟩ := sectionFive_distinguished_sylow_swap h
      (actionSectionThree_of_productDisconnected h) hp hpodd hab (show
        theorem4bIsSylowSubgroupOf p R D from ⟨S, rfl⟩)
    exact hnobot s hs (by change s ∈ normalizer (W : Set G); rwa [he])
  obtain ⟨P, hPp, hWP, hPR, hPN⟩ := exists_larger_normalizer_pSubgroup hp hRp hWRlt
  have hPD : P ≤ D := hPR.trans hRD
  have haP : (a : G ⧸ M) ∈ fixedPointsOfSubgroup G (G ⧸ M) P :=
    fun x hx => (hPD hx).1
  have hbP : (b : G ⧸ M) ∈ fixedPointsOfSubgroup G (G ⧸ M) P :=
    fun x hx => (hPD hx).2
  have hPcard : Nat.card (theorem4bFixedPoints M P) = 2 := by
    apply Nat.le_antisymm
    · by_contra hnot
      exact (not_le_of_gt hWP) (hmax.2 ⟨hPp, by omega⟩ hWP.le)
    · let f : Fin 2 → theorem4bFixedPoints M P := fun i =>
        if i = 0 then ⟨a, haP⟩ else ⟨b, hbP⟩
      have hf : Function.Injective f := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · rfl
        · exact (hab (by simpa [f] using congrArg Subtype.val hij)).elim
        · exact (hab (by simpa [f] using (congrArg Subtype.val hij).symm)).elim
        · rfl
      simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf
  let PN := P.subgroupOf N
  have haPN : a ∈ fixedPointsOfSubgroup N F PN := by
    intro x hx
    exact Subtype.ext (haP x hx)
  have hodd := odd_fixed_card_of_normal_two_complement htwo hthree hcomp hcyc PN a haPN
  let e : {x : F // x ∈ fixedPointsOfSubgroup N F PN} ≃ theorem4bFixedPoints M P :=
    { toFun := fun x => ⟨x.val.val, fun p hp =>
        congrArg Subtype.val (x.property (⟨p, hPN hp⟩ : N) hp)⟩
      invFun := fun x => ⟨⟨x.val, fun w hw => x.property w (hWP.le hw)⟩,
        fun p hp => Subtype.ext (x.property p hp)⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, hPcard] at hodd
  norm_num at hodd

end BenderSuzuki.ZD.Section16.NativeSource
