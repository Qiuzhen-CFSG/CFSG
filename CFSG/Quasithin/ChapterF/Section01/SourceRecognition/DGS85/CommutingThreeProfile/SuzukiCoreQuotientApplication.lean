module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreApplication

/-!
# Discharging the Suzuki middle-core quotient after the product application

`SuzukiCoreApplication` retains the source's central quotient alternative: the
middle-core image has quotient order one or the Suzuki Sylow-center order.  Once
its literal product application has proved that the middle-core subgroup is the
whole middle core, the quotient is necessarily trivial.  This extension keeps
the denominator and quotient map exactly as in the source application and
returns the centrality clause together with the sharpened order-one conclusion.

The source product, common-Sylow markings, natural-center data and the
Chapter 8 hypotheses remain producers of the two inputs.  This theorem is the
small assembly step used after those producers; it does not select the
Chapter 12.9 alternatives or reconstruct the binary Chapter 13 completion.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(12.3), printed pp.178--180.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem quotient_map_card_one_of_eq {A : Type*} [Group A]
    (N Q : Subgroup A) [hN : N.Normal] (h : N = Q) :
    Nat.card (Q.map (QuotientGroup.mk' N)) = 1 := by
  rw [← h]
  have hk : N.map (QuotientGroup.mk' N) = ⊥ := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    · exact bot_le
  rw [hk]
  simp

/-- The literal Suzuki quotient is trivial once the source middle-core product
has been established. -/
theorem source_suzuki_middle_core_quotient_trivial_of_product
    (i : Bool) {n : ℕ} {x : Vertex (reducedFamily L S)}
    (hExact :
      let F := reducedFamily L S
      let A := star L S (!i)
      let m := base F (!i)
      let y := base F i
      let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
      ∃ hN : (N.subgroupOf A).Normal,
        let _ : (N.subgroupOf A).Normal := hN
        ((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A)) ≤
          center (A ⧸ N.subgroupOf A) ∧
        (Nat.card (((Q F m).subgroupOf A).map
          (QuotientGroup.mk' (N.subgroupOf A))) = 1 ∨
          Nat.card (((Q F m).subgroupOf A).map
            (QuotientGroup.mk' (N.subgroupOf A))) = 2 ^ (2 * n + 1)))
    (hprod :
      let F := reducedFamily L S
      let m := base F (!i)
      let y := base F i
      let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
      N = Q F m) :
    let F := reducedFamily L S
    let A := star L S (!i)
    let m := base F (!i)
    let y := base F i
    let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
    ∃ hN : (N.subgroupOf A).Normal,
      let _ : (N.subgroupOf A).Normal := hN
      ((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A)) ≤
          center (A ⧸ N.subgroupOf A) ∧
      Nat.card (((Q F m).subgroupOf A).map
        (QuotientGroup.mk' (N.subgroupOf A))) = 1 := by
  let F := reducedFamily L S
  let A := star L S (!i)
  let m := base F (!i)
  let y := base F i
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  have hExact' : ∃ hN : (N.subgroupOf A).Normal,
      let _ : (N.subgroupOf A).Normal := hN
      ((Q F m).subgroupOf A).map (QuotientGroup.mk' (N.subgroupOf A)) ≤
        center (A ⧸ N.subgroupOf A) ∧
      (Nat.card (((Q F m).subgroupOf A).map
        (QuotientGroup.mk' (N.subgroupOf A))) = 1 ∨
        Nat.card (((Q F m).subgroupOf A).map
          (QuotientGroup.mk' (N.subgroupOf A))) = 2 ^ (2 * n + 1)) := by
    simpa only [F, A, m, y, N] using hExact
  have hprod' : N = Q F m := by
    simpa only [F, m, y, N] using hprod
  dsimp only [F, A, m, y, N]
  obtain ⟨hN, hcentral, _⟩ := hExact'
  let _ : (N.subgroupOf A).Normal := hN
  have hsub : N.subgroupOf A = (Q F m).subgroupOf A := by
    rw [hprod']
  refine ⟨hN, hcentral, ?_⟩
  exact quotient_map_card_one_of_eq (N.subgroupOf A) ((Q F m).subgroupOf A) hsub

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
