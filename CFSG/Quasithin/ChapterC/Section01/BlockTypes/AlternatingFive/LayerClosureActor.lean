module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.LayerClosureRatio
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison

/-!
# The faithful actor of a split alternating-five layer

The split layer makes the original block image A₅, so its centralizer is
proper. Its normal image in a quasisimple two-core quotient is central.
Thus the literal faithful actor is quasisimple and has the same simple
central quotient. No equality between the two kernels is assumed.

Source: Aschbacher–Smith, 10.2.1, printed p.743.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem IsAlternatingBlock.quasisimple_layer_actor
    (L W : Subgroup G) [W.Normal] (h : IsAlternatingBlock L 5)
    (hUW : (blockU L).map L.subtype ≤ W)
    (hs : W = (blockU L).map L.subtype ⊔ (W ⊓ centralizer (L : Set G)))
    (hWC : W ≤ centralizer (pCore 2 G : Set G))
    [IsQuasisimple (G ⧸ pCore 2 G)] :
    let C := centralizer (W : Set G)
    IsQuasisimple (G ⧸ C) ∧
      ∃ f : (G ⧸ pCore 2 G) →* (G ⧸ C), Function.Surjective f ∧
        (∀ g, f (QuotientGroup.mk' (pCore 2 G) g) = QuotientGroup.mk' C g) ∧
        f.ker ≤ center (G ⧸ pCore 2 G) ∧
        Nonempty (((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) ≃*
          ((G ⧸ C) ⧸ center (G ⧸ C))) := by
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  have hOC : pCore 2 G ≤ C := le_centralizer_iff.mp hWC
  have hOk : pCore 2 G ≤ q.ker := by rwa [QuotientGroup.ker_mk']
  let f := QuotientGroup.lift (pCore 2 G) q hOk
  have hf : Function.Surjective f := QuotientGroup.lift_surjective_of_surjective _ q
    (QuotientGroup.mk'_surjective _) _
  obtain ⟨e⟩ := h.layer_split_quotient_image L W hUW hs q (QuotientGroup.ker_mk' _)
  have hne : L.map q ≠ ⊥ := by
    intro hb
    have hh := Nat.card_congr e.toEquiv
    rw [hb,card_bot,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  let : Nontrivial (L.map q) := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial (G ⧸ C) := (L.map q).subtype_injective.nontrivial
  have hker : f.ker ≤ center (G ⧸ pCore 2 G) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hk | ht
    · exact hk
    · have hone : ∀ a : G ⧸ C, a = 1 := by
        intro a
        obtain ⟨g,rfl⟩ := hf a
        exact MonoidHom.mem_ker.mp (ht ▸ mem_top g)
      obtain ⟨a,ha⟩ := exists_ne (1 : G ⧸ C)
      exact (ha (hone a)).elim
  exact ⟨IsQuasisimple.of_surjective f hf,f,hf,fun _ => rfl,hker,
    ⟨IsQuasisimple.centralQuotientEquiv f hf⟩⟩
end CFSG.Quasithin.ChapterC

