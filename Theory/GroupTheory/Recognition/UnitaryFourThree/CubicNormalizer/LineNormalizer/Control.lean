module

public import Theory.GroupTheory.IndexTwoFourCentralizerControl
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Frattini

/-!
# Normalizer closure for an original cubic line

The canonical odd kernel V is elementary by the preceding source argument.
For U≤X of order three, V therefore centralizes U.  Local centralizer and
four-group normalizer bounds inside the literal N_G(U) force all of N_G(U)
to normalize V.  The earlier local bounds are retained explicitly here;
this theorem does not assume a global normalizer conclusion.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.7(3), printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The closure step, with the original Sylow image and its canonical kernel. -/
theorem cubic_line_normalizer_control (h : IsType z) (P : Sylow 3 (centralizer z))
    (U : Subgroup G) (hU : Nat.card U = 3)
    (hUX : U ≤ (P : Subgroup (centralizer z)).map (centralizer z).subtype)
    (hV : IsElementaryAbelian 3 (CubicNormalizer.oddKernel
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype)))
    (T : Sylow 2 (normalizer (U : Set G)))
    (hTI : (T : Subgroup (normalizer (U : Set G))) ≤
      (normalizer (CubicNormalizer.oddKernel
        ((P : Subgroup (centralizer z)).map (centralizer z).subtype) : Set G)).subgroupOf
          (normalizer (U : Set G)))
    (hA : Nat.card ((T : Subgroup (normalizer (U : Set G))) ⊓
      (Subgroup.centralizer (U : Set G)).subgroupOf (normalizer (U : Set G)) :
        Subgroup (normalizer (U : Set G))) = 4)
    (hn : normalizer (((T : Subgroup (normalizer (U : Set G))) ⊓
      (Subgroup.centralizer (U : Set G)).subgroupOf (normalizer (U : Set G))) :
        Set (normalizer (U : Set G))) ≤
      (normalizer (CubicNormalizer.oddKernel
        ((P : Subgroup (centralizer z)).map (centralizer z).subtype) : Set G)).subgroupOf
          (normalizer (U : Set G)))
    (hc : ∀ x ∈ (T : Subgroup (normalizer (U : Set G))), orderOf x = 2 →
      Subgroup.centralizer ({x} : Set (normalizer (U : Set G))) ≤
        (normalizer (CubicNormalizer.oddKernel
          ((P : Subgroup (centralizer z)).map (centralizer z).subtype) : Set G)).subgroupOf
            (normalizer (U : Set G)))
    (a b : normalizer (U : Set G)) (ha : a ∈ T) (hb : b ∈ T)
    (hao : orderOf a = 2) (hbo : orderOf b = 2)
    (haC : (a : G) ∈ Subgroup.centralizer (U : Set G))
    (hbC : (b : G) ∉ Subgroup.centralizer (U : Set G)) :
    let V := CubicNormalizer.oddKernel
      ((P : Subgroup (centralizer z)).map (centralizer z).subtype)
    V ≤ normalizer (U : Set G) ∧
      (V.subgroupOf (normalizer (U : Set G))).Normal ∧
      normalizer (U : Set G) ≤ normalizer (V : Set G) := by
  let V := CubicNormalizer.oddKernel
    ((P : Subgroup (centralizer z)).map (centralizer z).subtype)
  have hXV : (P : Subgroup (centralizer z)).map (centralizer z).subtype ≤ V := by
    rw [← (h.cubic_sylow_structure P).2.2.2.2.1]
    exact inf_le_left
  have hUV : U ≤ V := hUX.trans hXV
  let : IsElementaryAbelian 3 V := hV
  have hVC : V ≤ Subgroup.centralizer (U : Set G) := by
    intro v hv u hu
    exact congrArg Subtype.val (mul_comm' (⟨u,hUV hu⟩ : V) (⟨v,hv⟩ : V))
  have hVN : V ≤ normalizer (U : Set G) := hVC.trans (centralizer_le_normalizer _)
  have hN := normalizer_le_of_card_three_four_centralizers U (normalizer (V : Set G))
    hU T hTI hA hn hc a b ha hb hao hbo haC hbC
  exact ⟨hVN, (normal_subgroupOf_iff_le_normalizer hVN).mpr hN, hN⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
