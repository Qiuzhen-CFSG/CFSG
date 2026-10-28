module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp.Algebra
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp.Residual
public import Theory.ElementaryAbelian.Join

/-!
# The ambient normalizer contradiction

Two-perfectness kills the character image and then the two-group quotient
K/K∞, placing X_E in the canonical component. The commuting conjugate Uˢ
lies in C_H(U) = O₂(K). Thus component commutators normalize UUˢ. That
nontrivial elementary subgroup is already normalized by M, so maximal
two-locality identifies its normalizer with M, contradicting X_E ≰ M.

The commutator estimate is an explicit intermediate input here; the
assembly in PushingUp derives it from the universal earlier-source input.
Source: the proposed C.1.37 repair of Aschbacher–Smith 15.3.68(2), using
15.3.50 and 15.3.67, printed pp.1145,1152–1154.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A character with two-group image is trivial on a two-perfect subgroup. -/
theorem twoPerfect_le_character_kernel {C : Type*} [Group C]
    (H K X : Subgroup G) (χ : H →* C)
    (hχ : IsPGroup 2 χ.range) (hK : χ.ker.map H.subtype = K)
    (hXH : X ≤ H) (hX : IsPPerfect 2 X) : X ≤ K := by
  have ht := hX.hom_eq_one_of_isPGroup hχ (χ.rangeRestrict.comp (inclusion hXH))
  intro x hx
  rw [← hK]
  refine ⟨⟨x,hXH hx⟩, ?_, rfl⟩
  have hh := congrArg (fun f : X →* χ.range => (f ⟨x,hx⟩ : C)) ht
  exact hh

/-- Restrict C_H(U) = O₂(K) to the actual subgroup K ≤ H. -/
theorem centralizer_restrict (H K : Subgroup G) (U : Subgroup K)
    (hKH : K ≤ H)
    (hC : H ⊓ centralizer (U.map K.subtype : Set G) = (pCore 2 K).map K.subtype) :
    centralizer (U : Set K) = pCore 2 K := by
  ext x
  constructor
  · intro hx
    have hg : (x : G) ∈ H ⊓ centralizer (U.map K.subtype : Set G) := by
      refine ⟨hKH x.property, mem_centralizer_iff.mpr ?_⟩
      rintro y ⟨u,hu,rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx u hu)
    rw [hC] at hg
    obtain ⟨y,hy,he⟩ := hg
    exact (show y = x from Subtype.ext he) ▸ hy
  · intro hx
    have hg : (x : G) ∈ H ⊓ centralizer (U.map K.subtype : Set G) := by
      rw [hC]
      exact mem_map_of_mem _ hx
    apply mem_centralizer_iff.mpr
    intro u hu
    apply Subtype.ext
    exact mem_centralizer_iff.mp hg.2 u (mem_map_of_mem _ hu)

variable [Finite G]

/-- The intrinsic commutator estimate forces the ambient contradiction. -/
theorem ambient_endgame (M H K X W : Subgroup G) (U : Subgroup K) [U.Normal]
    (hXK : X ≤ K) (hX : IsPPerfect 2 X)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hC : H ⊓ centralizer (U.map K.subtype : Set G) = (pCore 2 K).map K.subtype)
    (hWH : W ≤ H) (hcomm : ⁅W, U.map K.subtype⁆ = ⊥)
    (hNU : ⁅pCore 2 K,solvableResidual K⁆ ≤ U)
    (hU : IsElementaryAbelian 2 U) (hW : IsElementaryAbelian 2 W)
    (hne : U ≠ ⊥) (hM : IsMaximalTwoLocal M)
    (hMA : M ≤ normalizer (U.map K.subtype ⊔ W : Subgroup G))
    (hXM : ¬ X ≤ M) : False := by
  let L := solvableResidual K
  let Lg := L.map K.subtype
  let Ug := U.map K.subtype
  have hWN : W ≤ (pCore 2 K).map K.subtype := by
    rw [← hC]
    exact le_inf hWH (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hLgU : Lg ≤ normalizer Ug := by
    exact (map_mono (show L ≤ normalizer U by rw [normalizer_eq_top]; exact le_top)).trans
      (U.le_normalizer_map K.subtype)
  have hWL : ⁅W,Lg⁆ ≤ Ug := by
    exact (commutator_mono hWN le_rfl).trans (by
      rw [← map_commutator]
      exact map_mono hNU)
  have hLA : Lg ≤ normalizer (Ug ⊔ W : Subgroup G) :=
    normalizes_sup_of_commutator_le Lg Ug W hLgU hWL
  have hXp : IsPPerfect 2 (X.subgroupOf K) := hX.of_surjective
    (subgroupOfEquivOfLe hXK).symm.toMonoidHom (subgroupOfEquivOfLe hXK).symm.surjective
  have hXL : X ≤ Lg := by
    have hh := map_mono (f := K.subtype)
      (twoPerfect_le_component L (X.subgroupOf K) (residual_sup_core eK) hXp)
    simpa only [map_subgroupOf_eq_of_le hXK] using hh
  let := hU
  let := hW
  let : IsElementaryAbelian 2 Ug := IsElementaryAbelian.map K.subtype
  let : IsElementaryAbelian 2 (Ug ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hUg : Ug ≠ ⊥ := fun hb => hne ((U.map_eq_bot_iff_of_injective K.subtype_injective).mp hb)
  have hA : Ug ⊔ W ≠ ⊥ := fun hb => hUg (eq_bot_iff.mpr (hb ▸ le_sup_left))
  exact false_of_normalizes_elementary_join M (Ug ⊔ W) X hM hA
    (IsElementaryAbelian.isPGroup 2 _) hMA (hXL.trans hLA) hXM

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
