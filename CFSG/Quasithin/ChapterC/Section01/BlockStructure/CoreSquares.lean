module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction
/-!
# Squares and centers in short blocks

The commutator layer of a short group has exponent two and centralizes the
two-core. Thus every core square centralizes the entire group. A trivial
center consequently makes the actual two-core elementary abelian. The same argument for the ambient
core of a pair of blocks makes that entire core elementary once its common
fixed subgroup vanishes.
For an ambient block commuting with a second subgroup, triviality of the
common fixed subgroup of the ambient core also kills the block's center.

These consequences retain the actual two-core rather than identifying it
with the moved layer. Source: Aschbacher–Smith C.1.7–8, pp.123–124, used
in the common-Sylow step of 10.2.3(4), printed p.747.
-/
public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

theorem IsShort.core_square_mem_center (h : IsShort L) (x : L) (hx : x ∈ pCore 2 L) :
    x ^ 2 ∈ center L := by
  let := h.elementary
  apply mem_center_iff.mpr
  intro l
  let c := l*x*l⁻¹*x⁻¹
  have hc : c ∈ blockU L := by
    rw [blockU,commutator_comm]
    exact commutator_mem_commutator (mem_top l) hx
  have hcx : Commute c x := (h.central hc x hx).symm
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
  have he : (l*x*l⁻¹)^2 = x^2 := by
    calc
      (l*x*l⁻¹)^2 = (c*x)^2 := by congr 1; dsimp [c]; group
      _ = c^2*x^2 := hcx.mul_pow 2
      _ = x^2 := by rw [hc2,one_mul]
  calc
    l*x^2 = (l*x*l⁻¹)^2*l := by simp only [pow_two]; group
    _ = x^2*l := by rw [he]

theorem IsShort.core_elementary_of_center_eq_bot (h : IsShort L) (hz : center L = ⊥) :
    IsElementaryAbelian 2 (pCore 2 L) := by
  have hp (x : pCore 2 L) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact mem_bot.mp (hz ▸ h.core_square_mem_center x x.property)
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

variable {G : Type*} [Group G] [Finite G]
theorem IsBlock.center_eq_bot_of_pair_core_centralizer
    {K B : Subgroup G} (hK : IsBlock K) (hc : ⁅K,B⁆ = ⊥)
    (hz : pCore 2 G ⊓ centralizer ((K ⊔ B : Subgroup G) : Set G) = ⊥) :
    center K = ⊥ := by
  apply bot_unique
  intro k hk
  have hkc : k ∈ pCore 2 K := by
    rw [←hK.short.centralizer_blockU]
    exact (center_le_centralizer _) hk
  have hkQ : (k : G) ∈ pCore 2 G :=
    pCoreIn_le_of_subnormal 2 hK.subnormal (mem_map_of_mem K.subtype hkc)
  have hkcen : (k : G) ∈ centralizer ((K ⊔ B : Subgroup G) : Set G) := by
    have hkK : (k : G) ∈ centralizer (K : Set G) := by
      intro x hx
      exact congrArg K.subtype (mem_center_iff.mp hk ⟨x,hx⟩)
    have hkB : (k : G) ∈ centralizer (B : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp hc) k.property
    have hi : centralizer (K : Set G) ⊓ centralizer (B : Set G) ≤
        centralizer ((K ⊔ B : Subgroup G) : Set G) :=
      le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp inf_le_left)
        (le_centralizer_iff.mp inf_le_right))
    exact hi ⟨hkK,hkB⟩
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hz ▸ (show (k : G) ∈
    pCore 2 G ⊓ centralizer ((K ⊔ B : Subgroup G) : Set G) from ⟨hkQ,hkcen⟩))))
/-- Every ambient-core square fixes a block. -/
theorem IsBlock.ambient_core_square_centralizes
    {K : Subgroup G} (hK : IsBlock K) (x : G) (hx : x ∈ pCore 2 G) :
    x ^ 2 ∈ centralizer (K : Set G) := by
  let V := (blockU K).map K.subtype
  let : IsElementaryAbelian 2 V := hK.short.elementary.map K.subtype
  intro k hk
  let c := k*x*k⁻¹*x⁻¹
  have hc : c ∈ V := by
    apply commutator_le_core_commutator_of_isSubnormal K (pCore 2 G)
      hK.subnormal hK.short.twoPerfect pCore_isPGroup le_normalizer_of_normal
    rw [commutator_comm]
    exact commutator_mem_commutator hk hx
  have hcx : Commute c x := hK.core_centralizes_blockU hx c hc
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
  have he : (k*x*k⁻¹)^2 = x^2 := by
    calc
      (k*x*k⁻¹)^2 = (c*x)^2 := by congr 1; dsimp [c]; group
      _ = c^2*x^2 := hcx.mul_pow 2
      _ = x^2 := by rw [hc2,one_mul]
  calc
    k*x^2 = (k*x*k⁻¹)^2*k := by simp only [pow_two]; group
    _ = x^2*k := by rw [he]

/-- A block pair with no common core fixed point has elementary ambient core. -/
theorem IsBlock.ambient_core_elementary_of_pair_core_centralizer
    {K B : Subgroup G} (hK : IsBlock K) (hB : IsBlock B)
    (hz : pCore 2 G ⊓ centralizer ((K ⊔ B : Subgroup G) : Set G) = ⊥) :
    IsElementaryAbelian 2 (pCore 2 G) := by
  have hp (x : pCore 2 G) : x ^ 2 = 1 := by
    apply Subtype.ext
    have hi : centralizer (K : Set G) ⊓ centralizer (B : Set G) ≤
        centralizer ((K ⊔ B : Subgroup G) : Set G) :=
      le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp inf_le_left)
        (le_centralizer_iff.mp inf_le_right))
    exact mem_bot.mp (hz ▸ (show (x : G)^2 ∈
      pCore 2 G ⊓ centralizer ((K ⊔ B : Subgroup G) : Set G) from
        ⟨(pCore 2 G).pow_mem x.property 2,hi
          ⟨hK.ambient_core_square_centralizes x x.property,
           hB.ambient_core_square_centralizes x x.property⟩⟩))
  exact {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hp x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }
end CFSG.Quasithin.ChapterC
