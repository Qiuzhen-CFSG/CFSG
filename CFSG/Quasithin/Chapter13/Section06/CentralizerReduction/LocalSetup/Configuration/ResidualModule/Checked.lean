module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Product

/-!
# Images in the literal checked centralizer

Every checked subgroup is mapped from its restriction to C_G(v) through
C_G(v) → C_G(v)/⟨v⟩. The line factor vanishes, so the checked span is the
commutator of the checked V and checked Lᵥ. Disjointness from the v-line
makes the quotient injective on [V,Lᵥ], giving its actual checked image
isomorphism. The flag application uses only its marking and original kernel.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.926.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry ResidualCoordinates
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G]

/-- The specified quotient homomorphism, with its checked codomain explicit. -/
def checkedQuotientMap (v : G) : Gv v →* Gcheck v := QuotientGroup.mk' (vLine v)

theorem checkedQuotientMap_kernel (v : G) : (checkedQuotientMap v).ker = vLine v :=
  QuotientGroup.ker_mk' _

theorem line_le_Gv (v : G) : zpowers v ≤ Gv v :=
  zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

/-- Always the literal restriction to C_G(v), followed by its quotient map. -/
def checkedImage (v : G) (H : Subgroup G) : Subgroup (Gcheck v) :=
  (H.subgroupOf (Gv v)).map (checkedQuotientMap v)

theorem checkedImage_commutator (v : G) (H K : Subgroup G)
    (hH : H ≤ Gv v) (hK : K ≤ Gv v) :
    checkedImage v ⁅H, K⁆ = ⁅checkedImage v H, checkedImage v K⁆ := by
  unfold checkedImage
  rw [← map_commutator]
  congr 1
  apply Subgroup.map_injective (Gv v).subtype_injective
  rw [map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup H K).trans (sup_le hH hK)),
    map_commutator, map_subgroupOf_eq_of_le hH, map_subgroupOf_eq_of_le hK]

theorem vLine_map_subtype (v : G) : (vLine v).map (Gv v).subtype = zpowers v := by
  rw [vLine, MonoidHom.map_zpowers]
  rfl

theorem line_subgroupOf (v : G) : (zpowers v).subgroupOf (Gv v) = vLine v := by
  apply Subgroup.map_injective (Gv v).subtype_injective
  rw [map_subgroupOf_eq_of_le (line_le_Gv v), vLine_map_subtype]

theorem checkedImage_line (v : G) : checkedImage v (zpowers v) = ⊥ := by
  rw [checkedImage, line_subgroupOf]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [checkedQuotientMap_kernel])

variable {L V : Subgroup G} (s : Marking L V)

theorem module_le_Gv : V ≤ Gv (markedV s) := by
  let := module_abelian s
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hx (map_mem s (Multiplicative.ofAdd v)))

variable [Finite G]

def checkedV : Subgroup (Gcheck (markedV s)) := checkedImage (markedV s) V
def checkedLv : Subgroup (Gcheck (markedV s)) := checkedImage (markedV s) (Lv L (markedV s))
def checkedVv : Subgroup (Gcheck (markedV s)) := checkedImage (markedV s) (Vv L (markedZ s) (markedV s))

theorem checkedVv_eq_checked_commutator :
    checkedVv s = checkedImage (markedV s) ⁅V, Lv L (markedV s)⁆ := by
  unfold checkedVv
  rw [Vv_eq_line_sup_commutator s, checkedImage,
    subgroupOf_sup (line_le_Gv (markedV s))
      ((residual_commutator_le_module s).trans (module_le_Gv s)), Subgroup.map_sup]
  change checkedImage (markedV s) (zpowers (markedV s)) ⊔ _ = _
  rw [checkedImage_line, bot_sup_eq]
  rfl

theorem checkedVv_eq_commutator : checkedVv s = ⁅checkedV s, checkedLv s⁆ := by
  rw [checkedVv_eq_checked_commutator s,
    checkedImage_commutator _ _ _ (module_le_Gv s) (Lv_le_Gv _ _)]
  rfl

/-- Restriction of the specified quotient map to the literal ambient commutator. -/
def checkedCommutatorMap : ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G) →* Gcheck (markedV s) :=
  (checkedQuotientMap (markedV s)).comp
    (inclusion ((residual_commutator_le_module s).trans (module_le_Gv s)))

theorem checkedCommutatorMap_injective : Function.Injective (checkedCommutatorMap s) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hl : inclusion ((residual_commutator_le_module s).trans (module_le_Gv s)) x ∈
      vLine (markedV s) := (QuotientGroup.eq_one_iff _).mp hx
  have hxline : (x : G) ∈ zpowers (markedV s) := by
    rw [← vLine_map_subtype]
    exact mem_map.mpr ⟨_, hl, rfl⟩
  exact Subtype.ext (disjoint_def.mp (line_disjoint_commutator s) hxline x.property)

theorem checkedCommutatorMap_range : (checkedCommutatorMap s).range = checkedVv s := by
  rw [checkedVv_eq_checked_commutator s]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact mem_map.mpr ⟨_, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

noncomputable def checkedCommutatorEquiv : ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G) ≃* checkedVv s :=
  (MonoidHom.ofInjective (checkedCommutatorMap_injective s)).trans
    (MulEquiv.subgroupCongr (checkedCommutatorMap_range s))

@[simp] theorem checkedCommutatorEquiv_apply (x : ↥(⁅V, Lv L (markedV s)⁆ : Subgroup G)) :
    (checkedCommutatorEquiv s x : Gcheck (markedV s)) = checkedCommutatorMap s x := rfl

/-- Every marked flag supplies the quotient and checked commutator identities
on its actual module, without any additional source conclusion as an input. -/
theorem FlagMarking.residual_and_checked {T : Sylow 2 G} {V₁ V₂ : Subgroup G}
    (f : FlagMarking T L V V₁ V₂) :
    Nat.card (Lv L (markedV f.module) ⧸ pCore 2 (Lv L (markedV f.module))) = 3 ∧
    Vv L (markedZ f.module) (markedV f.module) =
      zpowers (markedV f.module) ⊔ ⁅V, Lv L (markedV f.module)⁆ ∧
    Disjoint (zpowers (markedV f.module)) ⁅V, Lv L (markedV f.module)⁆ ∧
    checkedVv f.module = ⁅checkedV f.module, checkedLv f.module⁆ ∧
    (∃ c : G, MulAut.conj c (markedZ f.module) = markedA f.module) ∧
    markedA f.module ∈ V ⊓ centralizer (Lv L (markedV f.module) : Set G) :=
  ⟨f.residualQuotient_card, Vv_eq_line_sup_commutator f.module,
    line_disjoint_commutator f.module, checkedVv_eq_commutator f.module,
    markedA_conjugate_and_centralizes f.module⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.A5Module
