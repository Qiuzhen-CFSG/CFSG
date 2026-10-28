module
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Bounds
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
/-!
# Descending the pair-fixer bounds through the actual central cover

Condition (E1) identifies Z(I) with O₂(I). Composing the actual quotient map
with a supplied model isomorphism therefore gives a perfect central cover
whose kernel is the entire center. Its automorphism descent is injective.
The cover's pointwise fixer has order dividing the quotient pointwise fixer,
and square identities descend back through the injective automorphism map.

Thus the intrinsic model tasks can calculate on the image of the actual
embedded L in their concrete quotient model. No lifting of all quotient
automorphisms or arbitrary conjugacy of embeddings is assumed.

Source: the covering cases of Aschbacher–Smith 16.1.7(3) and the calculation
in 16.3.5, printed pp.1172–1173 and 1178–1179 (1 March 2004 manuscript).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
open Subgroup Theory.GroupTheory PerfectCentralCovering
universe u v
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G} {S : Type v} [Group S]

/-- The specified model comparison composed with the actual two-core quotient. -/
def PairContext.coreCover (h : PairContext E L I t i) (hG : Hypothesis1611 𝒦 G)
    (e : (I ⧸ pCore 2 I) ≃* S) : Cover I S where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 I))
  isPerfect := h.component.quasisimple.toIsPerfect
  ker_le_center := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk',
      ← hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component]

/-- E1 supplies the exact kernel needed for faithful automorphism descent. -/
theorem PairContext.coreCover_kernel (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    (h.coreCover hG e).toMonoidHom.ker = center I := by
  exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 I))
    e.toMonoidHom e.injective).trans ((QuotientGroup.ker_mk' _).trans
      (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component).symm)

variable [Finite S]

omit [Finite G] in
/-- A strict quotient-fixer bound excludes a faithful order-four actor on the cover. -/
theorem pairFixer_card_lt_of_cover (f : Cover I S)
    (hk : f.toMonoidHom.ker = center I)
    (hb : Nat.card (fixingSubgroup (MulAut S)
      ((L.subgroupOf I).map f.toMonoidHom : Set S)) < 4) :
    Nat.card (pairFixer L I) < 4 :=
  (Nat.le_of_dvd Nat.card_pos (f.card_fixing_dvd hk (L.subgroupOf I))).trans_lt hb

omit [Finite G] in
/-- Transfer the upper bound and square identities from the actual projected subgroup. -/
theorem fourBound_of_cover (f : Cover I S)
    (hk : f.toMonoidHom.ker = center I)
    (hb : Nat.card (fixingSubgroup (MulAut S)
      ((L.subgroupOf I).map f.toMonoidHom : Set S)) ≤ 4)
    (hsq : ∀ a : fixingSubgroup (MulAut S)
      ((L.subgroupOf I).map f.toMonoidHom : Set S), a ^ 2 = 1) : FourBound L I := by
  constructor
  · exact (Nat.le_of_dvd Nat.card_pos (f.card_fixing_dvd hk (L.subgroupOf I))).trans hb
  · intro a
    apply Subtype.ext
    apply f.autMap_injective hk
    change f.autMap hk ((a : MulAut I) ^ 2) = f.autMap hk 1
    rw [map_pow, map_one]
    have ha : f.autMap hk (a : MulAut I) ∈ fixingSubgroup (MulAut S)
        ((L.subgroupOf I).map f.toMonoidHom : Set S) := by
      rw [mem_fixingSubgroup_iff]
      rintro _ ⟨x, hx, rfl⟩
      change f.autMap hk (a : MulAut I) (f.toMonoidHom x) = f.toMonoidHom x
      rw [f.autMap_apply hk]
      exact congrArg f.toMonoidHom (a.property ⟨x, hx⟩)
    exact congrArg Subtype.val (hsq ⟨_, ha⟩)
end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation
