module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.ChiefMarking
public import Theory.GroupTheory.PResidual.PCoreQuotient
public import Theory.GroupTheory.PResidual.OrderSix
public import Theory.GroupTheory.PResidual.NormalSup
public import Theory.GroupTheory.PResidual.NormalCubicLines

/-!
# Residuals of the marked chief-plane centralizers

The kernel of the original chief action is a two-group. Restricting it to
one marked factor gives an SL₂(2) quotient, whose two-residual has order
three. Transport through the two-group kernel preserves the intrinsic
residual/core quotient. The factors are normal in their paired base;
taking characteristic residuals preserves that relative normality, and
the residuals generate O² of every overgroup whose residual lies in the base.
MarkedExclusion applies these facts to the literal H, KS and outside actor.

Source: Aschbacher--Smith, Notation15.2.9 and15.2.21--22,
printed pp.1110,1114--1115; refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
namespace ChiefWreath
private instance : Fintype Actor := Fintype.ofEquiv ((C2 → SL2) × C2)
  (RegularWreathProduct.equivProd SL2 C2).symm

theorem factor_residual_core_card (i : C2) :
    Nat.card (pResidual 2 (factor i) ⧸ pCore 2 (pResidual 2 (factor i))) = 3 := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have hc : Nat.card (factor i) = 6 := by
    rw [Nat.card_congr ((factorEquiv i).trans e).toEquiv]
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hr := card_twoResidual_of_card_six hc
  have h3 : IsPGroup 3 (pResidual 2 (factor i)) := IsPGroup.of_card (n := 1) (by simpa using hr)
  have hb : pCore 2 (pResidual 2 (factor i)) = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide)
      (pCore 2 (pResidual 2 (factor i))) ⊤ pCore_isPGroup (h3.to_subgroup ⊤)
    simpa using hd.eq_bot
  rw [hb,Nat.card_congr QuotientGroup.quotientBot.toEquiv,hr]
end ChiefWreath

namespace ChiefWreathCoordinates
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} (c : ChiefWreathCoordinates ρ)

/-- The residual retains the original subgroup inclusion. -/
def residualFactor (i : ChiefWreath.C2) : Subgroup D :=
  (pResidual 2 (c.factor i)).map (c.factor i).subtype

omit [Finite D] in
theorem base_normalizes_factor (i : ChiefWreath.C2) :
    ChiefWreath.base.comap c.actor ≤ normalizer (c.factor i : Set D) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (c.factor i).map (MulAut.conj g).toMonoidHom = c.factor i
  rw [c.factor_conj]
  change (c.actor g).right = 1 at hg
  rw [hg,one_mul]

omit [Finite D] in
theorem factor_le_base (i : ChiefWreath.C2) :
    c.factor i ≤ ChiefWreath.base.comap c.actor := by
  intro g hg
  exact ((ChiefWreath.mem_factor (c.actor g) i).mp hg).1

theorem residualFactor_core_card (hk : IsPGroup 2 c.actor.ker) (i : ChiefWreath.C2) :
    Nat.card (c.residualFactor i ⧸ pCore 2 (c.residualFactor i)) = 3 := by
  let f := c.actor.subgroupMap (c.factor i)
  have hker : IsPGroup 2 f.ker := by
    change IsPGroup 2 (c.actor.subgroupMap (c.factor i)).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (f.pResidualCoreQuotientEquiv (c.actor.subgroupMap_surjective _) hker)
  let a := MulEquiv.subgroupCongr (c.factor_image i)
  let b := a.toMonoidHom.pResidualCoreQuotientEquiv (p := 2) a.surjective
    (by rw [(MonoidHom.ker_eq_bot_iff a.toMonoidHom).mpr a.injective]
        exact IsPGroup.of_card (n := 0) (by simp))
  let r' : pResidual 2 (c.factor i) ≃* c.residualFactor i :=
    (pResidual 2 (c.factor i)).equivMapOfInjective (c.factor i).subtype (c.factor i).subtype_injective
  have hrr : Nat.card (c.residualFactor i ⧸ pCore 2 (c.residualFactor i)) =
      Nat.card (pResidual 2 (c.factor i) ⧸ pCore 2 (pResidual 2 (c.factor i))) :=
    (Nat.card_congr (QuotientGroup.congr _ _ r' (pCore_map_iso 2 r')).toEquiv).symm
  rw [hrr,Nat.card_congr (e.trans b).toEquiv,ChiefWreath.factor_residual_core_card]

omit [Finite D] in
theorem residualFactor_le (i : ChiefWreath.C2) : c.residualFactor i ≤ pResidual 2 D :=
  map_pResidual_le 2 (c.factor i).subtype

omit [Finite D] in
theorem residualFactor_normalizes (i : ChiefWreath.C2) :
    ChiefWreath.base.comap c.actor ≤ normalizer (c.residualFactor i : Set D) :=
  (c.base_normalizes_factor i).trans
    (normalizer_le_normalizer_characteristic_image (c.factor i) (pResidual 2 (c.factor i)))

theorem residualFactor_mem (hk : IsPGroup 2 c.actor.ker)
    (hR : pResidual 2 D ≤ ChiefWreath.base.comap c.actor) (i : ChiefWreath.C2) :
    c.residualFactor i ∈ normalCubicResiduals (pResidual 2 D) := by
  refine ⟨c.residualFactor_le i,
    normal_subgroupOf_of_le_normalizer (hR.trans (c.residualFactor_normalizes i)),
    isPPerfect_embedded_pResidual 2 _,c.residualFactor_core_card hk i⟩

theorem residualFactors_span (hR : pResidual 2 D ≤ ChiefWreath.base.comap c.actor) :
    c.residualFactor 1 ⊔ c.residualFactor ChiefWreath.flip = pResidual 2 D := by
  let : ((c.factor 1).subgroupOf (c.factor 1 ⊔ c.factor ChiefWreath.flip)).Normal :=
    normal_subgroupOf_of_le_normalizer (by rw [c.factor_sup_eq_base]; exact c.base_normalizes_factor 1)
  let : ((c.factor ChiefWreath.flip).subgroupOf (c.factor 1 ⊔ c.factor ChiefWreath.flip)).Normal :=
    normal_subgroupOf_of_le_normalizer (by rw [c.factor_sup_eq_base]; exact c.base_normalizes_factor _)
  exact embedded_pResidual_sup_eq_of_contains_residual 2 _ _
    (by rw [c.factor_sup_eq_base]; exact hR)

end ChiefWreathCoordinates
end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
