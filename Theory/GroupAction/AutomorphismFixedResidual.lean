module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PCoreRestriction

/-!
# Three-cores controlled by fixed perfect residuals

The perfect residual of an automorphism's fixed subgroup is invariant under
all commuting automorphisms. Suppose its inner image has trivial three-core,
and its centralizer inside the automorphism centralizer has order prime to
three. Every intermediate subgroup containing that inner image then has
trivial three-core: a normal three-subgroup intersects the inner image
trivially, so commutes with it and lies in the prime-to-three centralizer.

This separates the finite-group argument from the concrete involution
centralizer calculations used in Aschbacher--Smith 15.3.38, printed p.1137.
No local calculation for a particular group is asserted here.
-/

public section

open Subgroup Theory.GroupTheory
namespace MulAut
variable {Q : Type*} [Group Q]

/-- The perfect residual of the fixed subgroup, embedded in the original group. -/
@[expose] def fixedPerfectResidual (a : MulAut Q) : Subgroup Q :=
  (solvableResidual a.fixedSubgroup).map a.fixedSubgroup.subtype

/-- Inner automorphisms induced by the fixed perfect residual. -/
@[expose] def fixedPerfectResidualInner (a : MulAut Q) : Subgroup (MulAut Q) :=
  (fixedPerfectResidual a).map (MulAut.conj : Q →* MulAut Q)

/-- Two local calculations sufficient to kill the three-core of an automorphism
subgroup containing the fixed perfect residual and centralizing the automorphism. -/
@[expose] def FixedResidualThreeCoreData (a : MulAut Q) : Prop :=
  pCore 3 (fixedPerfectResidualInner a) = ⊥ ∧
    Nat.Coprime 3 (Nat.card
      (centralizer ({a} : Set (MulAut Q)) ⊓
        centralizer (fixedPerfectResidualInner a : Set (MulAut Q)) : Subgroup (MulAut Q)))

/-- Commuting automorphisms preserve the fixed perfect residual and its inner image. -/
theorem centralizer_le_normalizer_fixedPerfectResidualInner (a : MulAut Q) :
    centralizer ({a} : Set (MulAut Q)) ≤ normalizer (fixedPerfectResidualInner a : Set (MulAut Q)) := by
  have hinv (d : MulAut Q) (hd : d ∈ centralizer ({a} : Set (MulAut Q)))
      (x : Q) (hx : x ∈ fixedPerfectResidual a) : d x ∈ fixedPerfectResidual a := by
    have hc := mem_centralizer_singleton_iff.mp hd
    let f : a.fixedSubgroup →* a.fixedSubgroup :=
      (d.toMonoidHom.comp a.fixedSubgroup.subtype).codRestrict a.fixedSubgroup (by
        intro y
        rw [MulAut.mem_fixedSubgroup]
        change a (d y) = d y
        have he := DFunLike.congr_fun hc (y : Q)
        change d (a y) = a (d y) at he
        rw [(MulAut.mem_fixedSubgroup a y).mp y.property] at he
        exact he.symm)
    obtain ⟨y, hy, rfl⟩ := hx
    exact mem_map_of_mem a.fixedSubgroup.subtype
      (map_solvableResidual_le f (mem_map_of_mem f hy))
  have hconj (d : MulAut Q) (hd : d ∈ centralizer ({a} : Set (MulAut Q)))
      (x : MulAut Q) (hx : x ∈ fixedPerfectResidualInner a) : d * x * d⁻¹ ∈ fixedPerfectResidualInner a := by
    obtain ⟨y, hy, rfl⟩ := hx
    have he : d * MulAut.conj y * d⁻¹ = MulAut.conj (d y) := by
      ext z
      change d (y * d.symm z * y⁻¹) = d y * z * (d y)⁻¹
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [he]
    exact mem_map_of_mem _ (hinv d hd y hy)
  intro d hd
  rw [mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hconj d hd x hx
  · intro x hx
    refine ⟨d⁻¹ * x * d, ?_, ?_⟩
    · change d⁻¹ * x * d ∈ fixedPerfectResidualInner a
      simpa only [inv_inv] using hconj d⁻¹ ((centralizer _).inv_mem hd) x hx
    · change d * (d⁻¹ * x * d) * d⁻¹ = x
      group

private theorem threeCore_eq_bot_of_normal_subgroup [Finite Q]
    (H D C : Subgroup Q) (hHD : H ≤ D) (hDC : D ≤ C)
    (hN : D ≤ normalizer (H : Set Q)) (hH : pCore 3 H = ⊥)
    (hC : Nat.Coprime 3 (Nat.card (C ⊓ centralizer (H : Set Q) : Subgroup Q))) :
    pCore 3 D = ⊥ := by
  let L := H.subgroupOf D
  have hn : L.Normal := (normal_subgroupOf_iff_le_normalizer hHD).mpr hN
  let := hn
  have hL : pCore 3 L = ⊥ := by
    rw [← pCore_map_iso 3 (subgroupOfEquivOfLe hHD).symm, hH, Subgroup.map_bot]
  have hpull : (pCore 3 D).comap L.subtype ≤ pCore 3 L :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective L.subtype L.subtype_injective⟩
  rw [hL] at hpull
  have hdis : Disjoint L (pCore 3 D) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    exact congrArg Subtype.val (mem_bot.mp (hpull (show (⟨x, hx.1⟩ : L) ∈
      (pCore 3 D).comap L.subtype from hx.2)))
  have hcent : pCore 3 D ≤ centralizer (L : Set D) :=
    le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hdis))
  let P := D.pCoreIn 3
  have hPC : P ≤ C ⊓ centralizer (H : Set Q) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hDC x.property, ?_⟩
    intro y hy
    exact congrArg Subtype.val (hcent hx ⟨y, hHD hy⟩ hy)
  obtain ⟨n, hncard⟩ := (isPGroup_pCoreIn 3 D).exists_card_eq
  have hcop : Nat.Coprime (Nat.card P)
      (Nat.card (C ⊓ centralizer (H : Set Q) : Subgroup Q)) := by
    rw [show Nat.card P = 3 ^ n from hncard]
    exact hC.pow_left n
  have hP : P = ⊥ := le_bot_iff.mp
    ((le_inf le_rfl hPC).trans (disjoint_of_coprime_natCard hcop).eq_bot.le)
  exact ((pCore 3 D).map_eq_bot_iff_of_injective D.subtype_injective).mp hP

/-- A normal three-subgroup commutes with the fixed perfect residual, hence lies
in a centralizer of order prime to three and is trivial. -/
theorem threeCore_eq_bot_of_fixedResidualData [Finite Q] (a : MulAut Q)
    (ha : FixedResidualThreeCoreData a) (D : Subgroup (MulAut Q))
    (hD : D ≤ centralizer ({a} : Set (MulAut Q))) (hR : fixedPerfectResidualInner a ≤ D) :
    pCore 3 D = ⊥ :=
  threeCore_eq_bot_of_normal_subgroup _ _ _ hR hD
    (hD.trans (centralizer_le_normalizer_fixedPerfectResidualInner a)) ha.1 ha.2

end MulAut
