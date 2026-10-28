module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The normal Fitting commutator in the star quotient

The subgroup [F(J(G_v)*), J(G_v)*] is normal in G_v*, and is solvable
because it lies in the nilpotent Fitting subgroup. Triviality of O₂(G_v*)
makes it odd, hence equal to its two-residual. It is nontrivial precisely
when the Fitting subgroup is not central.

These facts construct all the X-family clauses except generation by
J(T_v)*. That remaining FF-structure deduction is an explicit premise of
the final adapter, not an asserted source theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the first sentence after Lemma 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
variable {D : Type*} [Group D]

/-- The Fitting subgroup of N, embedded in its ambient group. -/
def fittingImage (N : Subgroup D) : Subgroup D :=
  (fittingSubgroup N).map N.subtype

/-- The normal commutator used for the solvable obstruction. -/
def fittingCommutator (N : Subgroup D) : Subgroup D := ⁅fittingImage N, N⁆

instance fittingImage_normal (N : Subgroup D) [N.Normal] : (fittingImage N).Normal :=
  ConjAct.normal_of_characteristic_of_normal

instance fittingCommutator_normal (N : Subgroup D) [N.Normal] :
    (fittingCommutator N).Normal := inferInstanceAs (⁅fittingImage N, N⁆.Normal)

theorem fittingCommutator_le (N : Subgroup D) [N.Normal] :
    fittingCommutator N ≤ fittingImage N := commutator_le_left _ _

/-- Centrality is tested in N itself, while the commutator is in D. -/
theorem fittingCommutator_eq_bot_iff (N : Subgroup D) :
    fittingCommutator N = ⊥ ↔ fittingSubgroup N ≤ center N := by
  rw [fittingCommutator, commutator_eq_bot_iff_le_centralizer]
  constructor
  · intro h x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_iff.mp (h (mem_map.mpr ⟨x, hx, rfl⟩)) y y.property
  · intro h x hx
    obtain ⟨x, hx, rfl⟩ := hx
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp (h hx) ⟨y, hy⟩)

variable [Finite D]

theorem fittingCommutator_solvable (N : Subgroup D) [N.Normal] :
    Group.IsSolvable (fittingCommutator N) := by
  let : Group.IsNilpotent (fittingImage N) := fittingSubgroupOf_isNilpotent N
  exact Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (fittingCommutator_le N))

/-- The embedded Fitting subgroup is an odd normal subgroup when O₂(D)=1. -/
theorem fittingImage_coprime_two (N : Subgroup D) [N.Normal]
    (hcore : pCore 2 D = ⊥) : Nat.Coprime 2 (Nat.card (fittingImage N)) := by
  have hF : fittingImage N ≤ fittingSubgroup D :=
    le_sSup ⟨inferInstance, fittingSubgroupOf_isNilpotent N⟩
  exact (pPrimeCore_coprime_card (p := 2) (G := D)).of_dvd_right
    (card_dvd_of_le (hF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)))

/-- The residual is the literal O² of the commutator subgroup. -/
theorem fittingCommutator_twoResidual (N : Subgroup D) [N.Normal]
    (hcore : pCore 2 D = ⊥) :
    (pResidual 2 (fittingCommutator N)).map (fittingCommutator N).subtype =
      fittingCommutator N := by
  have hc : Nat.Coprime 2 (Nat.card (fittingCommutator N)) :=
    (fittingImage_coprime_two N hcore).of_dvd_right
      (card_dvd_of_le (fittingCommutator_le N))
  have hr : pResidual 2 (fittingCommutator N) = ⊤ := by
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime (hc.of_dvd_right (_root_.orderOf_dvd_natCard x))
  rw [hr, ← MonoidHom.range_eq_map, range_subtype]

variable {G : Type*} [Group G] [Finite G]

/-- Every literal X-family clause follows once the FF commutator-generation
identity has been supplied. No normality or solvability witness is assumed. -/
theorem fittingCommutator_mem_XFamily (L T : Subgroup G) (z v : G)
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hgen : ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v))
    (hncentral : ¬ fittingSubgroup (JGstar z v) ≤ center (JGstar z v)) :
    fittingCommutator (JGstar z v) ∈ XFamily L T z v := by
  let : (JGstar z v).Normal := JGstar_normal z v
  refine ⟨⟨?_, fittingCommutator_twoResidual _ hcore,
    fun h => hncentral ((fittingCommutator_eq_bot_iff _).mp h), hgen⟩, inferInstance⟩
  rw [normalizer_eq_top]
  exact le_top

/-- The remaining FF-generation identity and the explicit 13.6.13 exclusion
imply the required equality. The identity still needs its source proof. -/
theorem fitting_eq_center_of_commutator_generation (L T : Subgroup G) (z v : G)
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (hgen : ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v))
    (hexclude : ∀ X ∈ XFamily L T z v, ¬ Group.IsSolvable X) :
    fittingSubgroup (JGstar z v) = center (JGstar z v) := by
  let : (JGstar z v).Normal := JGstar_normal z v
  apply le_antisymm
  · by_contra hn
    exact hexclude _ (fittingCommutator_mem_XFamily L T z v hcore hgen hn)
      (fittingCommutator_solvable _)
  · let : CommGroup (center (JGstar z v)) :=
      { (inferInstance : Group (center (JGstar z v))) with
        mul_comm := fun x y => Subtype.ext (mem_center_iff.mp x.property y).symm }
    exact le_sSup ⟨inferInstance, inferInstance⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter
