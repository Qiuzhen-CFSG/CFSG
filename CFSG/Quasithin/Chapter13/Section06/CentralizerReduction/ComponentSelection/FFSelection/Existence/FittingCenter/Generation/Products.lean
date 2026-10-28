module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.FittingCenter.Generation.PrimeOrder
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.QuotientSelection.ProductBranches.Factors

/-!
# Reducing the product FF branches to the double symmetric-three group

A normal solvable subgroup has trivial projection to any nonsolvable source
factor. Thus the odd Fitting subgroup embeds in the other coordinate. Unless
both factors are S₃, its order divides three and prime-order generation
applies. The remaining alternative supplies an actual group equivalence to
S₃×S₃, rather than a family tag or an assumed commutator identity.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3),(5), printed p.105; paragraph after 13.6.13, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.QuotientSelection.ProductBranches
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
variable {D E H : Type*} [Group D] [Group E] [Group H] [Finite D] [Finite E] [Finite H]

omit [Finite H] in
private theorem fitting_map_eq_bot (f : D →* H) (hf : Function.Surjective f)
    (hH : ∀ K : Subgroup H, K.Normal → Group.IsSolvable K → K = ⊥) :
    (fittingSubgroup D).map f = ⊥ := by
  let : ((fittingSubgroup D).map f).Normal := (inferInstance : (fittingSubgroup D).Normal).map f hf
  let : Group.IsSolvable ((fittingSubgroup D).map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective (fittingSubgroup D))
  exact hH _ inferInstance inferInstance

omit [Finite E] [Finite H] in
private theorem fitting_injective_fst (e : D ≃* E × H)
    (hH : ∀ K : Subgroup H, K.Normal → Group.IsSolvable K → K = ⊥) :
    Function.Injective (((MonoidHom.fst E H).comp e.toMonoidHom).comp
      (fittingSubgroup D).subtype) := by
  let f : D →* H := (MonoidHom.snd E H).comp e.toMonoidHom
  have hb := fitting_map_eq_bot f (Prod.snd_surjective.comp e.surjective) hH
  have hz (x : fittingSubgroup D) : (e x).2 = 1 := by
    have hh := mem_map_of_mem f x.property
    rwa [hb, mem_bot] at hh
  intro x y hxy
  apply Subtype.ext
  apply e.injective
  exact Prod.ext hxy ((hz x).trans (hz y).symm)

omit [Finite H] in
private theorem product_fitting_small (e : D ≃* E × H) (hE : FactorModel E)
    (hH : ∀ K : Subgroup H, K.Normal → Group.IsSolvable K → K = ⊥)
    (hcore : pCore 2 D = ⊥) : Nat.card (fittingSubgroup D) ∣ 3 := by
  let f : D →* E := (MonoidHom.fst E H).comp e.toMonoidHom
  have hf := fitting_injective_fst e hH
  rcases factor_structure hE with hs | ⟨_, _, he⟩
  · obtain ⟨eE⟩ := hs
    have hc : Nat.card E = 2 * 3 := by
      rw [Nat.card_congr eE.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hodd : Nat.Coprime 2 (Nat.card (fittingSubgroup D)) :=
      (pPrimeCore_coprime_card (p := 2) (G := D)).of_dvd_right
        (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))
    apply hodd.symm.dvd_of_dvd_mul_left
    exact hc ▸ card_dvd_of_injective (f.comp (fittingSubgroup D).subtype) hf
  · have hb := fitting_map_eq_bot f (Prod.fst_surjective.comp e.surjective) he
    have hF : fittingSubgroup D = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hh := mem_map_of_mem f hx
      rw [hb, mem_bot] at hh
      have heq : (⟨x, hx⟩ : fittingSubgroup D) = 1 := hf (hh.trans (map_one _).symm)
      exact congrArg Subtype.val heq
    rw [hF, card_bot]
    exact one_dvd _

theorem product_fitting_small_or_doubleThree (e : D ≃* E × H)
    (hE : FactorModel E) (hH : FactorModel H) (hcore : pCore 2 D = ⊥) :
    Nat.card (fittingSubgroup D) ∣ 3 ∨ Nonempty (D ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  rcases factor_structure hH with ht | ⟨_, _, hh⟩
  · obtain ⟨eH⟩ := ht
    rcases factor_structure hE with hs | ⟨_, _, he⟩
    · obtain ⟨eE⟩ := hs
      exact Or.inr ⟨e.trans (eE.prodCongr eH)⟩
    · exact Or.inl (product_fitting_small (e.trans MulEquiv.prodComm) hH he hcore)
  · exact Or.inl (product_fitting_small e hE hh hcore)

variable {G : Type*} [Group G] [Finite G]

/-- Both product source alternatives on the actual Thompson image reduce
to the one remaining double-S₃ group, retaining the concrete equivalence. -/
theorem thompson_generation_or_doubleThree_of_product
    (T : Subgroup G) (z v : G)
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    {E H : Type*} [Group E] [Group H] [Finite E] [Finite H]
    (e : JGstar z v ≃* E × H) (hE : FactorModel E) (hH : FactorModel H) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) ∨
      Nonempty (JGstar z v ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  rcases product_fitting_small_or_doubleThree e hE hH (JGstar_twoCore z v hcore) with hc | he
  · exact Or.inl (thompson_generation_of_fitting_card_dvd_prime T z v hSyl
      (by decide : Nat.Prime 3) hc)
  · exact Or.inr he


open scoped IsMulCommutative
/-- The hyperplane branch cannot give the double-S₃ exception: its literal
SL₃(2) factor has order 168, which does not divide 36. -/
theorem thompson_generation_of_hyperplane
    (T : Subgroup G) (z v : G) (hz : z ∈ Gv v)
    [IsElementaryAbelian 2 (Uv z v)]
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hcore : pCore 2 (Gstar z v) = ⊥)
    (c : HyperplaneCase (thompsonRepresentation z v hz)) :
    ⁅fittingCommutator (JGstar z v),
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ =
        fittingCommutator (JGstar z v) := by
  have hc := thompson_generation_or_doubleThree_of_product T z v hSyl hcore
    c.product.equiv.symm (.linearThree BinaryField.two (by decide) c.firstEquiv)
    (c.secondCase.factorModel _)
  rcases hc with hc | he
  · exact hc
  · obtain ⟨e⟩ := he
    have hfirst : Nat.card c.first = 168 :=
      (Nat.card_congr c.firstEquiv.toEquiv).trans Matrix.PSL3Two.card_SL
    have hwhole : Nat.card (JGstar z v) = 36 := by
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hd := c.first.card_subgroup_dvd_card
    rw [hfirst, hwhole] at hd
    norm_num at hd

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FittingCenter.Generation
