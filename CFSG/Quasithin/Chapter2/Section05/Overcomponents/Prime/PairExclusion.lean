module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.FixedRanks
public import Theory.GroupTheory.CommutingCenterlessPairQuotient
public import GorensteinWalter.PSL2Center
/-!
# Excluding two commuting original prime components in a retained overcomponent

The two commuting centerless copies inject together into the literal containing central quotient. The retained quotient orders have no square of their defining prime. This is the case-I second-pumpup exclusion.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows

/-- Two commuting embedded prime-field components cannot lie in either retained
quasisimple overcomponent. The homomorphisms retain their actual embeddings. -/
theorem prime_fixed_quotient_no_commuting_prime_pair
    {E : Type*} [Group E] [Finite E] (a : MulAut (E ⧸ center E))
    (hm : PrimeFixedQuotientModels (E ⧸ center E) a)
    {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (f g : PSL(2,ZMod p) →* E) (hf : Function.Injective f) (hg : Function.Injective g)
    (hc : ∀ x y, Commute (f x) (g y)) : False := by
  let : Fact p.Prime := ⟨hp⟩
  let q := QuotientGroup.mk' (center E)
  exact prime_fixed_quotient_no_prime_pair_embedding a hm hp hp7
    ((q.comp f).noncommCoprod (q.comp g) (fun x y => (hc x y).map q))
    (MonoidHom.central_quotient_noncommCoprod_injective f g hf hg
      (GorensteinWalter.psl2_center_eq_bot (ZMod p))
      (GorensteinWalter.psl2_center_eq_bot (ZMod p)) hc)
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.PrimeRows
