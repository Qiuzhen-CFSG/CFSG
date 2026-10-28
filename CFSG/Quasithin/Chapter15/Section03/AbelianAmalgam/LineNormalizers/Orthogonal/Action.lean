module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Basic
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction

/-!
# The faithful quotient of a full action on a singular four-group

Conjugation on the actual subgroup `E` has kernel its relative centralizer.
Its automorphism group is identified with S₃ through the permutation action
on its three nonidentity elements. Thus a full action kills the two-core;
when the kernel is a two-group, it is exactly the two-core, and the first
isomorphism theorem gives the required quotient equivalence.

These are action-to-quotient implications for 15.3.66(5), not assumptions
that the geometric action is full. The source assembly must still construct
the full action and prove its kernel is a two-group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66(5)–(6), printed p.1152, PDF p.1169.
-/

@[expose] public section

open Subgroup
open scoped Pointwise IsKleinFour
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal

variable {G : Type*} [Group G]

/-- The conjugation action on `E`, restricted to a specified subgroup of its normalizer. -/
def lineAction (E A : Subgroup G) (hA : A ≤ lineNormalizer E) : A →* MulAut E :=
  E.normalizerMonoidHom.comp (inclusion hA)

/-- The kernel is the centralizer inside the acting group, without ambient normality. -/
theorem lineAction_ker (E A : Subgroup G) (hA : A ≤ lineNormalizer E) :
    (lineAction E A hA).ker = (centralizer (E : Set G)).subgroupOf A := by
  ext a
  change inclusion hA a ∈ E.normalizerMonoidHom.ker ↔ _
  rw [E.normalizerMonoidHom_ker]
  rfl

/-- The two source factors both normalize the line. -/
theorem lineProduct_le_normalizer (Y T E : Subgroup G) :
    lineY Y E ⊔ lineT T E ≤ lineNormalizer E :=
  sup_le ((lineY_le Y E).trans inf_le_right) inf_le_right

/-- A full four-group action makes the ambient normalizer's two-core centralize the line. -/
theorem lineQ_le_centralizer_of_full_action [Finite G]
    (E : Subgroup G) [IsKleinFour E]
    (hfull : Function.Surjective E.normalizerMonoidHom) :
    lineQ E ≤ centralizer (E : Set G) := by
  have h := IsKleinFour.twoCore_le_ker_of_surjective E E.normalizerMonoidHom hfull
  rw [E.normalizerMonoidHom_ker] at h
  rintro x ⟨q, hq, rfl⟩
  exact h hq

/-- Full action and a two-group kernel identify the intrinsic two-core. -/
theorem lineProduct_twoCore_of_full_action [Finite G]
    (E A : Subgroup G) [IsKleinFour E] (hA : A ≤ lineNormalizer E)
    (hfull : Function.Surjective (lineAction E A hA))
    (hkernel : IsPGroup 2 ((centralizer (E : Set G)).subgroupOf A)) :
    Stellmacher.twoCoreAmbient A = A ⊓ centralizer (E : Set G) := by
  let e := IsKleinFour.autEquivPermThree E
  let f := e.toMonoidHom.comp (lineAction E A hA)
  have hk : f.ker = (centralizer (E : Set G)).subgroupOf A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, lineAction_ker]
  have he := ker_eq_twoCore_of_surjective_perm_three f (e.surjective.comp hfull) (hk ▸ hkernel)
  change (pCore 2 A).map A.subtype = _
  rw [← he, hk, ← comap_subtype, map_comap_eq, range_subtype, inf_comm]

/-- The quotient in 15.3.66(5) is an actual multiplicative equivalence with S₃. -/
noncomputable def lineProductQuotientEquiv [Finite G]
    (E A : Subgroup G) [IsKleinFour E] (hA : A ≤ lineNormalizer E)
    (hfull : Function.Surjective (lineAction E A hA))
    (hkernel : IsPGroup 2 ((centralizer (E : Set G)).subgroupOf A)) :
    (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3) := by
  let e := IsKleinFour.autEquivPermThree E
  let f := e.toMonoidHom.comp (lineAction E A hA)
  have hk : f.ker = (centralizer (E : Set G)).subgroupOf A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, lineAction_ker]
  have he := ker_eq_twoCore_of_surjective_perm_three f (e.surjective.comp hfull) (hk ▸ hkernel)
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (e.surjective.comp hfull))

/-- Full action of the two source factors gives the literal three-factor product. -/
theorem lineNormalizer_three_factor_product [Finite G] (Y T E : Subgroup G)
    (hTY : T ≤ normalizer (Y : Set G))
    (hfull : Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E))) :
    (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineT T E : Set G) * (centralizer (E : Set G) : Set G) := by
  rw [lineNormalizer_product_of_full_action E _ (lineProduct_le_normalizer Y T E) hfull,
    lineY_sup_lineT_product Y T E hTY]

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
