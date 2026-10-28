module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.NaturalAction
public import CFSG.Quasithin.ChapterA.Section01.PStructure
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Inputs and the two complete alternatives of 15.3.7

All star images below are images in `M/O₂(M)`. The action image is formed
separately using the compatible natural orthogonal action. `SourceInputs`
lists the earlier mathematical inputs allowed for this conditional proof:
the R₂ consequences, the residual image and its E₉ identification, an
intersection-core inverter, 14.1.17(3),(4), the quasithin rank bound and
characteristic two, and the already calculated local conclusions.

None of the two alternatives is an input. In particular the kernel of the
action on `Y` is not assumed to be a two-group. `oddCenterIn` expresses the
literal odd core of the center, and the conditional cyclicity input tests
faithfulness of the actual cyclic conjugation action on `O₃(M*)`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.1.17
and 15.3.7, printed pp.980 and 1122 (PDF pp.997 and 1139).
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
variable {G : Type*} [Group G]

abbrev ElementaryNine := Multiplicative (ZMod 3) × Multiplicative (ZMod 3)

/-- The quotient used by the source's star notation. -/
abbrev StarGroup (M : Subgroup G) := M ⧸ pCore 2 M

/-- The actual star image, even when `X` is originally given in `G`. -/
def star (M X : Subgroup G) : Subgroup (StarGroup M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))

/-- The source's intersection two-core, in the ambient group. -/
abbrev Rc (M Mc : Subgroup G) : Subgroup G := (M ⊓ Mc).pCoreIn 2

/-- The odd core of the center, embedded into the ambient group. -/
def oddCenterIn {H : Type*} [Group H] (K : Subgroup H) : Subgroup H :=
  (pPrimeCore 2 (center K)).map (K.subtype.comp (center K).subtype)

/-- The genuine preceding inputs used in the two three-group branches. -/
structure SourceInputs [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) : Prop where
  sylow_le : (T : Subgroup G) ≤ M
  sylow_le_partner : (T : Subgroup G) ≤ Mc
  module_le : V ≤ M
  /-- R₂(M): the two-core centralizes V. -/
  core_le_kernel : pCore 2 M ≤ d.actor.ker
  /-- The precise R₂(M) consequence C_Rc(V)=O₂(M). -/
  core_inter_kernel : (Rc M Mc).subgroupOf M ⊓ d.actor.ker = pCore 2 M
  /-- The residual-image calculation from the orthogonal-image owner. -/
  residual_image : ((residualY M Mc).subgroupOf M).map d.actor =
    twoResidualAmbient (⊤ : Subgroup OrthogonalActor)
  /-- Actual identification of the action image, not a family tag. -/
  image_model : Nonempty
    ((((residualY M Mc).subgroupOf M).map d.actor) ≃* ElementaryNine)
  /-- The central involution of the Sylow action image has a lift in Rc. -/
  inverter : ∃ r : M, r ∈ (Rc M Mc).subgroupOf M ∧ d.actor r ≠ 1 ∧
    (d.actor r) ^ 2 = 1 ∧ ∀ y ∈ (residualY M Mc).subgroupOf M,
      d.actor (r * y * r⁻¹) = (d.actor y)⁻¹
  /-- 14.1.17(3), first clause, in M/O₂(M). -/
  star_centralizes : star M (M ⊓ centralizer (V : Set G)) ≤
    centralizer ((star M (residualY M Mc) ⊔ star M (Rc M Mc) :
      Subgroup (StarGroup M)) : Set (StarGroup M))
  /-- 14.1.17(3), second clause, retaining the odd-central bound. -/
  star_odd_center : star M (residualY M Mc ⊓ centralizer (V : Set G)) ≤
    oddCenterIn (star M (M ⊓ centralizer (V : Set G)) ⊔ star M (Rc M Mc))
  /-- Exactly the p=3 specialization of 14.1.17(4) used here. -/
  faithful_cyclic : ∀ r : StarGroup M, r ∈ star M (Rc M Mc) → r ≠ 1 →
    Function.Injective
      ((MulAut.conjNormal : StarGroup M →* MulAut (pCore 3 (StarGroup M))).domRestrict
        (zpowers r)) →
    ∀ P : Sylow 3 (centralizer (zpowers r : Set (StarGroup M))), IsCyclic P
  /-- The standing quasithin rank bound. -/
  rank_bound : primeRank 3 M ≤ 2
  /-- The standing local characteristic-two condition. -/
  characteristic_two : centralizer (pCore 2 M : Set M) ≤ pCore 2 M
  /-- The previously calculated intersection factorization. -/
  intersection : M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G)
  /-- The previously calculated two-core of YT. -/
  join_core : (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
    (T : Subgroup G) ⊓ centralizer (V : Set G)
  /-- The module inclusion already obtained from [V,Y]=V. -/
  module_le_core : V ≤ (residualY M Mc).pCoreIn 2

/-- The entire E₉ alternative, with its prime-to-three residual convention. -/
def ElementaryAlternative (M Mc V : Subgroup G) : Prop :=
  (residualY M Mc).pCoreIn 2 = residualY M Mc ⊓ centralizer (V : Set G) ∧
  Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* ElementaryNine) ∧
  residualY M Mc = (primeToResidual 3 M).map M.subtype

/-- The entire extraspecial alternative, with the literal central preimage. -/
def ExtraspecialAlternative (M Mc V : Subgroup G)
    (d : NaturalOrthogonalAction M V) : Prop :=
  Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* HeisenbergPrime 3) ∧
  (centralPreimage (pCore 2 (residualY M Mc))).map (residualY M Mc).subtype =
    residualY M Mc ⊓ centralizer (V : Set G) ∧
  IsCyclic (((Rc M Mc).subgroupOf M).map d.actor) ∧
  residualY M Mc = theta M ∧
  ∀ P : Sylow 3 (M ⊓ Mc : Subgroup G), IsCyclic P

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
end
