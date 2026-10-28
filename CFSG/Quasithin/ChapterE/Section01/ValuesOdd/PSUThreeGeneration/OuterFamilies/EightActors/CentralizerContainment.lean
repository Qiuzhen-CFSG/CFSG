module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FamilyTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.QuotientTransport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.ActorImage
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.PrimeReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.FiveModel
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.FiveGeneration.Calculation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating
/-!
# Centralizer containment for the outer eight-actor branch

The full centralizer of the Sylow-central involution in the original
eight-actor lies in the obstruction overgroup. At p = 3, solvability gives
containment. For p > 5, the actual radical quotient has simple PSL₂(p) socle;
its faithful socle action and trivial two-core supply the prime-field local
escape theorem, and generation lifts through the restricted original family.

At p = 5, a radical intersection of order at least four gives a direct E₂
member with the corrected local tau orbit. Otherwise the original actor has
image of order four, and the actual quotient identification with S₅ places
it outside A₅. The positioned E₁ generation theorem then supplies containment.
Every model, actor-position and local-generation premise is discharged in
`centralizer_le_of_eight_actor`. The subsequent contradiction completing the
outer eight-actor branch of E.1.14(7) belongs to the parent module.

Source: Aschbacher--Smith E.1.1--2, E.1.5, E.1.8, E.1.10 and E.1.14(7),
pp.209--214; A.3.21(a), p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- Generation by the image of a single original actor suffices. The actor is
proved to belong to the quotient image of the restricted original family. -/
theorem centralizer_le_of_quotient_actor_generation {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    (hAT : A ≤ (T : Subgroup G)) {z : G}
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hgen : let K := centralizerResidualOvergroup T z
      let q := QuotientGroup.mk' (solvableRadical K)
      eSubgroup 1 (((T : Subgroup G).subgroupOf K).map q)
          ((A.subgroupOf K).map q) ⊔
        ((T : Subgroup G).subgroupOf K).map q = ⊤) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let K := centralizerResidualOvergroup T z
  let q := QuotientGroup.mk' (solvableRadical K)
  let S := (T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  let Ω := Subgroup.map q '' ChiefOrbit.restrictedFamily K d.family
  have hΩ : IsElementaryFamily Ω :=
    (ChiefOrbit.restrictedFamily_elementary K d.elementary).map q (QuotientGroup.mk'_surjective _)
  have haΩ : (A.subgroupOf K).map q ∈ Ω := by
    refine ⟨A.subgroupOf K, ?_, rfl⟩
    change (A.subgroupOf K).map K.subtype ∈ d.family
    rwa [map_subgroupOf_eq_of_le (show A ≤ K from hAT.trans le_sup_right)]
  have haS : (A.subgroupOf K).map q ≤ (S : Subgroup _) := map_mono (comap_mono hAT)
  apply centralizer_le_of_residual_quotient_family_generation d hTz
  change eFamilySubgroup 1 (S : Subgroup _) Ω ⊔
    normalizer (weakClosure (S : Subgroup _) Ω : Set _) = ⊤
  apply top_unique
  rw [← hgen]
  have hEF : eSubgroup 1 (S : Subgroup _) ((A.subgroupOf K).map q) ≤
      eFamilySubgroup 1 (S : Subgroup _) Ω :=
    le_iSup_of_le (⟨_, haΩ, haS⟩ : {B : Subgroup (K ⧸ solvableRadical K) //
      B ∈ Ω ∧ B ≤ (S : Subgroup _)}) le_rfl
  exact sup_le (hEF.trans le_sup_left)
    ((sylow_le_weakClosure_normalizer S hΩ).trans le_sup_right)

/-- The p = 5 consumer for two independent inputs: the actual marked S₅
quotient and its positioned four-group E-generation. All cardinalities,
Sylow maps, E-member transport and solvable-kernel removal are discharged. -/
theorem centralizer_le_of_marked_symmetric_five_quotient {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4)
    (e : ((centralizerResidualOvergroup T z) ⧸
      solvableRadical (centralizerResidualOvergroup T z)) ≃* Equiv.Perm (Fin 5))
    (hpos : ¬ ((A.subgroupOf (centralizerResidualOvergroup T z)).map
      (QuotientGroup.mk' (solvableRadical (centralizerResidualOvergroup T z)))).map
        e.toMonoidHom ≤ alternatingGroup (Fin 5))
    (hfive : ∀ (S : Sylow 2 (Equiv.Perm (Fin 5))) (B : Subgroup (Equiv.Perm (Fin 5))),
      IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ (S : Subgroup _) →
      ¬ B ≤ alternatingGroup (Fin 5) →
      eSubgroup 1 (S : Subgroup _) B ⊔ (S : Subgroup _) = ⊤) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let K := centralizerResidualOvergroup T z
  let q := QuotientGroup.mk' (solvableRadical K)
  let a := (A.subgroupOf K).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  let := d.elementary.1 A hA
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf
    (hAT.trans le_sup_right)
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map q
  have ha : Nat.card a = 4 :=
    quotient_actor_card_four_of_small_radical_intersection hAT hcard hzA hz hTz hsmall
  have hc : Nat.card (a.map e.toMonoidHom) = 4 :=
    (Nat.card_congr (a.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans ha
  have haS : a ≤ (S : Subgroup _) := map_mono (comap_mono hAT)
  have hg := hfive (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (a.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hc (map_mono haS) hpos
  apply centralizer_le_of_quotient_actor_generation d hA hAT hTz
  change eSubgroup 1 (S : Subgroup _) a ⊔ (S : Subgroup _) = ⊤
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, map_eSubgroup_equiv, map_top_of_surjective _ e.surjective]
  exact hg

/-- For p > 5, the actual radical quotient's simple PSL₂(p) socle supplies
the prime-field escape theorem, with its faithfulness and two-core premises
discharged. This includes every normal PSU₃(p) extension supplemented by T. -/
theorem centralizer_le_of_prime_gt_five (L : Subgroup G) [L.Normal]
    {T : Sylow 2 G} (hLT : L ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlarge : 5 < p)
    (hmodel : ClassicalGroup.IsPSU L 3 p) (d : LargeFamilyObstruction T)
    {z : G} (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let K := centralizerResidualOvergroup T z
  let Q := K ⧸ solvableRadical K
  obtain ⟨_, hs, hm, _⟩ := centralizer_residual_quotient_structure L hLT hp ho
    (by omega) hmodel hzL hz hTz
  let : IsSimpleGroup (generalizedFitting Q) := hs
  have ha := PSLTwoGeneration.nonabelian_of_model (generalizedFitting Q) hlarge hm
  exact centralizer_le_of_prime_quotient_escape L hLT hp ho hlarge hmodel d hzL hz hTz
    (PSLTwoGeneration.PrimeGeometry.largeFamilyEscape_of_prime_socle hp ho hlarge hm
      (SimpleSocle.centralizer_eq_bot ha)
      (SimpleSocle.pCore_eq_bot solvableRadical_quotient_solvableRadical 2))

/-- The p = 5 containment uses the original actor in both radical-intersection
cases. In the small-intersection case the marked S₅ equivalence and the E₁
generation of its outer four-group are both constructed from the hypotheses. -/
theorem centralizer_le_of_prime_five
    [IsSimpleGroup (generalizedFitting G)] {T : Sylow 2 G}
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 5)
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ generalizedFitting G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let := d.elementary.1 A hA
  by_cases hfour : 4 ≤ Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z))
  · exact centralizer_le_of_radical_four (generalizedFitting G) hLT (by decide)
      (by decide) (by decide) hmodel d hA hAT hcard hinner hzA hzL hz hTz hfour
  · have hsmall := Nat.lt_of_not_ge hfour
    obtain ⟨e, _, hpos⟩ := centralizer_quotient_five_marked hLT hmodel hAT hcard
      hzA hzL hz hTz hsmall
    exact centralizer_le_of_marked_symmetric_five_quotient d hA hAT hcard hzA hz hTz
      hsmall e hpos FiveGeneration.positioned_four_generation

/-- The centralizer-containment endpoint for the outer eight-actor branch of
E.1.14(7). The caller supplies the involution from `exists_common_central_involution`.
No quotient model, position, escape or generation assumption remains. The full
source SQTK and outer-family context is retained, although this local deduction
only uses its specified obstruction, actor and simple PSU₃ socle. -/
theorem centralizer_le_of_eight_actor {κ : GroupClass} (_hG : IsSQTK κ G)
    [IsSimpleGroup (generalizedFitting G)] {T : Sylow 2 G}
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (d : LargeFamilyObstruction T)
    (_houter : ∀ B ∈ d.family, B ≤ (T : Subgroup G) → B ≠ ⊥ →
      ¬ B ≤ generalizedFitting G)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (_hne : A ≠ ⊥) (hcard : Nat.card A = 8)
    (hinner : Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G) (hzA : z ∈ A)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  by_cases hthree : p = 3
  · subst p
    exact centralizer_le_of_prime_three (generalizedFitting G) hLT hmodel d hzL hz hTz
  by_cases hfive : p = 5
  · subst p
    exact centralizer_le_of_prime_five hLT hmodel d hA hAT hcard hinner hzA hzL hz hTz
  have hlarge : 5 < p := by
    have := hp.two_le
    obtain ⟨k, hk⟩ := ho
    omega
  exact centralizer_le_of_prime_gt_five (generalizedFitting G) hLT hp ho hlarge
    hmodel d hzL hz hTz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
