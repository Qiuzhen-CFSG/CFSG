module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.ActorImage
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.PrimeReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.FiveModel.Radical
public import Theory.SpecificGroups.SL2.PrimeMarkedFive
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
/-!
# The marked S₅ quotient for the PSU₃(5) centralizer

The actual centralizer supplement has SL₂(5) solvable residual. Its abelian
radical forces the original eight-actor's image of order four to lie outside the
simple socle: the commuting lift obstruction would make its image cyclic.
The genuine PSL₂(5)-to-A₅ comparison and Aut(A₅) = S₅ then construct an actual
quotient equivalence preserving the socle and placing the actor outside A₅.
Symmetric-five generation transports back through this equivalence.

The final two theorems discharge radical abelianness using `FiveModel.Radical`,
for every permitted ambient two-extension and arbitrary Hermitian form. The
SQTK hypothesis and the inner-intersection cardinality are unnecessary for
this quotient identification. The independent symmetric-five generation premise
is retained for its existing owner, `qt-e01-symmetric-five-outer-four-generation`;
the parent centralizer-containment task retains its final discharge.
Scratch/FiveCentralizerMarking/Probe.lean checks the application to
centralizer_le_of_marked_symmetric_five_quotient with the actual equivalence
and actor position discharged.

Source: Aschbacher--Smith A.3.21(a), p.55; E.1.2 and E.1.14(7), pp.210,214;
Aschbacher (1982), Lemma 4.11.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- The original eight-actor marks an actual S₅ quotient once the literal
centralizer radical is proved abelian. No quotient model or actor position
is an input. -/
theorem centralizer_quotient_five_marked_of_abelian_radical
    (L : Subgroup G) [L.Normal] {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (hmodel : ClassicalGroup.IsPSU L 3 5)
    {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4)
    (habelian : IsMulCommutative (solvableRadical (centralizerResidualOvergroup T z))) :
    let K := centralizerResidualOvergroup T z
    let Q := K ⧸ solvableRadical K
    let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
    ∃ e : Q ≃* Equiv.Perm (Fin 5),
      (generalizedFitting Q).map e.toMonoidHom = alternatingGroup (Fin 5) ∧
      ¬ a.map e.toMonoidHom ≤ alternatingGroup (Fin 5) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let K := centralizerResidualOvergroup T z
  let Q := K ⧸ solvableRadical K
  let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
  let : IsMulCommutative (solvableRadical K) := habelian
  let : IsElementaryAbelian 2 (A.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hAT.trans le_sup_right)
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv (p := 5) L T hLT (by decide)
    (by decide) (by decide) hmodel z hzL hz
  let er : solvableResidual K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    (centralizerResidualOvergroup_residualEquiv hTz).trans ec
  obtain ⟨ef⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  have ha : Nat.card a = 4 :=
    quotient_actor_card_four_of_small_radical_intersection hAT hcard hzA hz hTz hsmall
  exact Theory.SpecificGroups.SL2.PrimeMarkedFive.exists_marked_equiv (p := 5)
    (by decide) (by decide) er (centralizerResidualOvergroup_pResidual_eq hTz)
    ef (A.subgroupOf K) ha

/-- Symmetric-five generation transports to the literal centralizer quotient.
The model-specific abelian-radical premise remains explicit. -/
theorem centralizer_quotient_five_generation_of_abelian_radical
    (L : Subgroup G) [L.Normal] {T : Sylow 2 G}
    (hLT : L ⊔ (T : Subgroup G) = ⊤) (hmodel : ClassicalGroup.IsPSU L 3 5)
    {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ L) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4)
    (habelian : IsMulCommutative (solvableRadical (centralizerResidualOvergroup T z)))
    (hfive : ∀ (S : Sylow 2 (Equiv.Perm (Fin 5))) (B : Subgroup (Equiv.Perm (Fin 5))),
      IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ (S : Subgroup _) →
      ¬ B ≤ alternatingGroup (Fin 5) →
      eSubgroup 1 (S : Subgroup _) B ⊔ (S : Subgroup _) = ⊤) :
    let K := centralizerResidualOvergroup T z
    let q := QuotientGroup.mk' (solvableRadical K)
    eSubgroup 1 (((T : Subgroup G).subgroupOf K).map q)
        ((A.subgroupOf K).map q) ⊔
      ((T : Subgroup G).subgroupOf K).map q = ⊤ := by
  obtain ⟨e, _, hpos⟩ := centralizer_quotient_five_marked_of_abelian_radical
    L hLT hmodel hAT hcard hzA hzL hz hTz hsmall habelian
  let K := centralizerResidualOvergroup T z
  let q := QuotientGroup.mk' (solvableRadical K)
  let a := (A.subgroupOf K).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  let : IsElementaryAbelian 2 (A.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hAT.trans le_sup_right)
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map q
  have ha : Nat.card a = 4 :=
    quotient_actor_card_four_of_small_radical_intersection hAT hcard hzA hz hTz hsmall
  have hc : Nat.card (a.map e.toMonoidHom) = 4 :=
    (Nat.card_congr (a.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans ha
  have haS : a ≤ (S : Subgroup _) := map_mono (comap_mono hAT)
  have hg := hfive (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (a.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hc (map_mono haS) hpos
  change eSubgroup 1 (S : Subgroup _) a ⊔ (S : Subgroup _) = ⊤
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_sup, map_eSubgroup_equiv, map_top_of_surjective _ e.surjective]
  exact hg

/-- The actual radical quotient is S₅, with its simple socle identified with
A₅ and the original eight-actor mapping outside A₅. All model premises are
discharged for the simple generalized-Fitting PSU₃(5) socle. -/
theorem centralizer_quotient_five_marked
    [IsSimpleGroup (generalizedFitting G)] {T : Sylow 2 G}
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 5)
    {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ generalizedFitting G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4) :
    let K := centralizerResidualOvergroup T z
    let Q := K ⧸ solvableRadical K
    let a := (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))
    ∃ e : Q ≃* Equiv.Perm (Fin 5),
      (generalizedFitting Q).map e.toMonoidHom = alternatingGroup (Fin 5) ∧
      ¬ a.map e.toMonoidHom ≤ alternatingGroup (Fin 5) := by
  exact centralizer_quotient_five_marked_of_abelian_radical
    (generalizedFitting G) hLT hmodel hAT hcard hzA hzL hz hTz hsmall
    (centralizer_radical_isMulCommutative hLT hmodel hzL (hAT hzA) hz hTz)

/-- Generation in the positioned S₅ model gives generation in the literal
centralizer quotient. The only remaining premise is the independent symmetric-five
generation theorem; the quotient model and actor position are both proved. -/
theorem centralizer_quotient_five_generation
    [IsSimpleGroup (generalizedFitting G)] {T : Sylow 2 G}
    (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 5)
    {A : Subgroup G} [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hzA : z ∈ A) (hzL : z ∈ generalizedFitting G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4)
    (hfive : ∀ (S : Sylow 2 (Equiv.Perm (Fin 5))) (B : Subgroup (Equiv.Perm (Fin 5))),
      IsElementaryAbelian 2 B → Nat.card B = 4 → B ≤ (S : Subgroup _) →
      ¬ B ≤ alternatingGroup (Fin 5) →
      eSubgroup 1 (S : Subgroup _) B ⊔ (S : Subgroup _) = ⊤) :
    let K := centralizerResidualOvergroup T z
    let q := QuotientGroup.mk' (solvableRadical K)
    eSubgroup 1 (((T : Subgroup G).subgroupOf K).map q)
        ((A.subgroupOf K).map q) ⊔
      ((T : Subgroup G).subgroupOf K).map q = ⊤ := by
  exact centralizer_quotient_five_generation_of_abelian_radical
    (generalizedFitting G) hLT hmodel hAT hcard hzA hzL hz hTz hsmall
    (centralizer_radical_isMulCommutative hLT hmodel hzL (hAT hzA) hz hTz) hfive

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
