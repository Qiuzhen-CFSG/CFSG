module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.EarlierSources
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Product
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.PrimeRankElementary
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Restricting an SQTK cover to S₃ times a three-subgroup

Pull the genuine SQTK cover back to the image of the injective product map.
Its literal normal quotient is identified with S₃ × E by the first
isomorphism theorem. The three-core of this product is self-centralizing,
so its generalized Fitting subgroup is its three-core. A transposition
supplies a nontrivial two-subgroup, and the second factor lies in its
relative centralizer inside that core. A.1.31(1) makes the second factor
cyclic; elementary abelian second factors therefore have order at most
three. This bounds the complementary three-rank without asserting rank
monotonicity for arbitrary quotients.

`EarlierA131One` remains exactly the universal earlier-source implication,
with the rank hypothesis on the covering group and the normal quotient.
Its source producer is `qt-a-01-section-rank`; final classification assembly
must discharge that parameter. The generic result serves both B.5.8 and
the literal centralizer complement in B.5.11.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.1.31(1),
printed pp.27–28, and B.5.8/B.5.11, printed pp.106 and 109.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
universe u
variable {K : GroupClass.{u}} {D : Type u} [Group D] [Finite D]

private noncomputable def coverOfInjective (h : SQTKQuotient K D)
    {X : Type u} [Group X] (f : X →* D) (hf : Function.Injective f) :
    SQTKQuotient K X :=
  { h.subgroup f.range with
    equiv := (h.subgroup f.range).equiv.trans (MonoidHom.ofInjective hf).symm }

omit [Finite D] in
private theorem cyclic_of_cover (h131 : EarlierA131One.{u}) (h : SQTKQuotient K D)
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hfit : generalizedFitting D = pCore p D)
    (T R : Subgroup D) (hT : IsPGroup 2 T) (hTne : T ≠ ⊥)
    (hR : R ≤ pCore p D) (hRT : R ≤ centralizer (T : Set D)) : IsCyclic R := by
  let e := h.equiv
  let T' := T.map e.symm.toMonoidHom
  have hfit' : generalizedFitting (h.Cover ⧸ h.kernel) =
      pCore p (h.Cover ⧸ h.kernel) := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_generalizedFitting_equiv, pCore_map_iso, hfit]
  have hTne' : T' ≠ ⊥ := by
    intro hz
    apply hTne
    apply Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective
    simpa only [Subgroup.map_bot] using hz
  let := h131 h.Cover p hp ho (h.sqtk.stronglyQuasithin p hp ho) h.kernel hfit'
    T' (hT.map e.symm.toMonoidHom) hTne'
  let f : R →* ↥(pCore p (h.Cover ⧸ h.kernel) ⊓
      centralizer (T' : Set (h.Cover ⧸ h.kernel))) :=
    (e.symm.toMonoidHom.comp R.subtype).codRestrict _ (by
      intro r
      constructor
      · have hh := mem_map_of_mem e.symm.toMonoidHom (hR r.property)
        rwa [pCore_map_iso] at hh
      · rintro _ ⟨t, ht, rfl⟩
        change e.symm t * e.symm r = e.symm r * e.symm t
        simpa only [← map_mul] using congrArg e.symm (hRT r.property t ht))
  exact isCyclic_of_injective f (fun x y hxy =>
    Subtype.ext (e.symm.injective (congrArg Subtype.val hxy)))

private abbrev S := Equiv.Perm (Fin 3)

private theorem threeCore_selfCentralizing :
    centralizer (pCore 3 S : Set S) ≤ pCore 3 S := by
  have ha : alternatingGroup (Fin 3) ≤ pCore 3 S :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 1) (by
      rw [nat_card_alternatingGroup, Nat.card_fin]; decide)⟩
  have hc : centralizer (alternatingGroup (Fin 3) : Set S) ≤ alternatingGroup (Fin 3) := by
    have hh : ∀ g : S,
        (∀ a : S, a ∈ alternatingGroup (Fin 3) → a * g = g * a) →
          g ∈ alternatingGroup (Fin 3) := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    exact hh
  exact (centralizer_le ha).trans (hc.trans ha)

private theorem pCore_eq_top_of_pGroup {E : Type u} [Group E] (hE : IsPGroup 3 E) :
    pCore 3 E = ⊤ := by
  apply top_unique
  exact le_sSup ⟨inferInstance, hE.to_subgroup ⊤⟩

private theorem product_fitting {E : Type u} [Group E] [Finite E] (hE : IsPGroup 3 E) :
    generalizedFitting (S × E) = pCore 3 (S × E) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 3
  intro x hx
  rw [pCore_prod, pCore_eq_top_of_pGroup hE]
  refine ⟨threeCore_selfCentralizing ?_, mem_top _⟩
  intro s hs
  have hh := hx (s, 1) (by
    rw [pCore_prod]
    exact ⟨hs, one_mem _⟩)
  exact congrArg Prod.fst hh

private theorem cyclic_of_product_cover {E : Type u} [Group E] [Finite E]
    (h131 : EarlierA131One.{u}) (h : SQTKQuotient K (S × E)) (hE : IsPGroup 3 E) :
    IsCyclic E := by
  let t : S := Equiv.swap 0 1
  let T : Subgroup (S × E) := (zpowers t).map (MonoidHom.inl S E)
  let R : Subgroup (S × E) := (⊥ : Subgroup S).prod ⊤
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime <;> decide +kernel
  have hT : IsPGroup 2 T :=
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; decide)).map (MonoidHom.inl S E)
  have hTne : T ≠ ⊥ := by
    intro hz
    have hh : (t, (1 : E)) ∈ T := mem_map_of_mem (MonoidHom.inl S E) (mem_zpowers t)
    rw [hz] at hh
    have he : t = 1 := congrArg Prod.fst (show (t, (1 : E)) = 1 from hh)
    have := congrArg orderOf he
    rw [ht, orderOf_one] at this
    contradiction
  have hR : R ≤ pCore 3 (S × E) := by
    rw [pCore_prod, pCore_eq_top_of_pGroup hE]
    exact Subgroup.prod_mono bot_le le_rfl
  have hRT : R ≤ centralizer (T : Set (S × E)) := by
    intro r hr
    rintro _ ⟨s, hs, rfl⟩
    have hr1 : r.1 = 1 := hr.1
    apply Prod.ext
    · change s * r.1 = r.1 * s
      simp only [hr1, mul_one, one_mul]
    · change 1 * r.2 = r.2 * 1
      simp
  let := cyclic_of_cover h131 h 3 (by decide) (by decide)
    (product_fitting hE) T R hT hTne hR hRT
  let f : E →* R := (MonoidHom.inr S E).codRestrict R (by intro e; exact ⟨rfl, mem_top _⟩)
  exact isCyclic_of_injective f (fun x y hxy => congrArg (fun r : R => r.val.2) hxy)

/-- Restrict the genuine cover to the inverse image of S₃ times each elementary
three-subgroup of the second factor, and apply A.1.31(1) there. -/
theorem second_primeRank_le_one_of_symmetricThree
    (h131 : EarlierA131One.{u}) (h : SQTKQuotient K D)
    {A B : Subgroup D} (hprod : InternalProduct A B)
    (f : Equiv.Perm (Fin 3) →* A) (hf : Function.Injective f) :
    primeRank 3 B ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le B).mpr
  intro E hE
  let := hE
  let j : (S × E) →* D := hprod.equiv.toMonoidHom.comp (f.prodMap E.subtype)
  have hj : Function.Injective j := by
    intro x y hxy
    have hh := hprod.equiv.injective hxy
    exact Prod.ext (hf (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let := cyclic_of_product_cover h131 (coverOfInjective h j hj)
    (IsElementaryAbelian.isPGroup 3 E)
  have hcard : Nat.card E ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 3 E
  simpa using Nat.le_of_dvd (by decide : 0 < 3) hcard
end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
