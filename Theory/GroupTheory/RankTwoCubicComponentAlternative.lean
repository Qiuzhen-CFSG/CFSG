module

public import Theory.GroupTheory.RankTwoCharacteristicThreeQuotient
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter
public import Theory.GroupTheory.CComponent.TwoComponent
public import Theory.GroupAction.NormalComplement

/-!
# Components forced by a noncyclic abelian cubic quotient

Let A be an image of a finite group of three-rank at most two, and suppose
A has a noncyclic abelian three-group quotient. Its three-prime core is
killed by the quotient map. If A/O₃′(A) has no ordinary components, its
three-core is self-centralizing; the characteristic-three quotient theorem
then makes A/O₃′(A) a three-group. Thus A has a normal three-complement.

Contrapositively, failure of a normal three-complement produces an actual
ordinary component in A/O₃′(A). Its order is divisible by three, since the
ambient three-prime core is trivial and prime-complement cores are monotone
along subnormal inclusions. No solvability premise or component lifting
through an arbitrary kernel is used.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

variable {B A D : Type*} [Group B] [Finite B] [Group A] [Finite A]
  [Group D] [IsMulCommutative D]

omit [IsMulCommutative D] in
private theorem threePrimeCore_le_kernel_of_three_target
    (q : A →* D) (hD : IsPGroup 3 D) : pPrimeCore 3 A ≤ q.ker := by
  let R := (pPrimeCore 3 A).map q
  have hc : Nat.Coprime 3 (Nat.card R) :=
    (pPrimeCore_coprime_card (p := 3) (G := A)).of_dvd_right
      ((pPrimeCore 3 A).card_map_dvd q)
  have hcard : Nat.card R = 1 := (hD.to_subgroup R).card_eq_or_dvd.resolve_right
    (Nat.prime_three.coprime_iff_not_dvd.mp hc)
  exact (Subgroup.map_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hcard)

/-- Absence of ordinary components after quotienting the three-prime core
forces a normal three-complement. Rank remains on the original cover. -/
theorem hasNormalThreeComplement_of_no_components_of_noncyclic_abelian_quotient
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (hnoncyclic : ¬IsCyclic D)
    (hnc : ∀ L : Subgroup (A ⧸ pPrimeCore 3 A),
      ¬IsComponent (A ⧸ pPrimeCore 3 A) L) : HasNormalPComplement 3 A := by
  let O := pPrimeCore 3 A
  let π := QuotientGroup.mk' O
  have hkill : O ≤ q.ker := threePrimeCore_le_kernel_of_three_target q hD
  let f : (A ⧸ O) →* D := QuotientGroup.lift O q hkill
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective O q hq hkill
  have hc : centralizer (pCore 3 (A ⧸ O) : Set (A ⧸ O)) ≤ pCore 3 (A ⧸ O) := by
    have hh := centralizer_core_product_le_of_no_components 3 hnc
    simpa only [pPrimeCore_quotient_pPrimeCore_eq_bot,sup_bot_eq] using hh
  have hp : IsPGroup 3 (A ⧸ O) :=
    isThreeGroup_of_characteristic_three_of_noncyclic_abelian_quotient
      (π.comp cover) ((QuotientGroup.mk'_surjective O).comp hcover) hrank
      hc f hf hD hnoncyclic
  exact ⟨O,inferInstance,pPrimeCore_coprime_card,hp⟩

private theorem component_three_dvd_of_threePrimeCore_bot
    {X : Type*} [Group X] [Finite X] (hcore : pPrimeCore 3 X = ⊥)
    (L : Subgroup X) (hL : IsComponent X L) : 3 ∣ Nat.card L := by
  by_contra hn
  have hc : Nat.Coprime 3 (Nat.card L) := Nat.prime_three.coprime_iff_not_dvd.mpr hn
  have htop : pPrimeCore 3 L = ⊤ := top_unique (le_sSup ⟨inferInstance,by simpa using hc⟩)
  have hh := hL.1.pPrimeCore_map_le (p := 3)
  rw [htop,←MonoidHom.range_eq_map,range_subtype,hcore] at hh
  have hb : L = ⊥ := bot_unique hh
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  exact (nontrivial_iff_ne_bot L).mp inferInstance hb

/-- Failure of a normal three-complement forces an ordinary component of
three-divisible order in the literal quotient by the three-prime core. -/
theorem exists_component_of_not_normalThreeComplement_of_noncyclic_abelian_quotient
    (cover : B →* A) (hcover : Function.Surjective cover) (hrank : primeRank 3 B ≤ 2)
    (q : A →* D) (hq : Function.Surjective q) (hD : IsPGroup 3 D)
    (hnoncyclic : ¬IsCyclic D) (hnot : ¬HasNormalPComplement 3 A) :
    ∃ L : Subgroup (A ⧸ pPrimeCore 3 A),
      IsComponent (A ⧸ pPrimeCore 3 A) L ∧ 3 ∣ Nat.card L := by
  have hex : ∃ L : Subgroup (A ⧸ pPrimeCore 3 A),
      IsComponent (A ⧸ pPrimeCore 3 A) L := by
    by_contra hn
    exact hnot (hasNormalThreeComplement_of_no_components_of_noncyclic_abelian_quotient
      cover hcover hrank q hq hD hnoncyclic (fun L hL => hn ⟨L,hL⟩))
  obtain ⟨L,hL⟩ := hex
  exact ⟨L,hL,component_three_dvd_of_threePrimeCore_bot
    (pPrimeCore_quotient_pPrimeCore_eq_bot 3) L hL⟩

end Theory.GroupTheory
