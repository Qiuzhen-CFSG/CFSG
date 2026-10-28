module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvablePrimeModels
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ResidualKernel
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual

/-!
# The actual quotient model in the solvable two-three branch

When X/O₂(X) is a {2,3}-group, so is X. Its three-prime core is therefore
O₂(X). Locality activates the literal relative-centralizer clause (c),
which makes the full omega-action kernel prime to three. Reducedness then
identifies this kernel with O₂(X), retaining the original embedded module.

The already constructed F.6 models consequently describe X/O₂(X) itself.
In the product S₃ × S₃ model, the whole two-residual is abelian of order
nine. Thus the original two residuals commute on the omega module.
Noncommuting actions exclude that model and select an actual isomorphism
to the Heisenberg extension 3₊¹⁺² ⋊ E₄.

The {2,3} premise is explicit. SolvableOddPrimeReduction constructs the
remaining odd-prime obstruction from its negation; excluding that
obstruction, proving the six-dimensional module and Thompson normality,
and excluding this case for the original plane are still required for
13.4.7. Source: Aschbacher--Smith 13.4.7, printed pp.901--902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

/-- For a two-three group the full three-prime core is its two-core. -/
theorem primeToThreeCore_eq_twoCore_of_twoThree (h : IsPiGroup twoThreePrimes G) :
    pPrimeCore 3 G = pCore 2 G := by
  have hp : IsPGroup 2 (pPrimeCore 3 G) := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
    intro p hp
    have hdiv := Nat.dvd_of_mem_primeFactors hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have he := (IsPiGroup_iff _ _).mp h ⟨p,hprime⟩
      (hdiv.trans (pPrimeCore 3 G).card_subgroup_dvd_card)
    rcases he with he | he
    · change p = 2 at he
      subst p
      norm_num
    · change p = 3 at he
      exact False.elim ((Nat.prime_three.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := 3) (G := G))) (he ▸ hdiv))
  exact le_antisymm (le_sSup ⟨inferInstance,hp⟩) ChapterF.twoCore_le_primeToThreeCore

private theorem twoThree_of_twoCore_quotient
    (h : IsPiGroup twoThreePrimes (G ⧸ pCore 2 G)) : IsPiGroup twoThreePrimes G := by
  apply IsPiGroup.of_normal_subgroup_and_quotient (pCore 2 G) ?_ h
  intro p hp
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  change p.val ∣ Nat.card (pCore 2 G) at hp
  rw [hn] at hp
  exact Or.inl ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
    (p.property.dvd_of_dvd_pow hp))

variable {T : Sylow 2 G} {L V A B : Subgroup G}
variable (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
include h₀ D m hTA hTB eA eB hne hindexA hindexB hcentral

/-- In the two-three branch, all three original quotients agree: the
prime-to-three quotient, the two-core quotient and the faithful omega action. -/
theorem original_pair_twoThree_full_kernel
    (h23 : IsPiGroup twoThreePrimes ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G))) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    pPrimeCore 3 X = pCore 2 X ∧ X ⊓ centralizer (W : Set G) = X.pCoreIn 2 := by
  let X := A ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let U := W.subgroupOf X
  let N := centralizer (U : Set X)
  have hlocal := original_pair_local D m hTA hTB eA eB hne hindexA hindexB
  have hres := (hcentral hlocal).2.2
  have hcore := primeToThreeCore_eq_twoCore_of_twoThree (twoThree_of_twoCore_quotient h23)
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  obtain ⟨hred,_,_,_⟩ := original_pair_action_kernel h₀ D m
    hTA hTB eA eB hne hindexA hindexB
  let : U.Normal := hred.normal
  have hmapN : N.map X.subtype = X ⊓ centralizer (W : Set G) := by
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) U
    simpa only [U,top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hWX] using hh.symm
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    rw [Nat.card_congr (N.equivMapOfInjective X.subtype X.subtype_injective).toEquiv,hmapN]
    exact original_pair_kernel_primeToThree h₀ D m hTA hTB eA eB hne hindexA hindexB hres
  have hN : N = pCore 2 X := le_antisymm
    ((show N ≤ pPrimeCore 3 X from le_sSup ⟨inferInstance,hcop⟩).trans hcore.le)
    (le_centralizer_iff.mp hred.le_centralizer_pCore)
  exact ⟨hcore,hmapN.symm.trans (congrArg (map X.subtype) hN)⟩

/-- The source model alternatives now concern the actual two-core quotient,
with the full kernel proved, once the odd-prime exclusion is available. -/
theorem original_pair_twoThree_models
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (h23 : IsPiGroup twoThreePrimes ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G))) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      (Nonempty ((X ⧸ pCore 2 X) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        Nonempty ((X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension)) := by
  obtain ⟨hc,hk⟩ := original_pair_twoThree_full_kernel h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcentral h23
  have hm := (original_pair_solvable_prime_models h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcores hs).2
  let e := QuotientGroup.quotientMulEquivOfEq hc.symm
  refine ⟨hk,?_⟩
  rcases hm with hm | hm
  · exact Or.inl ⟨e.trans hm.some⟩
  · exact Or.inr ⟨e.trans hm.some⟩

/-- Noncommuting original residual actions select the actual Heisenberg
extension in the two-three branch. The odd-prime exclusion remains explicit. -/
theorem original_pair_twoThree_noncommuting_model
    (hcores : A.pCoreIn 2 ≠ B.pCoreIn 2) (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (h23 : IsPiGroup twoThreePrimes ((A ⊔ B : Subgroup G) ⧸ pCore 2 (A ⊔ B : Subgroup G)))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension) := by
  obtain ⟨hk,hm⟩ := original_pair_twoThree_models h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcentral hcores hs h23
  refine ⟨hk,?_⟩
  rcases hm with hm | he
  · let e := hm.some
    exfalso
    apply hcomm
    let X := A ⊔ B
    let Q := X ⧸ pCore 2 X
    let q := QuotientGroup.mk' (pCore 2 X)
    let R := pResidual 2 Q
    have hcard : Nat.card R = 3 ^ 2 := by
      rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,map_pResidual]
      exact SymmetricThreeProductResidual.residual_card
    let : IsMulCommutative R := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard
    have hr : ⁅pResidual 2 X,pResidual 2 X⁆ ≤ pCore 2 X := by
      rw [←QuotientGroup.ker_mk' (pCore 2 X)]
      apply (Subgroup.map_eq_bot_iff (f := q) _).mp
      rw [map_commutator,map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
      exact commutator_self_eq_bot_iff.mpr inferInstance
    have hlocalres := commutator_mono
      (map_pResidual_le 2 (A.subgroupOf X).subtype)
      (map_pResidual_le 2 (B.subgroupOf X).subtype)
    have hh := map_mono (f := X.subtype) (hlocalres.trans hr)
    rw [map_commutator,map_embedded_pResidual,map_embedded_pResidual,
      map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right] at hh
    exact hh.trans (hk.symm.le.trans inf_le_right)
  · exact he

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
