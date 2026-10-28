module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Targets
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.ThreeFree
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.SolvableRadical

/-!
# The Fitting and layer argument for a strict closure

The Fitting preimage has solvable join with H, so the actual maximal-prime
bound restricts its primes. Centralizer coprimality eliminates those odd
primes, while O₂(Mc/O₂(Mc))=1 eliminates two. Any component outside the normal
closure then lies in a three-prime centralizer and must be Suzuki; the proved
Suzuki exclusion removes it. The closure image is therefore F*(Mc/O₂(Mc)).

The literal source application is ExchangedLayer. Its model comparison is
still owned by qt-e-suitable-odd-normalizer, along with final source assembly.
Source: Aschbacher--Smith, proof of 14.6.14, printed p.1033.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

/-- The maximal-prime bound also controls the actual Fitting subgroup of the
two-core quotient: its preimage has solvable join with the original H. -/
theorem fitting_quotient_prime_support
    {H Mc : Subgroup G} (hHMc : H ≤ Mc) (hs : Group.IsSolvable H)
    {p : ℕ} (hbound : SolvableOvergroupPrimeBound H Mc p)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card (fittingSubgroup (Mc ⧸ pCore 2 Mc))) :
    r = 2 ∨ r = 3 ∨ (p = 5 ∧ r = 5) := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let F := fittingSubgroup (Mc ⧸ pCore 2 Mc)
  let D := F.comap q
  let A := H.subgroupOf Mc
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable D := isSolvable_comap_of_solvable_ker q F
  let : D.Normal := inferInstance
  let := hs
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hHMc).toMonoidHom) (subgroupOfEquivOfLe hHMc).injective
  let : Group.IsSolvable (D ⊔ A : Subgroup Mc) := Group.isSolvable_sup_of_normal_left D A
  let J := (D ⊔ A : Subgroup Mc).map Mc.subtype
  have hHJ : H ≤ J := by
    have hh := map_mono (f := Mc.subtype) (show A ≤ D ⊔ A from le_sup_right)
    rwa [map_subgroupOf_eq_of_le hHMc] at hh
  have hJs : Group.IsSolvable J := Group.isSolvable_of_surjective
    (Mc.subtype.subgroupMap_surjective (D ⊔ A))
  apply hbound J hHJ (map_subtype_le _) hJs r hr
  have hFD : Nat.card F ∣ Nat.card D := by
    have hh := card_map_dvd D q
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hh
  rw [card_map_of_injective Mc.subtype_injective]
  exact hd.trans (hFD.trans (card_dvd_of_le (show D ≤ D ⊔ A from le_sup_left)))

/-- A layer subgroup with the source centralizer exclusions kills the Fitting
subgroup; the prime support is derived on the actual solvable extension. -/
theorem fitting_quotient_eq_bot_of_closure_centralizers
    {H Mc : Subgroup G} (hHMc : H ≤ Mc) (hs : Group.IsSolvable H)
    {p : ℕ} (hbound : SolvableOvergroupPrimeBound H Mc p)
    (K : Subgroup (Mc ⧸ pCore 2 Mc)) (hK : K ≤ componentLayer (Mc ⧸ pCore 2 Mc))
    (h3 : Nat.Coprime 3 (Nat.card (centralizer (K : Set (Mc ⧸ pCore 2 Mc)))))
    (h5 : p = 5 → Nat.Coprime 5 (Nat.card (centralizer (K : Set (Mc ⧸ pCore 2 Mc))))) :
    fittingSubgroup (Mc ⧸ pCore 2 Mc) = ⊥ := by
  let F := fittingSubgroup (Mc ⧸ pCore 2 Mc)
  have hFC : F ≤ centralizer (K : Set (Mc ⧸ pCore 2 Mc)) :=
    le_centralizer_iff.mp (hK.trans (componentLayer_le_centralizer_solvable_normal F))
  have h2 : Nat.Coprime 2 (Nat.card F) := pPrimeCore_coprime_card.coprime_dvd_right
    (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 (pCore_quotient_pCore_eq_bot 2)))
  apply (eq_bot_iff_card F).mpr
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro r hr hd
  rcases fitting_quotient_prime_support hHMc hs hbound hr hd with rfl | rfl | ⟨hp,rfl⟩
  · exact Nat.prime_two.coprime_iff_not_dvd.mp h2 hd
  · exact Nat.prime_three.coprime_iff_not_dvd.mp h3 (hd.trans (card_dvd_of_le hFC))
  · exact (by decide : Nat.Prime 5).coprime_iff_not_dvd.mp (h5 hp)
      (hd.trans (card_dvd_of_le hFC))

/-- Once F vanishes, three-prime centralizer and the proved Suzuki exclusion
force a normal layer subgroup to be the whole generalized Fitting subgroup. -/
theorem closure_eq_generalizedFitting_of_centralizer
    (Mc : Subgroup G) (hsq : IsSQTK KnownSimple.IsKnownSimple Mc)
    (hno : NoSuzukiComponents Mc)
    (K : Subgroup (Mc ⧸ pCore 2 Mc)) [K.Normal]
    (hK : K ≤ componentLayer (Mc ⧸ pCore 2 Mc))
    (hF : fittingSubgroup (Mc ⧸ pCore 2 Mc) = ⊥)
    (h3 : Nat.Coprime 3 (Nat.card (centralizer (K : Set (Mc ⧸ pCore 2 Mc))))) :
    K = generalizedFitting (Mc ⧸ pCore 2 Mc) := by
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Mc ⧸ pCore 2 Mc) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  rw [generalizedFitting,hF,bot_sup_eq]
  apply le_antisymm hK
  apply sSup_le
  intro D hD
  rcases hD.normal_dichotomy K with hDK | hcomm
  · exact hDK
  · have hc : D ≤ centralizer (K : Set (Mc ⧸ pCore 2 Mc)) :=
      commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hd : ¬ 3 ∣ Nat.card D := fun hd => Nat.prime_three.coprime_iff_not_dvd.mp h3
      (hd.trans (card_dvd_of_le hc))
    have hmodel := ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      _ hQ (pCore_quotient_pCore_eq_bot 2) D hD.isCComponent
    obtain ⟨m,hm,he⟩ := hmodel.suzuki_of_three_free hd
    let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
    obtain ⟨J,hJ,hJD⟩ := hD.isCComponent.exists_map_quotient_eq (pCore 2 Mc)
    have heJ : (J.map Mc.subtype).subgroupOf Mc = J :=
      comap_map_eq_self_of_injective Mc.subtype_injective J
    exfalso
    apply hno (J.map Mc.subtype) (map_subtype_le _) (by rwa [heJ]) m (by omega)
    rw [heJ,hJD]
    exact he
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
