module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionQuotientTransfer
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionBinaryCentralizer

/-!
# The literal binary centralizer cannot embed in the doubled model centralizer

In the remaining strict-enlargement branch, the original local action gives
an actual SL₄(2) or SL₅(2) marking of the component image. Its full centralizer
has order prime to three, using the strongly quasithin original normalizer
and the explicit inverted-plane argument. An order dividing 36 would make
this centralizer a normal two-group, hence trivial. The outer two-group then
puts the full normalizer action in the local actor. Its invariant Sylow orbit
therefore equals the normalizer orbit.

Thus every remaining strict enlargement has a three-free centralizer whose
order does not divide 36, and cannot embed in S₃ × S₃. This discharges the
final centralizer exclusion in D.3.9 once multiplicity two supplies that
embedding. That construction, general U = W and final Source325 assembly
remain with qt-baumann-fsu; no multiplicity or centralizer bound is assumed
in the strict-enlargement conclusion. All original markings and hmany remain.
Source: Aschbacher--Smith D.3.9(1), D.3.13 and 3.2.5,
printed pp.200,202,580--581; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The marked binary branch has three-free component centralizer in the
literal faithful normalizer image. The rank bound stays on the preimage. -/
theorem normalizer_binary_component_centralizer_three_free
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {d : ℕ} (hd : 4 ≤ d)
    (e : ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _))) ≃*
      SL(d,ZMod 2)) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
    ¬ 3 ∣ Nat.card (centralizer (K : Set (internalActionImage M U (le_normalizer_componentOrbit V M)))) := by
  intro M U K
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hr : primeRank 3 M ≤ 2 :=
    (h.simpleQTKE.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  exact binary_component_centralizer_three_free f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective hr K hd e

/-- A full local actor makes the actual Sylow orbit normalizer-invariant. -/
theorem normalizerOrbit_eq_of_localActor_eq_top
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (htop : D.normalizerLocalActor = ⊤) :
    componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let ρ := UniqueFactor.imageRepresentation M U hn
  apply le_antisymm
  · apply iSup_le
    intro g
    rintro _ ⟨v,hv,rfl⟩
    have hs := D.normalizerLocalActor_stabilizes_section h
      (show f g ∈ D.normalizerLocalActor from htop ▸ mem_top _)
    let v' : Additive U := Additive.ofMul ⟨v,le_componentOrbit V M hv⟩
    have hv' : v' ∈ internalSection U W := le_componentOrbit V T hv
    exact (hs v').mpr hv'
  · exact iSup_conjugates_le_of_le_normalizer V T U
      (le_componentOrbit V M) (D.sylow_normalizes_component.trans hn)

/-- Once the actual binary centralizer order divides 36, the original
normalizer and Sylow orbits coincide. -/
theorem normalizerOrbit_eq_of_binary_centralizer_card_dvd
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _))) ≃*
      SL(d,ZMod 2))
    (hcard : let M := normalizer (L : Set G)
      let U := componentOrbit V M
      let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
      Nat.card (centralizer (K : Set (internalActionImage M U (le_normalizer_componentOrbit V M)))) ∣ 36) :
    componentOrbit V (normalizer (L : Set G)) = componentOrbit V (T : Subgroup G) := by
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hmax : IsMaximalTwoLocal M := by
    simpa only [D.localOrbit_eq] using hu.normalizer_maximal
  have hr : primeRank 3 M ≤ 2 :=
    (h.simpleQTKE.twoLocal_sqtk hmax.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  apply D.normalizerOrbit_eq_of_localActor_eq_top h.toHypothesis1221
  rw [D.normalizerLocalActor_eq_component_sup_sylow]
  exact binary_sylow_supplement_of_centralizer_card_dvd f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective hr K hd e
    (D.normalizerActor_twoCore_eq_bot h.toHypothesis1221) hcard
    (internalSylow T M U hn D.sylow_normalizes_component)

/-- Every strict enlargement has a three-free binary component centralizer
whose order cannot divide 36. The remaining local obligation is to construct
the multiplicity-two centralizer embedding, not to exclude such an embedding. -/
theorem normalizer_strict_binary_centralizer_obstruction
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
    let C := centralizer (K : Set (internalActionImage M U (le_normalizer_componentOrbit V M)))
    (∃ d : ℕ, (d = 4 ∨ d = 5) ∧
      IsNaturalPlusDual (D.normalizerLocalComponentAction h.toHypothesis1221) d) ∧
      ¬ 3 ∣ Nat.card C ∧ ¬ Nat.card C ∣ 36 := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro M U K C
  obtain ⟨A,hAS,hA,hAC,hoff,d,hd,⟨a⟩⟩ :=
    D.exists_normalizer_local_naturalDual_of_moved_of_many h hmany hc hm hne
  exact ⟨⟨d,hd,⟨a⟩⟩,
    D.normalizer_binary_component_centralizer_three_free h (by omega) a.groupEquiv,
    fun hcard => hne (D.normalizerOrbit_eq_of_binary_centralizer_card_dvd h hd a.groupEquiv hcard)⟩

/-- The remaining strict enlargement cannot have the centralizer embedding
provided by two copies of the natural and two copies of the dual module. -/
theorem normalizer_strict_centralizer_not_symmetricThreePair
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G)) :
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U (le_normalizer_componentOrbit V M))
    let C := centralizer (K : Set (internalActionImage M U (le_normalizer_componentOrbit V M)))
    ∀ f : C →* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)), ¬ Function.Injective f := by
  intro M U K C f hf
  have hb := (D.normalizer_strict_binary_centralizer_obstruction h hmany hc hm hne).2.2
  apply hb
  have hd := Subgroup.card_dvd_of_injective f hf
  have he : Nat.card (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 36 := by
    rw [Nat.card_prod,Nat.card_perm,Nat.card_fin]
    rfl
  exact he ▸ hd

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
