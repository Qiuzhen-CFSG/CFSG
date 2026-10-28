module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddConjugation
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.Representation.BinaryPermutation.FiveOrbits
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# Reciprocal point centralizers in a marked A₅ module

The binary five-point core is the four-dimensional deleted permutation
module. Its nonzero alternating point stabilizers have order six or twelve,
so their literal centralizer preimages contain a cubic and are {2,3}-groups.
The point projection below records its precise kernel.

Every elementary offender on this module contains an odd permutation.
For an A₅ action, maximum elementary subgroups of a point radical therefore
centralize the module. B.2.10 identifies its Thompson and Baumann subgroups
with those of the ambient two-core. No block or Sylow-fixed-point premise
is needed for this component-level calculation.

The actual selected-component application is
Chapter13/Section04/FixedCoreSource/Nonsolvable/ComponentFive.lean.
Source: Aschbacher–Smith B.3.2(4), p.83, B.2.10(1), p.77, and the A₅
row of 13.4.10, printed pp.907–908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterB.AlternatingFivePoint
variable {H : Type*} [Group H] [Finite H]
variable (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
  (q : H →* alternatingGroup (Fin 5))
  (hq : Function.Surjective q) (hk : q.ker = pCore 2 H)
  (e : U ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
  (he : ∀ h u, (e (MulAut.conjNormal h u)).toAdd =
    BinaryPermutation.coreRepresentation (Fin 5) (q h).val (e u).toAdd)

include he in
omit [Finite H] [IsElementaryAbelian 2 U] in
private theorem action_fixed_iff (h : H) (u : U) :
    BinaryPermutation.coreRepresentation (Fin 5) (q h).val (e u).toAdd =
      (e u).toAdd ↔ h * u.val = u.val * h := by
  rw [←he,Multiplicative.toAdd.injective.eq_iff,e.injective.eq_iff,Subtype.ext_iff]
  exact mul_inv_eq_iff_eq_mul

include he in
omit [Finite H] [IsElementaryAbelian 2 U] in
/-- The marking identifies the literal action kernel. -/
theorem kernel_centralizer : q.ker = centralizer (U : Set H) := by
  ext h
  constructor
  · intro hh u hu
    have hh' : q h = 1 := hh
    have hf : BinaryPermutation.coreRepresentation (Fin 5) (q h).val (e ⟨u,hu⟩).toAdd =
        (e ⟨u,hu⟩).toAdd := by rw [hh']; simp
    exact ((action_fixed_iff U q e he h ⟨u,hu⟩).mp hf).symm
  · intro hh
    change q h = 1
    apply Subtype.ext
    apply BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)
    apply LinearMap.ext
    intro x
    let a := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    obtain ⟨v,rfl⟩ := a.surjective x
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd v)
    have hf := (action_fixed_iff U q e he h u).mpr (hh u.val u.property).symm
    rw [hu] at hf
    rw [←BinaryPermutation.coreEquivNatural_equivariant,
      ←BinaryPermutation.coreEquivNatural_equivariant]
    simpa using congrArg a hf

include hq he in
omit [Finite H] [IsElementaryAbelian 2 U] in
/-- Restrict the original quotient map to the actual vector centralizer. -/
theorem point_centralizer_projection (w : U) :
    ∃ f : centralizer ({w.val} : Set H) →*
        BinaryPermutation.FiveOrbits.evenStabilizer (e w).toAdd,
      Function.Surjective f ∧ f.ker = q.ker.subgroupOf (centralizer ({w.val} : Set H)) := by
  let C := centralizer ({w.val} : Set H)
  let P := BinaryPermutation.FiveOrbits.evenStabilizer (e w).toAdd
  have hf (h : C) : q h.val ∈ P :=
    (action_fixed_iff U q e he h.val w).mpr (mem_centralizer_singleton_iff.mp h.property)
  let f : C →* P := (q.comp C.subtype).codRestrict P hf
  refine ⟨f,?_,?_⟩
  · intro p
    obtain ⟨h,hh⟩ := hq p.val
    have hc : h ∈ C := mem_centralizer_singleton_iff.mpr
      ((action_fixed_iff U q e he h w).mp (by rw [hh]; exact p.property))
    exact ⟨⟨h,hc⟩,Subtype.ext hh⟩
  · ext h
    exact Subtype.ext_iff

include hq hk he in
omit [IsElementaryAbelian 2 U] in
/-- Every nonzero point centralizer contains a cubic and is a {2,3}-group. -/
theorem point_centralizer_cubic (w : U) (hw : w ≠ 1) :
    3 ∣ Nat.card (centralizer ({w.val} : Set H)) ∧
      IsPiGroup twoThreePrimes (centralizer ({w.val} : Set H)) := by
  obtain ⟨f,hf,hker⟩ := point_centralizer_projection U q hq e he w
  have hv : (e w).toAdd ≠ 0 := fun hh => hw (e.injective (hh.trans e.map_one.symm))
  have hc : Nat.card (BinaryPermutation.FiveOrbits.evenStabilizer (e w).toAdd) = 6 ∨
      Nat.card (BinaryPermutation.FiveOrbits.evenStabilizer (e w).toAdd) = 12 := by
    rw [BinaryPermutation.FiveOrbits.evenStabilizer_card,if_neg hv]
    split_ifs <;> simp
  have hthree : 3 ∣ Nat.card (BinaryPermutation.FiveOrbits.evenStabilizer (e w).toAdd) := by
    rcases hc with hc | hc <;> rw [hc] <;> decide
  refine ⟨hthree.trans (card_dvd_of_surjective f hf),?_⟩
  have hp : IsPGroup 2 f.ker := by rw [hker,hk]; exact pCore_isPGroup.comap_subtype
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hcard := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,hn] at hcard
  rw [IsPiGroup_iff]
  intro p hp
  rw [hcard] at hp
  change p.val = 2 ∨ p.val = 3
  rcases p.property.dvd_mul.mp hp with hc' | h2
  · have hd : p.val ∣ 2^2 * 3 := by
      rcases hc with hc | hc
      · rw [hc] at hc'; exact hc'.trans (by decide : 6 ∣ 2^2 * 3)
      · rw [hc] at hc'; exact hc'
    rcases p.property.dvd_mul.mp hd with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left p.property.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)

include hk he in
/-- The reciprocal point radical has the Thompson and Baumann subgroups of O₂(H). -/
theorem point_baumann (w : U) :
    let R := (centralizer ({w.val} : Set H)).pCoreIn 2
    elementaryAbelianMaxJ R = elementaryAbelianMaxJ (pCore 2 H) ∧
      baumann R = baumann (pCore 2 H) ∧ (baumann R).Normal := by
  let P := centralizer ({w.val} : Set H)
  let R := P.pCoreIn 2
  have hker := kernel_centralizer U q e he
  have hQP : pCore 2 H ≤ P := by
    rw [←hk,hker]
    intro h hh
    exact mem_centralizer_singleton_iff.mpr (hh w.val w.property).symm
  have hQR : pCore 2 H ≤ R :=
    le_pCoreIn_of_normalizes pCore_isPGroup hQP (by rw [normalizer_eq_top]; exact le_top)
  have hUR : U ≤ R :=
    (show U ≤ pCore 2 H from le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans hQR
  let f := (alternatingGroup (Fin 5)).subtype.comp q
  have hf : f.ker = centralizer (U : Set H) :=
    (MonoidHom.ker_comp_of_injective _ _ (alternatingGroup (Fin 5)).subtype_injective).trans hker
  have hJ := Offenders.thompson_le_kernel_of_even_core_action (Or.inl rfl) U R hUR f hf e he
    (by rintro _ ⟨h,_,rfl⟩; exact (q h).property)
  have hcore : pCore 2 H = R ⊓ centralizer (U : Set H) := by
    rw [←hker,hk,inf_eq_right.mpr hQR]
  have hb := lemma_B_2_10_centralizing U R hUR hQR hcore
    (by rw [thompsonJ_zero,←hf]; exact hJ)
  exact ⟨by simpa only [thompsonJ_zero] using hb.1,hb.2.1,hb.2.2.2⟩
end CFSG.Quasithin.ChapterB.AlternatingFivePoint
