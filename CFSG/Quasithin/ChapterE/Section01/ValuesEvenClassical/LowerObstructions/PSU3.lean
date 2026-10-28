module
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSU3.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSU3.RootCenter
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSU3.RootPairs
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.SpecificGroups.SU3.BinarySylowOrder
/-!
# PSU₃ even order and the lower obstruction in E.1.14(1)

The actual Hermitian root subgroup has order (2^f)^3. Transport through the
model equivalence and the subgroup inclusion proves even ambient order,
for every nondegenerate Hermitian form with the prescribed Frobenius.
The matrix field has order (2^f)^2, and f need not be prime.

For the lower obstruction, use the ambient conjugates of Z(L ∩ T). The
root-center theorem computes its rank as f and its weak closure in T as
itself. Its normalizer is proper. E0 forces every applicable E-member to
contain L ∩ T, and root-pair generation forces any member escaping the
normalizer to contain L. Both literal E-member quotients then preserve the
center's rank, contradicting the bound f - 1.

The model geometry is discharged for every normal simple PSU₃(2^f) subgroup,
including arbitrary ambient outer automorphisms. Specializing to L = F*(G)
gives the requested lower bound and even order under the source hypotheses.
The lower argument does not require the additional SQTK and G = LT guards.
The independent upper bound needed for n(G) = f is not asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
E.1.1–6 and E.1.14(1), printed pp.209–211, 214; Huppert II.10.12.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical
open BenderSuzuki.MatrixGroups.HermitianForm
variable {G : Type*} [Group G]
/-- A genuine PSU₃(2^f) subgroup forces even ambient order via its actual root subgroup. -/
theorem not_odd_card_of_isPSU3 (L : Subgroup G) {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) : ¬ Odd (Nat.card G) := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hroot := BinarySylowOrder.cube_dvd_card_projective J (by omega : f ≠ 0)
    hcard hconj
  have htwo : 2 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact (dvd_pow_self 2 (by omega : f ≠ 0)).trans
      ((dvd_pow_self (2 ^ f) (by decide : 3 ≠ 0)).trans hroot)
  exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr
    (htwo.trans L.card_subgroup_dvd_card))

open PSU3

/-- The actual PSU₃ source consumer for the geometric lower-obstruction inputs.
No assumptions on a chosen matrix form or on the outer action are discarded.
This is a conditional application, not the completed source lower bound. -/
theorem psu3_lower_bounds_of_root_geometry [Finite G]
    (L : Subgroup G) (T : Sylow 2 G) [IsSimpleGroup L]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f))
    (hZelem : IsElementaryAbelian 2 (rootCenter L T))
    (hZ0 : rootCenter L T ≠ ⊥) (hZLne : rootCenter L T ≠ L)
    (hZrank : Group.rank (rootCenter L T) = f)
    (huniq : ∀ g : G, (rootCenter L T).map (MulAut.conj g).toMonoidHom ≤
      (T : Subgroup G) →
      (rootCenter L T).map (MulAut.conj g).toMonoidHom = rootCenter L T)
    (hpair : ∀ g : G, (rootSection L T).map (MulAut.conj g).toMonoidHom ≠
      rootSection L T →
      L ≤ rootSection L T ⊔ (rootSection L T).map (MulAut.conj g).toMonoidHom) :
    ¬ IsEGenerated (f - 1) G ∧ ¬ Odd (Nat.card G) :=
  ⟨not_isEGenerated_of_root_geometry L T (by omega) hZelem hZ0 hZLne hZrank huniq
      (root_overgroup_of_conjugate_join L T hpair),
    not_odd_card_of_isPSU3 L (by omega) hmodel⟩

/-- The PSU₃ lower obstruction and even order, with every root-geometry
premise proved from the actual model. Normality covers all ambient conjugations. -/
theorem psu3_lower_bounds_of_normal [Finite G]
    (L : Subgroup G) [L.Normal] [IsSimpleGroup L] (T : Sylow 2 G)
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    ¬ IsEGenerated (f - 1) G ∧ ¬ Odd (Nat.card G) := by
  obtain ⟨helem, hne, hproper, hrank, huniq⟩ := rootCenter_geometry L T hf hmodel
  exact psu3_lower_bounds_of_root_geometry L T hf hmodel helem hne hproper hrank huniq
    (rootSection_conjugate_join L T hf hmodel)

/-- The lower-bound inputs for the PSU₃ clause of E.1.14(1), applied to the
literal generalized Fitting subgroup. No additional geometric premise remains. -/
theorem psu3_lower_bounds [Finite G]
    [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)] (T : Sylow 2 G)
    {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU (Theory.GroupTheory.generalizedFitting G) 3 (2 ^ f)) :
    ¬ IsEGenerated (f - 1) G ∧ ¬ Odd (Nat.card G) :=
  psu3_lower_bounds_of_normal (Theory.GroupTheory.generalizedFitting G) T hf hmodel

/-- Failure of predecessor-rank E-generation for the actual PSU₃ generalized
Fitting subgroup, including its ambient outer two-extensions. -/
theorem not_isEGenerated_of_isPSU3 [Finite G]
    [IsSimpleGroup (Theory.GroupTheory.generalizedFitting G)] (T : Sylow 2 G)
    {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU (Theory.GroupTheory.generalizedFitting G) 3 (2 ^ f)) :
    ¬ IsEGenerated (f - 1) G :=
  (psu3_lower_bounds T hf hmodel).1

end CFSG.Quasithin.ChapterE.ValuesEvenClassical
