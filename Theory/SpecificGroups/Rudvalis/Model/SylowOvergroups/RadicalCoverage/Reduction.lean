module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.CoverageReduction
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# The fixed-local-subgroup reduction for Rudvalis radical normalizers

The remaining calculation splits into two independent obligations. First,
the concrete ATLAS subgroup max4 must contain an ambient Sylow two-subgroup.
Second, classify the maximal normalizers of radical subgroups normal in one
explicit Sylow two-subgroup of max4. This second calculation does not require
an ambient Sylow certificate as an input. Once the first obligation is known,
the subgroup index formula makes this chosen Sylow subgroup ambient Sylow too.

Given both obligations, an odd-index radical normalizer contains an ambient
Sylow subgroup. Conjugation moves this to the one inside max4. The local
calculation applies, and conjugation supplies actual multiplicative
equivalences of normalizers on the preserved degree-4060 carrier.

Source: [Asc86b], as used in Aschbacher--Smith, proof of Proposition 1.3.4,
printed p.511 (PDF p.528); GLS3 Table 5.3r motivates the local candidates.
The propositions below are unproved local obligations, not source theorems.
-/

namespace Rudvalis.SylowOvergroups

open Subgroup

/-- The fourth ATLAS candidate contains a Sylow subgroup of the ambient
degree-4060 model. No assertion about the full model order is needed. -/
@[expose] public def Max4ContainsSylow : Prop :=
  ∃ S : Sylow 2 Model, (S : Subgroup Model) ≤ max4

/-- The local calculation for one Sylow subgroup of max4. The two inclusions
say that U is normal in the ambient image of S; they do not assert ambient
normality. Radicality is still taken in the whole Rudvalis model. -/
@[expose] public def Max4RadicalNormalizerCover : Prop :=
  ∃ S : Sylow 2 max4, ∀ U : Subgroup Model, U.IsPRadical 2 →
    U ≤ (S : Subgroup max4).map max4.subtype →
    (S : Subgroup max4).map max4.subtype ≤ normalizer (U : Set Model) →
    IsCoatom (normalizer (U : Set Model)) →
    Nonempty (normalizer (U : Set Model) ≃* max4) ∨
      Nonempty (normalizer (U : Set Model) ≃* max6)

/-- A checked self-normalizer calculation for a two-subgroup of max4
suffices for the ambient Sylow obligation. -/
public theorem max4ContainsSylow_of_selfNormalizer (P : Subgroup Model)
    (hP : IsPGroup 2 P) (hP4 : P ≤ max4)
    (hN : normalizer (P : Set Model) = P) : Max4ContainsSylow := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_isPGroup_of_normalizer_eq P hP hN
  exact ⟨S, hS.symm ▸ hP4⟩

/-- The fixed-local calculation and the ambient Sylow certificate imply
the requested global radical-normalizer cover. Both premises still need
to be constructed for the concrete model. -/
public theorem oddIndexMaximalRadicalCover_of_max4
    (hSylow : Max4ContainsSylow) (hcover : Max4RadicalNormalizerCover) :
    OddIndexMaximalRadicalCover := by
  obtain ⟨S, hS⟩ := hSylow
  obtain ⟨Q, hQ⟩ := hcover
  have h4index : ¬ 2 ∣ max4.index := fun h =>
    S.not_dvd_index (h.trans (index_dvd_of_le hS))
  have hQindex : ¬ 2 ∣ ((Q : Subgroup max4).map max4.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul Q.not_dvd_index h4index
  let T : Sylow 2 Model := (Q.isPGroup'.map max4.subtype).toSylow hQindex
  intro U hU hmax hodd
  obtain ⟨g, hUT, hTU⟩ := hU.exists_conjugate_le_and_le_normalizer T hodd
  let e := MulAut.conj g
  let V := U.map e.toMonoidHom
  have hV : V.IsPRadical 2 := hU.map_equiv e
  have hN : (normalizer (U : Set Model)).map e.toMonoidHom =
      normalizer (V : Set Model) := map_equiv_normalizer_eq U e
  have hmaxV : IsCoatom (normalizer (V : Set Model)) :=
    hN ▸ (OrderIso.isCoatom_iff e.mapSubgroup _).mpr hmax
  have hlocal := hQ V hV hUT hTU hmaxV
  let eN : normalizer (U : Set Model) ≃* normalizer (V : Set Model) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr hN)
  exact hlocal.imp (Nonempty.map fun f => eN.trans f) (Nonempty.map fun f => eN.trans f)

end Rudvalis.SylowOvergroups
