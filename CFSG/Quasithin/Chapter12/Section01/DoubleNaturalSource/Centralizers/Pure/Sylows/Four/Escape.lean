module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Index
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Point
public import Theory.GroupTheory.SylowIndexTwoOvergroup

/-!
# A contrary enlargement of the original pure-point Sylow

The marked T₁ has half the order of T. A larger two-subgroup in C_G(w)
is therefore an ambient Sylow. The local Sylow theorem forces its
intersection with M to be exactly T₁, while index two makes it normalize
T₁. Thus N_G(T₁) escapes M. Local uniqueness then excludes a nontrivial
characteristic subgroup of T₁ normal in LT.

Generation by T and the actual point residual is supplied separately in
`Generation`; it turns the last restriction into the relative MS3 clause.
Source: Aschbacher--Smith 12.1.4, printed p.790. Final Sylow and pure-core
assembly remains with `qt-d-double-natural-pure-fusion`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

private theorem half_sylow_escape
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) (Q H M : Subgroup G)
    (hQT : Q ≤ (T : Subgroup G)) (hi : Q.relIndex T = 2)
    (hrel : CFSG.Quasithin.Chapter1.IsSylowIn 2 Q (M ⊓ H))
    (hfail : ¬ CFSG.Quasithin.Chapter1.IsSylowIn 2 Q H) :
    (T : Subgroup G) ≤ normalizer (Q : Set G) ∧
      ∃ P : Sylow 2 G, Q < (P : Subgroup G) ∧ (P : Subgroup G) ≤ H ∧
        Q.relIndex P = 2 ∧ (P : Subgroup G) ≤ normalizer (Q : Set G) ∧
        (P : Subgroup G) ⊓ M = Q ∧ ¬ (P : Subgroup G) ≤ M ∧
        ¬ normalizer (Q : Set G) ≤ M := by
  have hnT : (Q.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTN := (normal_subgroupOf_iff_le_normalizer hQT).mp hnT
  obtain ⟨hQ,hQMH,hmax⟩ := CFSG.Quasithin.Chapter1.isSylowIn_iff.mp hrel
  have hQH := hQMH.trans inf_le_right
  obtain ⟨R,hR⟩ := hQ.comap_subtype.exists_le_sylow (G := H)
  let U := (R : Subgroup H).map H.subtype
  have hQU : Q ≤ U := by
    rw [← map_subgroupOf_eq_of_le hQH]
    exact map_mono hR
  have hUH : U ≤ H := map_subtype_le _
  have hU : IsPGroup 2 U := R.isPGroup'.map H.subtype
  have hne : U ≠ Q := fun he => hfail ⟨R,he⟩
  obtain ⟨hbound,he | ⟨P,hP⟩⟩ := two_group_over_index_two_sylow T Q U hQT hi hU hQU
  · exact (hne he).elim
  have hidx : Q.relIndex U = 2 := by
    have hpos : Q.relIndex U ≠ 0 := (Q.subgroupOf U).index_ne_zero_of_finite
    have hnot : Q.relIndex U ≠ 1 := fun hh => hne (le_antisymm (relIndex_eq_one.mp hh) hQU)
    omega
  have hnU : (Q.subgroupOf U).Normal := normal_of_index_eq_two hidx
  have hUN := (normal_subgroupOf_iff_le_normalizer hQU).mp hnU
  have hinter : U ⊓ M = Q := hmax _ hU.to_inf_left
    (le_inf hQU (hQMH.trans inf_le_left)) (le_inf inf_le_right (inf_le_left.trans hUH))
  have hout : ¬ U ≤ M := by
    intro hUM
    exact hne ((inf_eq_left.mpr hUM).symm.trans hinter)
  refine ⟨hTN,P,?_,?_,?_,?_,?_,?_,?_⟩ <;> try rw [hP]
  · exact lt_of_le_of_ne hQU hne.symm
  · exact hUH
  · exact hidx
  · exact hUN
  · exact hinter
  · exact hout
  · exact fun hh => hout (hUN.trans hh)

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem doubleNatural_pure_sylow_escape_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      let R := (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)
      ¬ Chapter1.IsSylowIn 2 R (B.pointCentralizer w) →
      (T : Subgroup G) ≤ normalizer (R : Set G) ∧
        ∃ P : Sylow 2 G, R < (P : Subgroup G) ∧ (P : Subgroup G) ≤ B.pointCentralizer w ∧
          R.relIndex P = 2 ∧ (P : Subgroup G) ≤ normalizer (R : Set G) ∧
          (P : Subgroup G) ⊓ normalizer (L : Set G) = R ∧
          ¬ (P : Subgroup G) ≤ normalizer (L : Set G) ∧
          ¬ normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix R hf
  exact half_sylow_escape T _ _ _ inf_le_left
    (S.naturalSylowNormalizer_relIndex D.sylow_normalizes_component)
    (D.doubleNatural_marked_pure_relative_sylow_of_many h hmany B S w hw hp hfix).2 hf

theorem doubleNatural_pure_characteristic_normal_restriction_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      let R := (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G)
      ¬ Chapter1.IsSylowIn 2 R (B.pointCentralizer w) →
      ∀ C : Subgroup R, C.Characteristic →
        ((C.map R.subtype).subgroupOf (L ⊔ (T : Subgroup G))).Normal → C = ⊥ := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix R hf C hC hnC
  let := hC
  have hout := (D.doubleNatural_pure_sylow_escape_of_many h hmany B S w hw hp hfix hf).2
  obtain ⟨P,_,_,_,_,_,_,hN⟩ := hout
  by_contra hne
  have hmapne : C.map R.subtype ≠ ⊥ := by
    intro he
    exact hne ((map_injective R.subtype_injective) (he.trans (Subgroup.map_bot _).symm))
  have hCL : C.map R.subtype ≤ L ⊔ (T : Subgroup G) :=
    (map_subtype_le C).trans (inf_le_left.trans le_sup_right)
  exact hN ((normalizer_le_normalizer_characteristic_image R C).trans
    (D.normal_subgroup_normalizer_le h.toHypothesis1221 hCL hmapne
      ((normal_subgroupOf_iff_le_normalizer hCL).mp hnC)))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
