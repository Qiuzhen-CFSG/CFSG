module

public import CFSG.Quasithin.ChapterC.Section06.Escape
public import Stellmacher.ResidualCommutatorIdempotence
public import Theory.GroupTheory.PGroup.SubnormalCore

/-!
# The general pushing-up lemma, C.6.3

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma C.6.3, printed pp. 166--167.

The first step derives the commutator bound needed for the conjugate-escape
argument. The two-core of `L` lies in the two-core of `L R` by subnormality.
The commutator `[Q,L]` is a normal two-subgroup of `L`, hence lies in that
two-core; idempotence of the action of `O^2(L)=L` then puts `[Q,L]` in `U`.
These initial theorems use a finite ambient group. The source only assumes
the named subgroups are finite; a local-finiteness version is still needed.
-/

namespace CFSG.Quasithin.ChapterC

open Subgroup Stellmacher

/-- Finite-ambient form of the commutator bound in the first paragraph of
C.6.3. All cores and residuals are mapped into the common ambient group. -/
public theorem c6_3_commutator_core_bound
    {G : Type*} [Group G] [Finite G]
    (L R : Subgroup G)
    (hRL : R ≤ normalizer (L : Set G))
    (hres : twoResidualAmbient L = L) :
    let S := L ⊔ R
    let Q := (pCore 2 S).map S.subtype
    let M := (pCore 2 L).map L.subtype
    ⁅L, Q⁆ ≤ ⁅M, L⁆ ∧ M ≤ Q := by
  classical
  let S := L ⊔ R
  let Q := (pCore 2 S).map S.subtype
  let M := (pCore 2 L).map L.subtype
  have hSL : S ≤ normalizer (L : Set G) :=
    sup_le (le_normalizer_iff_commutator_le_right.mpr (commutator_le_self L)) hRL
  have hLSnormal : (L.subgroupOf S).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hSL
  have hMQ : M ≤ Q :=
    pCoreAmbient_mono_of_isSubnormalIn L S 2 le_sup_left hLSnormal.isSubnormal
  have hSQ : S ≤ normalizer (Q : Set G) := by
    have hh := (pCore 2 S).le_normalizer_map S.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      using hh
  have hLQ : L ≤ normalizer (Q : Set G) := le_sup_left.trans hSQ
  have hQL : Q ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans hSL
  have hcommQ : ⁅Q, L⁆ ≤ Q :=
    le_normalizer_iff_commutator_le_left.mp hLQ
  have hcommL : ⁅Q, L⁆ ≤ L :=
    le_normalizer_iff_commutator_le_right.mp hQL
  have hcommNormal : ((⁅Q, L⁆).subgroupOf L).Normal :=
    (normal_subgroupOf_iff_le_normalizer hcommL).mpr
      (normalizer_commutator_ge_right Q L)
  have hcommM : ⁅Q, L⁆ ≤ M :=
    isPGroup_le_pCoreAmbient_of_isSubnormalIn L ⁅Q, L⁆ 2 hcommL
      hcommNormal.isSubnormal
      (((pCore_isPGroup (p := 2) (G := S)).map S.subtype).to_le hcommQ)
  have hidem : ⁅⁅Q, L⁆, L⁆ = ⁅Q, L⁆ := by
    simpa only [hres] using
      commutator_twoResidualAmbient_idempotent Q L
        ((pCore_isPGroup (p := 2) (G := S)).map S.subtype) hLQ
  refine ⟨?_, hMQ⟩
  calc
    ⁅L, Q⁆ = ⁅Q, L⁆ := commutator_comm L Q
    _ = ⁅⁅Q, L⁆, L⁆ := hidem.symm
    _ ≤ ⁅M, L⁆ := commutator_mono hcommM le_rfl

/-- Finite-ambient form of C.6.3(1): an `XT`-conjugate of the residual
two-core action escapes `Q=O₂(LR)`. Conjugation is `Uˣ=x⁻¹Ux`. -/
public theorem c6_3_exists_escaping_conjugate
    {G : Type*} [Group G] [Finite G]
    (L R T Λ : Subgroup G)
    (hRL : R ≤ normalizer (L : Set G))
    (hres : twoResidualAmbient L = L)
    (hQR : (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype ≤ R)
    (hU : ⁅(pCore 2 L).map L.subtype, L⁆ ≠ ⊥)
    (hRT : R ≤ T)
    (hTR : (R.subgroupOf T).Normal)
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G)) :
    let U := ⁅(pCore 2 L).map L.subtype, L⁆
    let Q := (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ T,
      ¬ U.map (MulAut.conj x⁻¹) ≤ Q := by
  let M := (pCore 2 L).map L.subtype
  let U := ⁅M, L⁆
  let Q := (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype
  have hMU : L ≤ normalizer (M : Set G) := by
    have hh := (pCore 2 L).le_normalizer_map L.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      using hh
  have hUM : U ≤ M := le_normalizer_iff_commutator_le_left.mp hMU
  have hUQ : U ≤ Q := hUM.trans (c6_3_commutator_core_bound L R hRL hres).2
  have hUR : U ≤ R := hUQ.trans hQR
  have hTR' : T ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp hTR
  exact exists_conjugate_escape_of_commutator_le L R T Λ U Q
    hU hUR hRT hTR' (c6_3_commutator_core_bound L R hRL hres).1 hno

end CFSG.Quasithin.ChapterC
