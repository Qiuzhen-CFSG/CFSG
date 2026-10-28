module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Localization.PrimeCores
public import Theory.GroupAction.BinaryAbelianPrimeRank
public import Theory.Quasithin.NormalTwoRank

/-!
# Local prime localization in E.6.20

The preceding modules prove inversion of the completed local odd closure X
and the exact identity (*) for its prime cores. Here U₀≠1 puts C_G(U₀)
inside the genuine two-local N_G(U₀), so quasithinness bounds the odd-prime
rank of Y. The actual V-action on Y is constructed by its normalizer. The
binary action bound gives |V:C_V(Y)| ≤ 4, hence corank at most two for
C_V(Y). Completeness then identifies Y with O_p(C_G(C_V(Y))). This also
handles Y=1, when C_V(Y)=V.

`localPrimeLocalization_of_completed` proves the full local conclusion
from `CompletedLocalOddClosure` and the earlier characteristic-two inputs.
Discharging these inputs and assembling E.6.20 remains with the parent.
The bound 2 < localM V is unnecessary for this local deduction once the
dimension and completion hypotheses are available. E.6.20 cites A.1.29
for the action bound, but the actual A.1.29 on printed p.27 concerns
perfect actions; the imported binary action theorem proves the bound directly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.20,
printed p.253 (PDF p.264), the paragraph following (*).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U₀ : Subgroup G}

omit [Finite G] in
/-- The actual prime closure centralizes its initial subspace. -/
theorem localPrimeClosure_le_centralizer (p : ℕ) (V U₀ : Subgroup G) :
    localPrimeClosure p V U₀ ≤ centralizer (U₀ : Set G) := by
  refine iSup_le fun W => ?_
  exact (pCoreIn_le p _).trans (Subgroup.centralizer_le W.property.1)

omit [Finite G] in
/-- V normalizes each hyperplane prime core and hence their actual closure. -/
theorem le_normalizer_localPrimeClosure [IsElementaryAbelian 2 V] (p : ℕ) :
    V ≤ normalizer (localPrimeClosure p V U₀ : Set G) := by
  apply le_trans (le_iInf fun W => ?_) (iInf_normalizer_le_normalizer_iSup _)
  exact (V.le_centralizer.trans (Subgroup.centralizer_le W.property.2.1)).trans
    (centralizer_le_normalizer_primeCentralizer p W.val)

/-- Identity (*) proves that the generated prime closure is a p-group. -/
theorem localPrimeClosure_isPGroup
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) : IsPGroup p (localPrimeClosure p V U₀) := by
  rw [localPrimeClosure_eq_pCoreIn h earlier hcpl hUV hcor p hp]
  exact isPGroup_pCoreIn p _

/-- The generated prime closure inherits the proved abelianness of X. -/
theorem localPrimeClosure_isMulCommutative
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) : IsMulCommutative (localPrimeClosure p V U₀) := by
  let _ := localOddClosure_isMulCommutative h earlier hcpl hUV hcor
  have hLX : localPrimeClosure p V U₀ ≤ localOddClosure V U₀ := by
    rw [localPrimeClosure_eq_pCoreIn h earlier hcpl hUV hcor p hp]
    exact pCoreIn_le p _
  apply IsMulCommutative.of_comm
  intro a b
  apply Subtype.ext
  exact setLike_mul_comm (hLX a.property) (hLX b.property)

/-- Corank three and dimension at least six ensure U₀ is nonidentity.
Its normalizer is a genuine two-local, so quasithinness bounds the odd-prime
rank of every subgroup of C_G(U₀), including the generated prime closure. -/
theorem localPrimeClosure_primeRank_le_two [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (hdim : 6 ≤ Module.finrank (ZMod 2) (Additive V))
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    primeRank p (localPrimeClosure p V U₀) ≤ 2 := by
  have hU : U₀ ≠ ⊥ := by
    intro he
    rw [he, corank_bot] at hcor
    omega
  have hlocal : IsTwoLocal (normalizer (U₀ : Set G)) :=
    ⟨U₀, hU, (IsElementaryAbelian.isPGroup 2 V).to_le hUV, rfl⟩
  exact (primeRank_mono p ((localPrimeClosure_le_centralizer p V U₀).trans
    (Subgroup.centralizer_le_normalizer _))).trans
    ((Theory.GroupTheory.isQuasithin_iff_twoLocal.mp h.simpleQTKE.quasithin)
      _ hlocal p Fact.out hp)

/-- The zero prime closure localizes at V itself, with no nontriviality premise. -/
theorem localPrimeLocalization_zero [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hUV : U₀ ≤ V) (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hzero : localPrimeClosure p V U₀ = ⊥) :
    ∃ U₄ : Subgroup G, U₀ ≤ U₄ ∧ U₄ ≤ V ∧ subgroupCorank V U₄ ≤ 2 ∧
      localPrimeClosure p V U₀ = primeCentralizer p U₄ := by
  refine ⟨V, hUV, le_rfl, ?_, ?_⟩
  · rw [(corank_eq_zero_iff V).mpr le_rfl]
    decide
  · rw [hzero, primeCentralizer_V_eq_bot h earlier p hp]

/-- Once the fixed space has the required corank, completeness and (*)
identify its prime centralizer exactly. -/
theorem localPrimeClosure_eq_primeCentralizer_of_fixedSpace_corank
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hsmall : subgroupCorank V (V ⊓ centralizer (localPrimeClosure p V U₀ : Set G)) ≤ 2) :
    localPrimeClosure p V U₀ =
      primeCentralizer p (V ⊓ centralizer (localPrimeClosure p V U₀ : Set G)) := by
  let _ := h.elementary
  let A := V ⊓ centralizer (localPrimeClosure p V U₀ : Set G)
  have hUA : U₀ ≤ A := le_inf hUV
    (le_centralizer_iff.mpr (localPrimeClosure_le_centralizer p V U₀))
  change subgroupCorank V A ≤ 2 at hsmall
  have hlt : U₀ < A := lt_of_corank_lt hUA (by rw [hcor]; omega)
  have hfix : localPrimeClosure p V U₀ ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  have he := localOddClosure_pCoreIn_inter_eq h earlier hcpl hUV hcor p hp hlt
    (show A ≤ V from inf_le_left)
  rw [← localPrimeClosure_eq_pCoreIn h earlier hcpl hUV hcor p hp,
    inf_eq_left.mpr hfix] at he
  exact he

/-- The faithful image of V on the abelian odd-prime closure has order at
most four. Thus its kernel C_V(Y) has corank at most two, including Y=1. -/
theorem localPrimeClosure_fixedSpace_corank_le_two [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    (hdim : 6 ≤ Module.finrank (ZMod 2) (Additive V))
    (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    subgroupCorank V (V ⊓ centralizer (localPrimeClosure p V U₀ : Set G)) ≤ 2 := by
  have hindex := relIndex_le_four_of_elementaryAbelian_two_normalizing_abelian_odd
    hp V (localPrimeClosure p V U₀) inferInstance
    (localPrimeClosure_isMulCommutative h earlier hcpl hUV hcor p hp)
    (localPrimeClosure_isPGroup h earlier hcpl hUV hcor p hp)
    (le_normalizer_localPrimeClosure p)
    (localPrimeClosure_primeRank_le_two h hUV hcor hdim p hp)
  rw [Subgroup.relIndex_eq_two_pow_quotient_finrank,
    ← subgroupCorank_eq_quotient_finrank] at hindex
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ subgroupCorank V
      (V ⊓ centralizer (localPrimeClosure p V U₀ : Set G)) ≤ 2 ^ 2 from hindex)

/-- The local conclusion used by maximal-core globalization in E.6.20.
For every corank-three U₀, choose U₄=C_V(Y), where Y is the actual local
prime closure. The earlier source inputs and odd completion remain explicit;
abelianness, identity (*), the action bound and localization are all proved. -/
theorem localPrimeLocalization_of_completed [IsElementaryAbelian 2 V]
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V)
    (hdim : 6 ≤ Module.finrank (ZMod 2) (Additive V))
    (p : ℕ) [Fact p.Prime] (hp : Odd p) : LocalPrimeLocalization p V := by
  intro U₀ hUV hcor
  have hsmall := localPrimeClosure_fixedSpace_corank_le_two h earlier hcpl hUV hcor hdim p hp
  refine ⟨V ⊓ centralizer (localPrimeClosure p V U₀ : Set G),
    le_inf hUV (le_centralizer_iff.mpr (localPrimeClosure_le_centralizer p V U₀)),
    inf_le_left, hsmall, ?_⟩
  exact localPrimeClosure_eq_primeCentralizer_of_fixedSpace_corank
    h earlier hcpl hUV hcor p hp hsmall

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
