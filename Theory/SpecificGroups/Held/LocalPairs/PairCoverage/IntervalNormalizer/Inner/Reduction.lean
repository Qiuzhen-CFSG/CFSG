module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.LocalSubgroups

/-!
# Separating ambient and local Held normalizer calculations

Write M for either literal ATLAS local subgroup, C for its embedded two-core,
and q for M → M/O₂(M). If an inner normalizer of U lies in M and the
normalizer of q(U) lies in q(RS), then that inner normalizer lies in RS.
The lifting step uses C ≤ S, proved by Sylow maximality inside M; it does
not assume that U is normal in Held.

A second reduction supplies C ≤ O₂(O²(RS)) from [C,R] = C and oddness of R.
The commutator first places C in the relative residual. Its normality is
then restricted from M to that residual before the two-core is used.

The actual ambient containment and quotient calculation remain separate
model obligations. These reductions assert neither of them. They support
the additional Held calculation required in the retained invariant-three
branch; the Lie-type argument in the source does not prove that calculation.

Sources: Aschbacher–Smith, printed pp.509–511 and 747–748; GLS3, Table 5.3p;
the literal ATLAS subgroup definitions in PairCoverage.LocalSubgroups.
-/

@[expose] public section

open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

/-- The two-core of the local overgroup, embedded in Held. -/
def localTwoCore (i : Bool) : Subgroup Held.He :=
  (pCore 2 (localOvergroup i)).map (localOvergroup i).subtype

/-- The intrinsic local quotient, without an assumed abstract identification. -/
abbrev LocalQuotient (i : Bool) := localOvergroup i ⧸ pCore 2 (localOvergroup i)

/-- The actual quotient homomorphism on the literal local subgroup. -/
def localQuotientMap (i : Bool) : localOvergroup i →* LocalQuotient i :=
  QuotientGroup.mk' (pCore 2 (localOvergroup i))

/-- Restrict an ambient subgroup to the local overgroup and take its image. -/
def localImage (i : Bool) (H : Subgroup Held.He) : Subgroup (LocalQuotient i) :=
  (H.subgroupOf (localOvergroup i)).map (localQuotientMap i)

theorem localTwoCore_le (i : Bool) : localTwoCore i ≤ localOvergroup i := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- Normality here is relative to the local overgroup. -/
theorem localOvergroup_le_normalizer_localTwoCore (i : Bool) :
    localOvergroup i ≤ normalizer (localTwoCore i : Set Held.He) := by
  apply le_normalizer_iff.mpr
  rintro g hg x ⟨y, hy, rfl⟩
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹,
    (pCore_normal (p := 2)).conj_mem y hy ⟨g, hg⟩, rfl⟩

/-- An ambient Sylow contained in M contains the two-core of M. -/
theorem localTwoCore_le_sylow (i : Bool) (S : Sylow 2 Held.He)
    (hS : (S : Subgroup Held.He) ≤ localOvergroup i) : localTwoCore i ≤ S := by
  rintro x ⟨y, hy, rfl⟩
  exact pCore_isPGroup.le_sylow_of_normal (S.subtype hS) hy

/-- The commutator identity supplies the lower endpoint needed by the ambient
normalizer calculation. The identity itself is not asserted here. -/
theorem localTwoCore_le_twoCore_of_commutator
    (i : Bool) (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i)
    (hodd : Nat.Coprime 2 (Nat.card R))
    (hcomm : ⁅localTwoCore i, R⁆ = localTwoCore i) :
    localTwoCore i ≤ twoCore S R := by
  have hR : R ≤ residual S R := by
    rw [residual_eq_normalClosure S R S.isPGroup' hodd]
    intro r hr
    exact ⟨⟨r, (show R ≤ R ⊔ (S : Subgroup Held.He) from le_sup_left) hr⟩,
      le_normalClosure hr, rfl⟩
  have hCK : localTwoCore i ≤ R ⊔ (S : Subgroup Held.He) :=
    (localTwoCore_le_sylow i S (le_sup_right.trans hplace)).trans le_sup_right
  have hCX : localTwoCore i ≤ residual S R := by
    rw [← hcomm]
    exact (commutator_mono le_rfl hR).trans
      (le_normalizer_iff_commutator_le_right.mp
        (hCK.trans (pairProduct_le_normalizer_residual S R)))
  have hn : (localTwoCore i |>.subgroupOf (residual S R)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hCX).mpr
      ((residual_le S R).trans (hplace.trans (localOvergroup_le_normalizer_localTwoCore i)))
  have hp : IsPGroup 2 (localTwoCore i) := pCore_isPGroup.map _
  have hc : (localTwoCore i).subgroupOf (residual S R) ≤ pCore 2 (residual S R) :=
    le_sSup ⟨hn, hp.comap_subtype⟩
  intro x hx
  exact ⟨⟨x, hCX hx⟩, hc hx, rfl⟩

private theorem normalizer_le_of_local (U K M : Subgroup Held.He) (hUM : U ≤ M)
    (hambient : normalizer (U : Set Held.He) ≤ M)
    (hlocal : normalizer (U.subgroupOf M : Set M) ≤ K.subgroupOf M) :
    normalizer (U : Set Held.He) ≤ K := by
  intro g hg
  have hgM : g ∈ M := hambient hg
  have hgn : (⟨g, hgM⟩ : M) ∈ normalizer (U.subgroupOf M : Set M) := by
    rw [← subgroupOf_normalizer_eq hUM]
    exact hg
  exact hlocal hgn

/-- Combine ambient containment with a calculation in M/O₂(M). Normalization
is tested in the quotient of M, and the conclusion is inside Held. -/
theorem normalizer_le_pairProduct_of_localQuotient
    (i : Bool) (S : Sylow 2 Held.He) (R U : Subgroup Held.He)
    (hplace : R ⊔ (S : Subgroup Held.He) ≤ localOvergroup i) (hUS : U ≤ S)
    (hambient : normalizer (U : Set Held.He) ≤ localOvergroup i)
    (hquotient : normalizer (localImage i U : Set (LocalQuotient i)) ≤
      localImage i (R ⊔ (S : Subgroup Held.He))) :
    normalizer (U : Set Held.He) ≤ R ⊔ (S : Subgroup Held.He) := by
  apply normalizer_le_of_local U _ (localOvergroup i)
    (hUS.trans (le_sup_right.trans hplace)) hambient
  have hm := (le_normalizer_map (H := U.subgroupOf (localOvergroup i))
    (localQuotientMap i)).trans hquotient
  have hker : (localQuotientMap i).ker ≤
      (R ⊔ (S : Subgroup Held.He)).subgroupOf (localOvergroup i) := by
    intro x hx
    have hxC : (x : Held.He) ∈ localTwoCore i := by
      refine ⟨x, ?_, rfl⟩
      change x ∈ pCore 2 (localOvergroup i)
      simpa only [localQuotientMap, QuotientGroup.ker_mk'] using hx
    exact (show (S : Subgroup Held.He) ≤ R ⊔ (S : Subgroup Held.He) from le_sup_right)
      (localTwoCore_le_sylow i S (le_sup_right.trans hplace) hxC)
  exact (map_le_map_iff.mp hm).trans (sup_le le_rfl hker)

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
