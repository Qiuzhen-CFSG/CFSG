module

public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.PGroupCore

/-!
# Killing the quotient two-core in Stellmacher (5.2)

Let `V` be the normal closure in `M` of a seed subgroup `Z`, and put
`C0=C_M(V)`.  Suppose `T` centralizes `Z`.  If the two-core of `M/C0` is
contained in the image of `T`, then that two-core is trivial.

Indeed, its pullback `W` lies in `C0 T`, so both factors make `W` centralize
the seed `Z`.  Since `W` is normal in `M`, the normal-closure commutator
transfer makes `W` centralize all of `V`.  Therefore `W≤C_M(V)=C0`, and its
image in the quotient is trivial.

This is the final pullback sentence proving `O₂(M/C0)=1` in Stellmacher
(5.2), Journal of Algebra 190 (1997), p. 29.  The preceding source argument
that places the quotient two-core in the indicated Sylow image is deliberately
kept as a separate obligation.
-/

namespace Stellmacher.SectionsFiveToSeven

universe u

/-- The normal-closure pullback kills a quotient two-core contained in the
image of a subgroup centralizing the normal-closure seed. -/
public theorem quotient_twoCore_eq_bot_of_le_seed_centralizer
    {M : Type u} [Group M] [Finite M]
    (Z V C0 T : Subgroup M)
    [V.Normal]
    (hV : V = Subgroup.normalClosure (Z : Set M))
    (hC0 : C0 = Subgroup.centralizer (V : Set M))
    [C0.Normal]
    (hTcentral : T ≤ Subgroup.centralizer (Z : Set M))
    (hWbar : pCore 2 (M ⧸ C0) ≤
      T.map (QuotientGroup.mk' C0)) :
    pCore 2 (M ⧸ C0) = ⊥ := by
  let q : M →* M ⧸ C0 := QuotientGroup.mk' C0
  let Wbar : Subgroup (M ⧸ C0) := pCore 2 (M ⧸ C0)
  let W : Subgroup M := Wbar.comap q
  have hWnormal : W.Normal :=
    (pCore_normal (G := M ⧸ C0) (p := 2)).comap q
  let _ : W.Normal := hWnormal
  have hWle : W ≤ T ⊔ C0 := by
    have hWcomap : W ≤ (T.map q).comap q := by
      intro x hx
      exact hWbar hx
    simpa [q, QuotientGroup.ker_mk', sup_comm] using hWcomap
  have hZV : Z ≤ V := by
    rw [hV]
    exact Subgroup.subset_normalClosure
  have hC0central : C0 ≤ Subgroup.centralizer (Z : Set M) := by
    rw [hC0]
    exact Subgroup.centralizer_le hZV
  have hWcentralZ : W ≤ Subgroup.centralizer (Z : Set M) :=
    hWle.trans (sup_le hTcentral hC0central)
  have hcommZ : ⁅W, Z⁆ ≤ (⊥ : Subgroup M) :=
    le_bot_iff.mpr
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hWcentralZ)
  have hcommV : ⁅W, V⁆ ≤ (⊥ : Subgroup M) := by
    rw [hV]
    exact Subgroup.commutator_normalClosure_le_of_normal W Z ⊥ hcommZ
  have hWcentralV : W ≤ Subgroup.centralizer (V : Set M) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    exact le_bot_iff.mp hcommV
  have hWC0 : W ≤ C0 := by simpa [hC0] using hWcentralV
  apply le_bot_iff.mp
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C0 y
  have hxW : x ∈ W := hy
  have hxker : x ∈ q.ker := by
    simpa [q, QuotientGroup.ker_mk'] using hWC0 hxW
  change q x ∈ (⊥ : Subgroup (M ⧸ C0))
  simpa using hxker

end Stellmacher.SectionsFiveToSeven
