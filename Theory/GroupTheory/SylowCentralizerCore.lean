module

public import Theory.GroupTheory.Fitting.Centralizer

/-!
# Sylow centralizers and the prime core

For a finite solvable group with trivial prime-complement core, the
Fitting subgroup equals the prime core and lies in every Sylow subgroup.
Fitting self-centralization therefore puts the centralizer of a Sylow
subgroup in the prime core. Applied after quotienting by the odd core,
this controls central Sylow actors in the final reduction of Stellmacher
(9.3), Journal of Algebra 190 (1997), printed p.50.
-/

public theorem centralizer_sylow_le_pCore_of_pPrimeCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hsolvable : Group.IsSolvable G) (hcore : pPrimeCore p G = ⊥)
    (sylow : Sylow p G) :
    Subgroup.centralizer (sylow : Set G) ≤ pCore p G := by
  have hFitting : fittingSubgroup G = pCore p G := Fitting_eq_pcore G p hcore
  have hle : fittingSubgroup G ≤ (sylow : Subgroup G) :=
    hFitting ▸ fitting_pCore_le_sylow sylow
  exact ((Subgroup.centralizer_le hle).trans
    (centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolvable)).trans_eq hFitting

/-- An abelian Sylow subgroup of a solvable group with trivial prime-complement
core is the prime core. -/
public theorem Sylow.eq_pCore_of_isMulCommutative_of_isSolvable
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [IsMulCommutative S]
    (hsolvable : Group.IsSolvable G) (hcore : pPrimeCore p G = ⊥) :
    (S : Subgroup G) = pCore p G := by
  exact le_antisymm
    ((Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_sylow_le_pCore_of_pPrimeCore_eq_bot hsolvable hcore S))
    (fitting_pCore_le_sylow S)

/-- In the solvable case, trivial prime-complement core forces an abelian
Sylow subgroup to be normal. -/
public theorem Sylow.normal_of_isMulCommutative_of_isSolvable
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [IsMulCommutative S]
    (hsolvable : Group.IsSolvable G) (hcore : pPrimeCore p G = ⊥) :
    (S : Subgroup G).Normal := by
  rw [S.eq_pCore_of_isMulCommutative_of_isSolvable hsolvable hcore]
  infer_instance
