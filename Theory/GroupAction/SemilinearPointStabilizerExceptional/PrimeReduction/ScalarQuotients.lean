module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Basic
public import Theory.GroupAction.NormalComplement

/-!
# Scalar generation and p-transfer obstructions

A homomorphism to a p-group kills every scalar if p is coprime to the
scalar order. When the scalars normally generate the actor, that homomorphism
is trivial. Thus there is no normal p-complement when p also divides the
actor's order. Burnside transfer then forces the Sylow normalizer to act
nontrivially on its Sylow subgroup.

These are the normal-generation contradictions in GLS, Volume 4,
Chapter 1, Lemma 3.9 (`refs/KGroup/GLS4/Chapter1.tex`, lines 437–449).
The separate metacyclic transfer argument must still establish that p is
coprime to the scalar order.
-/

public section

namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Field F] [MulAction X F] [FaithfulSMul X F]
variable (c : Coordinates X F)

/-- Any normal subgroup containing the scalars is the whole group. -/
theorem normal_eq_top_of_scalar_le (hgen : c.scalarClosure = ⊤)
    (N : Subgroup X) [N.Normal] (hK : c.scalarSubgroup ≤ N) : N = ⊤ := by
  have h : c.scalarClosure ≤ N := Subgroup.normalClosure_le_normal hK
  exact top_unique (hgen ▸ h)

/-- The product [X,X]K is all of X under scalar normal generation. This is
the contradiction used when the first branch of transfer makes it proper. -/
theorem commutator_sup_scalar_eq_top (hgen : c.scalarClosure = ⊤) :
    commutator X ⊔ c.scalarSubgroup = ⊤ := by
  let : (commutator X ⊔ c.scalarSubgroup).Normal :=
    Subgroup.Normal.of_commutator_le X le_sup_left
  exact c.normal_eq_top_of_scalar_le hgen _ le_sup_right

/-- A p-group image is trivial when p is coprime to the scalar order.
Normal generation propagates the element-order calculation from K to X. -/
theorem pgroup_hom_eq_one [Finite F] {p : ℕ}
    (hgen : c.scalarClosure = ⊤) (hcop : p.Coprime (Nat.card F - 1))
    {Y : Type*} [Group Y] (hY : IsPGroup p Y) (f : X →* Y) (x : X) : f x = 1 := by
  have hK : c.scalarSubgroup ≤ f.ker := by
    rintro g ⟨a, rfl⟩
    change f (c.scalar a) = 1
    obtain ⟨k, hk⟩ := hY.exists_orderOf_dvd_pow (f (c.scalar a))
    have ha : orderOf (f (c.scalar a)) ∣ Nat.card F - 1 := by
      rw [← Nat.card_units]
      exact (orderOf_map_dvd (f.comp c.scalar) a).trans (orderOf_dvd_natCard a)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) hk ha)
  have hker : f.ker = ⊤ := c.normal_eq_top_of_scalar_le hgen f.ker hK
  exact show x ∈ f.ker from hker ▸ Subgroup.mem_top x

/-- The normal p-complement prohibited in the cyclic-Sylow branch of
Lemma 3.9: it would contain K and hence all of X. -/
theorem not_hasNormalPComplement [Finite X] [Finite F] {p : ℕ}
    (hp : p.Prime) (hgen : c.scalarClosure = ⊤)
    (hcop : p.Coprime (Nat.card F - 1)) (hpX : p ∣ Nat.card X) :
    ¬ HasNormalPComplement p X := by
  rintro ⟨N, hN, hNcop, hquot⟩
  let := hN
  have hNtop : N = ⊤ := by
    apply top_unique
    intro x _
    have h := c.pgroup_hom_eq_one hgen hcop hquot (QuotientGroup.mk' N) x
    exact (QuotientGroup.eq_one_iff x).mp h
  have hc : Nat.card N = Nat.card X := by rw [hNtop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hc] at hNcop
  exact (hp.coprime_iff_not_dvd.mp hNcop) hpX

/-- Burnside transfer gives a noncentral normalizer whenever the scalar
order is prime to p and p divides the ambient order. -/
theorem sylow_normalizer_not_le_centralizer [Finite X] [Finite F] {p : ℕ}
    [Fact p.Prime] (hgen : c.scalarClosure = ⊤)
    (hcop : p.Coprime (Nat.card F - 1)) (hpX : p ∣ Nat.card X) (Q : Sylow p X) :
    ¬ Subgroup.normalizer (Q : Set X) ≤ Subgroup.centralizer (Q : Set X) := by
  intro hQ
  have hker := MonoidHom.not_dvd_card_ker_transferSylow Q hQ
  have heq : (MonoidHom.transferSylow Q hQ).ker = ⊤ := by
    apply top_unique
    intro x _
    exact c.pgroup_hom_eq_one hgen hcop Q.isPGroup' (MonoidHom.transferSylow Q hQ) x
  rw [heq] at hker
  apply hker
  simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hpX

end MulAction.SemilinearPointStabilizer.Coordinates
