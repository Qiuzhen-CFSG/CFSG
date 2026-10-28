module

public import CFSG.Quasithin.ChapterF.Section01.SourceCartan.Transport
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Dihedral

/-!
# The dihedral Cartan action in F.1.3(5)

In the D₁₀ alternative the Sylow two-subgroup is self-normalizing, so its
Cartan complement is trivial. Thus every automorphism fixes that complement.
The model is connected by an actual multiplicative equivalence.
Source: Aschbacher–Smith, F.1.1(c) and F.1.3(5), printed pp.259–260.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {H : Type*} [Group H] [Finite H]

/-- The order-ten model has trivial Cartan complements, hence rigidity. -/
theorem cartanQuadraticRigidity_of_dihedral_equiv (e : H ≃* DihedralGroup 5) :
    CartanQuadraticRigidity H := by
  intro T D hDN _ho hd _hs a _hao _haT _haD _hquad x hx
  have hcard : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  have hne : (T : Subgroup H) ≠ ⊥ := fun hh => by simp [hh] at hcard
  have hnorm : normalizer (T : Set H) = (T : Subgroup H) :=
    odd_dihedral_two_subgroup_normalizer 5 (by decide) e
      (T : Subgroup H) T.isPGroup' hne
  have hx1 : x = 1 := disjoint_iff_inf_le.mp hd ⟨hnorm ▸ hDN hx,hx⟩
  simp only [hx1, map_one]
end CFSG.Quasithin.ChapterF.Source
