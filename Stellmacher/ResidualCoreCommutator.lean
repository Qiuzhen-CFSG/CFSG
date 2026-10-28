module
public import BenderSuzuki.External.Huppert.IV.Residual
public import Theory.PGroupCore
public import Mathlib.GroupTheory.Transfer
/-!
# A residual-perfect group's core commutator

If a finite group R equals its two-residual and R/O₂(R) has odd order,
then O₂(R)=[O₂(R),R]. The odd quotient is essential: residual perfection
alone does not exclude a central two-core.

Quotient by the displayed commutator. The image K of the two-core is a
central Sylow two-subgroup, since its index divides the given odd index.
Burnside transfer gives a map onto this Sylow subgroup with complementary
kernel. Residual perfection descends to the quotient and forces the transfer
kernel to be the whole group, since the transfer image is a two-group.
Its complementary Sylow subgroup is therefore trivial, proving the identity.

This supplies the algebraic reduction after the two triple commutators in
Stellmacher (8.4)(7), Journal of Algebra 190 (1997), printed p.39. The
source-facing consumer must supply both residual perfection and the odd
core quotient; neither is inferred from a merely solvable ambient group.
-/

namespace Stellmacher
open BenderSuzuki.External
open scoped commutatorElement
public theorem twoCore_eq_commutator_of_residual_perfect
    {R : Type*} [Group R] [Finite R]
    (hres : hktPResidual 2 R = ⊤)
    (hodd : Odd (Nat.card (R ⧸ pCore 2 R))) :
    pCore 2 R = ⁅pCore 2 R, (⊤ : Subgroup R)⁆ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCore 2 R
  let N := ⁅Q, (⊤ : Subgroup R)⁆
  let _ : N.Normal := inferInstance
  let f : R →* R ⧸ N := QuotientGroup.mk' N
  let K := Q.map f
  have hNQ : N ≤ Q := Subgroup.commutator_le_left _ _
  have hKp : IsPGroup 2 K := (pCore_isPGroup (p := 2) (G := R)).map f
  have hKind : ¬ 2 ∣ K.index := by
    have hQindex : Odd Q.index := by rw [Subgroup.index_eq_card]; exact hodd
    exact fun hd => hQindex.not_two_dvd_nat (hd.trans (Q.index_map_dvd (QuotientGroup.mk'_surjective N)))
  let T : Sylow 2 (R ⧸ N) := hKp.toSylow hKind
  have hcentral : K ≤ Subgroup.center (R ⧸ N) := by
    rintro z ⟨q,hq,rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective N y
    have hc : ⁅q,r⁆ ∈ N := Subgroup.commutator_mem_commutator hq (show r ∈ (⊤ : Subgroup R) from trivial)
    have hc' : ⁅f q,f r⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hc').symm
  have hnorm : Subgroup.normalizer (T : Set (R ⧸ N)) ≤ Subgroup.centralizer (T : Set (R ⧸ N)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_center_iff.mp (hcentral ht) x).symm
  let transfer := MonoidHom.transferSylow T hnorm
  have hquotp : IsPGroup 2 ((R ⧸ N) ⧸ transfer.ker) :=
    (T.isPGroup'.to_subgroup transfer.range).of_equiv
      (QuotientGroup.quotientKerEquivRange transfer).symm
  have hfull : transfer.ker = ⊤ := by
    apply top_unique
    rw [← hktPResidual_quotient_eq_top_of_eq_top N hres]
    exact hktPResidual_le transfer.ker inferInstance hquotp
  have hTbot : (T : Subgroup (R ⧸ N)) = ⊥ := by
    have hd := (MonoidHom.ker_transferSylow_isComplement' T hnorm).disjoint
    rw [hfull] at hd
    exact disjoint_top.mp hd.symm
  apply le_antisymm ?_ hNQ
  have hKbot : K = ⊥ := hTbot
  simpa only [f, QuotientGroup.ker_mk'] using
    (Subgroup.map_eq_bot_iff (f := f) (H := Q)).mp hKbot
end Stellmacher
