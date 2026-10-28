module

public import CFSG.Quasithin.MainConverse.ExceptionalLocal.Triality.OddRankReduction
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.Residual

/-!
# The inner triality rank reduction from actual parabolic data

The full parabolic modulo its local factor is cyclic. Its derived group
therefore lies in that local factor. The actual PSL₂ quotient by the local
two-core has cyclic Sylow three-subgroups, so the derived parabolic has
three-rank at most one. Containment of an involution fixed group in a
conjugate root parabolic transfers this bound to its derived fixed group.

All model geometry remains explicit: the local quotient isomorphism,
cyclic full-parabolic quotient, and fixed-group containment must be proved
for the pinned graph-field carrier. This reduction adds no claim about
components of a larger fixed subgroup.

Source: Aschbacher–Smith E.6.18, printed p.252, using F.1.12(I)(4),
pp.263–264, and 16.1.4(1), p.1171, `refs/quasithin.pdf`; GLS3 2.6.5.
-/

public section

open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.TrialityCase

/-- The derived group removes the cyclic torus contribution to odd rank. -/
theorem derived_parabolic_rank_of_local_data (P : Parameters) (a : Node)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (e : (localFactor P a ⧸ pCore 2 (localFactor P a)) ≃* PSL(2, F))
    (hcyc : IsCyclic (parabolic P a ⧸
      (localFactor P a).subgroupOf (parabolic P a))) :
    primeRank 3 (commutator (parabolic P a)) ≤ 1 := by
  let N := (localFactor P a).subgroupOf (parabolic P a)
  let := hcyc
  have hle : commutator (parabolic P a) ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp inferInstance
  have h := primeRank_le_of_injective 3 (inclusion hle) (inclusion_injective hle)
  have hr : primeRank 3 N ≤ 1 := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe (localFactor_le_parabolic P a))]
    exact MainConverse.TrialityLocal.localFactor_primeRank_le_one_of_quotient
      P a F e Nat.prime_three (by decide)
  exact h.trans hr

/-- Containment in a conjugate of an actual root parabolic suffices for the
inner branch. The fixed subgroup need not be a component of the parabolic. -/
theorem derived_fixed_rank_of_parabolic (n : ℕ) (hn : 0 < n)
    (hpar : ∀ a : Node,
      primeRank 3 (commutator (parabolic (binaryParameters n hn) a)) ≤ 1)
    (r : MulAut (BinaryCarrier n hn)) (Q : Subgroup (BinaryCarrier n hn))
    (hQ : EvenInvolutionGeometry.IsRootParabolic n hn Q) (hC : r.fixedSubgroup ≤ Q) :
    primeRank 3 (commutator r.fixedSubgroup) ≤ 1 := by
  obtain ⟨a, g, hQg⟩ := hQ
  let e : parabolic (binaryParameters n hn) a ≃* Q :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hQg.symm)
  let f : r.fixedSubgroup →* parabolic (binaryParameters n hn) a :=
    e.symm.toMonoidHom.comp (inclusion hC)
  have hf : Function.Injective f := e.symm.injective.comp (inclusion_injective hC)
  have hd : (commutator r.fixedSubgroup).map f ≤
      commutator (parabolic (binaryParameters n hn) a) := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let k : commutator r.fixedSubgroup →* commutator (parabolic (binaryParameters n hn) a) :=
    (f.comp (commutator r.fixedSubgroup).subtype).codRestrict _
      (fun x => hd (mem_map_of_mem f x.property))
  have hk : Function.Injective k := by
    intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  exact (primeRank_le_of_injective 3 k hk).trans (hpar a)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.TrialityCase
