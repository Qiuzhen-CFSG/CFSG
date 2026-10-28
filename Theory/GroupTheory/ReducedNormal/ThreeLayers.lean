module
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# A normal actor fixing three layers of a reduced module

Let U be a reduced normal elementary abelian p-subgroup. A normal actor
N with [U,N] ≤ Z, [Z,N] ≤ D and [D,N] = 1 centralizes U. Its p-residual
acts idempotently on U, so the three commutator bounds kill that residual.
The remaining action image is a normal p-subgroup of the literal reduced
centralizer quotient and is therefore trivial.

No splitting of the intermediate layers is required. The source application
compares the original action kernels in Aschbacher--Smith 14.3.25,
printed p.1001, through the central quotient of U.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Trivial action on three successive layers forces a normal actor to fix
a reduced module pointwise. The intermediate subgroups need not be normal. -/
theorem IsPReduced.centralizes_of_three_layers
    {U : Subgroup G} (hU : IsPReduced p U) (N Z D : Subgroup G) [N.Normal]
    (hUZ : ⁅U,N⁆ ≤ Z) (hZD : ⁅Z,N⁆ ≤ D) (hDN : ⁅D,N⁆ = ⊥) :
    N ≤ centralizer (U : Set G) := by
  let := hU.normal
  let := hU.elementary
  let R := (pResidual p N).map N.subtype
  have hRN : R ≤ N := map_subtype_le _
  have hi := commutator_isPPerfect_idempotent R U
    (isPPerfect_embedded_pResidual p N) (IsElementaryAbelian.isPGroup p U)
    le_normalizer_of_normal
  have hRC : R ≤ centralizer (U : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer,commutator_comm]
    apply le_bot_iff.mp
    rw [←hi]
    conv_lhs => lhs; rw [←hi]
    exact (commutator_mono
      ((commutator_mono ((commutator_mono le_rfl hRN).trans hUZ) hRN).trans hZD)
      hRN).trans hDN.le
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  let f := q.subgroupMap N
  have hRker : pResidual p N ≤ f.ker := by
    intro n hn
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (n : G)).mpr (hRC (mem_map_of_mem N.subtype hn))
  let fbar : (N ⧸ pResidual p N) →* N.map q := QuotientGroup.lift _ f hRker
  have hsurj : Function.Surjective fbar := by
    intro x
    obtain ⟨n,rfl⟩ := q.subgroupMap_surjective N x
    exact ⟨QuotientGroup.mk' _ n,rfl⟩
  have hp : IsPGroup p (N.map q) := (isPGroup_quotient_pResidual p).of_surjective fbar hsurj
  have hcore : N.map q ≤ pCore p (G ⧸ C) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective C),hp⟩
  rw [hU.quotient_pCore_eq_bot] at hcore
  intro n hn
  exact (QuotientGroup.eq_one_iff n).mp (hcore (mem_map_of_mem q hn))
end Theory.GroupTheory
