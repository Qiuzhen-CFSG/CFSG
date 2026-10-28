module
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PerfectSubgroupAutomorphismFixer
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Prime-core quotients and proper local normalizers in inner images

A central kernel in a subgroup whose prime-core quotient is centerless lies
in its prime core. Consequently the quotient model survives passage from
the literal subgroup to its inner automorphism image. For a quasisimple
ambient group, the inner group is simple and perfect, with trivial
automorphism centralizer. It cannot normalize a nontrivial two-subgroup.

Source application: Aschbacher--Smith, original 4.3.15--16, printed p.618.
The actual application is NonblockEndgameSieveGeometry.localImageData.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]

omit [Finite H] [Fact p.Prime] in
/-- A centerless prime-core quotient forces the original center into the prime core. -/
theorem center_le_pCore_of_quotient_center_eq_bot
    (hz : center (H ⧸ pCore p H) = ⊥) : center H ≤ pCore p H := by
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply mem_bot.mp
  rw [← hz]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pCore p H) y
  exact congrArg (QuotientGroup.mk' (pCore p H)) (mem_center_iff.mp hx y)

omit [Finite H] [Fact p.Prime] in
/-- The inner-action kernel of the literal subgroup is a prime group. -/
theorem innerImage_kernel_isPGroup (A : Subgroup H)
    (hz : center (A ⧸ pCore p A) = ⊥) :
    IsPGroup p ((MulAut.conj : H →* MulAut H).subgroupMap A).ker := by
  apply pCore_isPGroup.to_le
  apply le_trans _ (center_le_pCore_of_quotient_center_eq_bot hz)
  intro x hx
  have hx' : (x : H) ∈ (MulAut.conj : H →* MulAut H).ker :=
    congrArg Subtype.val hx
  rw [DoubleCoverCentralizer.conj_kernel] at hx'
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (mem_center_iff.mp hx' (y : H))

/-- Inner conjugation preserves the prime-core quotient when that quotient is centerless. -/
noncomputable def innerImageCoreEquiv (A : Subgroup H)
    (hz : center (A ⧸ pCore p A) = ⊥) :
    A ⧸ pCore p A ≃*
      (A.map (MulAut.conj : H →* MulAut H)) ⧸
        pCore p (A.map (MulAut.conj : H →* MulAut H)) :=
  (MulAut.conj.subgroupMap A).pCoreQuotientEquiv
    (MulAut.conj.subgroupMap_surjective A) (innerImage_kernel_isPGroup A hz)
end Subgroup

namespace Theory.GroupTheory
open Subgroup
variable {H : Type*} [Group H]

/-- Perfectness makes the full inner group self-centralizing in the automorphism group. -/
theorem centralizer_inner_eq_bot_of_perfect [Group.IsPerfect H] :
    centralizer (MulAut.innerSubgroup H : Set (MulAut H)) = ⊥ := by
  have he := PerfectSubgroupAutomorphismFixer.inner_centralizer_eq_fixer
    (⊤ : Subgroup H)
  change centralizer ((MulAut.conj : H →* MulAut H).range : Set (MulAut H)) = ⊥
  rw [MonoidHom.range_eq_map]
  rw [he]
  apply (eq_bot_iff_forall _).mpr
  intro a ha
  rw [mem_fixingSubgroup_iff] at ha
  ext x
  exact ha x (mem_top x)

/-- The full inner image is the actual quotient by the center. -/
noncomputable def innerEquivCentralQuotient :
    MulAut.innerSubgroup H ≃* H ⧸ center H :=
  (QuotientGroup.quotientKerEquivRange (MulAut.conj : H →* MulAut H)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel)

/-- A nontrivial two-subgroup of automorphisms is not normalized by all inner automorphisms of a finite quasisimple group. -/
theorem inner_not_le_normalizer_twoGroup [Finite H] [IsQuasisimple H]
    (R : Subgroup (MulAut H)) (hR : IsPGroup 2 R) (hne : R ≠ ⊥) :
    ¬ MulAut.innerSubgroup H ≤ normalizer (R : Set (MulAut H)) := by
  intro hn
  let K := MulAut.innerSubgroup H
  let : IsSimpleGroup (H ⧸ center H) := IsQuasisimple.simple
  let : IsSimpleGroup K := (innerEquivCentralQuotient (H := H)).isSimpleGroup
  let : Group.IsPerfect K := Group.IsPerfect.range MulAut.conj
  have hn' : (R.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hn
  have hi : R ⊓ K = ⊥ := by
    rcases hn'.eq_bot_or_eq_top with hb | ht
    · have he := congrArg (Subgroup.map K.subtype) hb
      simpa using he
    · have hKR : K ≤ R := subgroupOf_eq_top.mp ht
      let : Group.IsNilpotent K := (hR.to_le hKR).isNilpotent
      exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  have hcomm : ⁅R, K⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hi]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hn)
      (commutator_le_right R K)
  have hc : R ≤ centralizer (K : Set (MulAut H)) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  exact hne (le_bot_iff.mp (hc.trans centralizer_inner_eq_bot_of_perfect.le))
end Theory.GroupTheory

end
