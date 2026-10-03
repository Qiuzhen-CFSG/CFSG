module
public import Stellmacher.SectionOne.OneSevenTransvectionSupportSelection
public import Mathlib.Tactic.Group

/-!
# A small fixed intersection forces normalization of a selected factor

Let M contain a canonical one-seven factor support, and let I≤M have
index at most two. Suppose T preserves that factor, fixes I pointwise,
and moves a vector of the support. Every group R preserving M and
normalizing T then normalizes the selected factor.

The support is not contained in I, so together they generate M. Since T
fixes I and preserves the support, every T-displacement in M lies in the
support. Choose a nonzero such displacement. Each R-image remains a
T-displacement in M and also lies in the conjugate factor support. Distinct
canonical supports are disjoint, so every such conjugate factor equals the
original one.

This is the normalization step leading to O²(F)=O²(E₁) and source (9.4)(5),
printed p.51/PDF p.41 of `refs/files/stellmacher-n-group.pdf`. The concrete
consumer supplies T as the induced actor closure and R as the initial/remote
core-intersection image; the factor or its normalization is not assumed for R.
-/

open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

private theorem join_eq_of_index_le_two
    {V : Type*} [Group V] [Finite V] (I S M : Subgroup V)
    (hIM : I ≤ M) (hSM : S ≤ M) (hindex : I.relIndex M ≤ 2)
    (hnot : ¬ S ≤ I) : S ⊔ I = M := by
  let K := S ⊔ I
  have hIK : I ≤ K := le_sup_right
  have hKM : K ≤ M := sup_le hSM hIM
  have hindexPos : 0 < I.relIndex K := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hindexNe : I.relIndex K ≠ 1 := by
    intro hh
    exact hnot (le_sup_left.trans (Subgroup.relIndex_eq_one.mp hh))
  have hKPos : 0 < K.relIndex M := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hmul := Subgroup.relIndex_mul_relIndex I K M hIK hKM
  have htwo : 2 ≤ I.relIndex K := by omega
  have hKone : K.relIndex M = 1 := by nlinarith
  exact le_antisymm hKM (Subgroup.relIndex_eq_one.mp hKone)

public theorem oneSevenFactor_normalized_of_small_fixed_intersection
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (hyp : Hypotheses G V) (D T R : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D)
    (M I : Subgroup V)
    (hSM : commutatorAction D V ≤ M) (hIM : I ≤ M)
    (hindex : I.relIndex M ≤ 2)
    (hTD : T ≤ Subgroup.normalizer D)
    (hRT : R ≤ Subgroup.normalizer T)
    (hRM : ∀ r ∈ R, ∀ v ∈ M, r • v ∈ M)
    (hfix : ∀ t ∈ T, ∀ v ∈ I, t • v = v)
    (hmove : ∃ t ∈ T, ∃ v ∈ commutatorAction D V, t • v ≠ v) :
    R ≤ Subgroup.normalizer D := by
  let S := commutatorAction D V
  obtain ⟨t,ht,v,hv,hmove⟩ := hmove
  have hnot : ¬ S ≤ I := fun hh => hmove (hfix t ht v (hh hv))
  have hjoin : S ⊔ I = M := join_eq_of_index_le_two I S M hIM hSM hindex hnot
  have hstable := commutatorAction_isInvariant_of_normalizing_actor (V:=V) T D hTD
  have hdifference : ∀ t ∈ T, ∀ v ∈ M, v⁻¹*(t • v) ∈ S := by
    intro a ha w hw
    rw [← hjoin] at hw
    obtain ⟨s,hs,i,hi,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hw
    have hsact : a • s ∈ S := (hstable.invariant ⟨a,ha⟩ s).mp hs
    have hdelta : s⁻¹*(a • s) ∈ S := S.mul_mem (S.inv_mem hs) hsact
    have heq : (s*i)⁻¹ * (a • (s*i)) = s⁻¹ * (a • s) := by
      rw [smul_mul',hfix a ha i hi,mul_inv_rev]
      calc
        i⁻¹ * s⁻¹ * (a • s * i) = (s⁻¹ * (a • s)) * (i⁻¹*i) := by ac_rfl
        _ = s⁻¹ * (a • s) := by rw [inv_mul_cancel,mul_one]
    exact heq ▸ hdelta
  let delta := v⁻¹*(t • v)
  have hdelta : delta ∈ S := hdifference t ht v (hSM hv)
  have hdeltaNe : delta ≠ 1 := fun hh => hmove (inv_mul_eq_one.mp hh).symm
  intro r hr
  have hdeltaImage : r • delta ∈ S := by
    have hconj : r*t*r⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hRT hr) t).mp ht
    have hvec : r • v ∈ M := hRM r hr v (hSM hv)
    have hh := hdifference (r*t*r⁻¹) hconj (r • v) hvec
    have heq : r • delta = (r • v)⁻¹ * ((r*t*r⁻¹) • (r • v)) := by
      simp only [delta,smul_mul',smul_inv',mul_smul,inv_smul_smul]
    exact heq ▸ hh
  have hconjSupport : r • delta ∈ commutatorAction (D.conjBy r) V := by
    rw [← RankOneThreeGroupAssembly.commutatorAction_conjBy D r]
    exact ⟨delta,hdelta,rfl⟩
  have hfactorEq : D.conjBy r = D := by
    by_contra hne
    have hdisj := oneSevenFactor_support_disjoint_of_ne hyp (D.conjBy r) D
      (hD.conjBy D r) hD hne
    have hzero : r • delta = 1 := hdisj.le_bot ⟨hconjSupport,hdeltaImage⟩
    exact hdeltaNe (MulAction.injective r (hzero.trans (smul_one r).symm))
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfactorEq

end Stellmacher.SectionOne
