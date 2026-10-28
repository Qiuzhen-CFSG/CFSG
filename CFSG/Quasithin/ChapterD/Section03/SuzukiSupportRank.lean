module
public import Theory.Representation.Suzuki.CommutingDisplacement
public import Theory.Representation.BinaryOffender.CubicOrbitRestriction
public import CFSG.Quasithin.ChapterD.Section02.Inheritance
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# The rank of support moved by a centralizing Suzuki actor

Select a homogeneous Irr+ seed for the moved perfect support X. Its orbit
under the Suzuki group K and the starred actor A is fixed by C_A(X).
Thus the actor image on that orbit has rank at most its image in Aut(X).
A nonzero actor displacement is a faithful Suzuki module, of binary degree
at least 4(2m+1). The inherited ratio-two bound forces the image in Aut(X)
to have rank at least 2(2m+1), even when A has a large kernel on X.

The literal Chapter 10 application is SeedAnalysis.SuzukiSupportRank.
Source: Aschbacher--Smith A.1.42, D.2.7 and D.3.9,
printed pp.32,180,200--201; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterD
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The rank paid by a centralizing starred actor is already visible on its
moved perfect support, after discarding the pointwise action kernel. -/
theorem suzuki_centralizing_support_image_rank
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A X : Subgroup G) [Group.IsPerfect X]
    (hA : A ∈ ChapterD.QhatStar ρ) (hAc : A ≤ centralizer (K : Set G))
    (hXn : X ≠ ⊥) (hAX : A ≤ normalizer (X : Set G)) (hXA : ⁅X,A⁆ = X) :
    2 * (2*m+1) ≤ rank (X.normalizerMonoidHom.comp (inclusion hAX)).range := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hp : IsPGroup 2 A := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨I,hI⟩ := exists_isIrrPlusWith_of_faithful ρ hf X A hXn hAX hp
  let C := A ⊓ centralizer (X : Set G)
  let O := orbitSpan ρ (K ⊔ A) I
  have hAO : A ≤ subspaceStabilizer ρ O := le_sup_right.trans (orbitSpan_invariant ρ _ _)
  have hKO : K ≤ subspaceStabilizer ρ O := le_sup_left.trans (orbitSpan_invariant ρ _ _)
  have hIO : I ≤ O := le_orbitSpan ρ _ _
  have hAnorm : A ≤ normalizer (C : Set G) :=
    (le_inf A.le_normalizer (hAX.trans (normalizer_le_normalizer_centralizer X))).trans
      inf_normalizer_le_normalizer_inf
  have hKnorm : K ≤ normalizer (C : Set G) :=
    ((le_centralizer_iff.mp hAc).trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCO : O ≤ fixedSpace ρ C :=
    orbitSpan_le_fixedSpace_of_normalizes ρ (sup_le hKnorm hAnorm)
      ((le_orbitSpan ρ A I).trans (orbitSpan_fixed_by_two_centralizer ρ hp hI))
  have hmove : ¬ O ≤ fixedSpace ρ A := by
    intro hh
    apply hI.isIrrPlus.not_le_fixedSpace ρ
    rw [←hXA]
    exact le_fixedSpace_commutator_of_invariant ρ hI.invariant (hIO.trans hh)
  let α : A →* MulAut X := X.normalizerMonoidHom.comp (inclusion hAX)
  let β := subgroupActionHom ρ O A hAO
  have hker : α.ker ≤ β.ker := by
    intro a ha
    have hc : (a : G) ∈ centralizer (X : Set G) := by
      intro x hx
      have hh := congrArg (fun f : MulAut X => (f ⟨x,hx⟩ : G)) ha
      change (a : G) * x * (a : G)⁻¹ = x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    apply subspaceImageRepresentation_injective ρ O
    ext v
    exact hCO v.property ⟨a,a.property,hc⟩
  have hcard : Nat.card (restrictedSubgroup ρ O A) ≤ Nat.card α.range := by
    rw [←subgroupActionHom_range ρ O A hAO]
    change Nat.card β.range ≤ _
    have hd : β.ker.index ∣ α.ker.index := index_dvd_of_le hker
    rw [index_ker,index_ker] at hd
    exact Nat.le_of_dvd (Nat.card_pos) hd
  have hr : rank (restrictedSubgroup ρ O A) ≤ rank α.range :=
    Nat.log_mono_right hcard
  have hb := ChapterD.RPlusBound.restricted ρ
    (show A ∈ ChapterD.RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,ChapterD.QhatStar.mem_RPlus ρ hA⟩)
    O hAO hmove
  have hupper := (actionRatio_le_nat_iff _ hb.1 2).mp hb.2
  obtain ⟨a,ha⟩ : ∃ a : A, β a ≠ 1 := by
    by_contra! hh
    apply hmove
    intro v hv a
    have he := congrArg (fun g => subspaceImageRepresentation ρ O g ⟨v,hv⟩) (hh a)
    exact congrArg Subtype.val he
  let σ := subspaceImageRepresentation ρ O
  let τ : Representation (ZMod 2) K O := (invariantSubspace ρ K O hKO).toRepresentation
  have hτ : τ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    apply Subtype.ext
    apply hfix.le
    intro k
    exact congrArg Subtype.val (hv k)
  have hn : σ (β a) - 1 ≠ 0 := by
    intro hz
    apply ha
    apply subspaceImageRepresentation_injective ρ O
    exact (sub_eq_zero.mp hz).trans (map_one _).symm
  have hc (k : K) : (σ (β a) - 1) * τ k = τ k * (σ (β a) - 1) := by
    rw [sub_mul,mul_sub,one_mul,mul_one]
    congr 1
    ext v
    change ρ a (ρ k v) = ρ k (ρ a v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ ((hAc a.property) k k.property).symm) v
  have hl := Suzuki.commuting_operator_rank_bound τ hτ m hm e (σ (β a)-1) hn hc
  have haim : β a ∈ restrictedSubgroup ρ O A := by
    rw [←subgroupActionHom_range ρ O A hAO]
    exact ⟨a,rfl⟩
  have hu := NaturalTensor.operatorFixedCodim_le_fixedCodim σ
    (restrictedSubgroup ρ O A) haim
  change Module.finrank (ZMod 2) (σ (β a)-1).range ≤ _ at hu
  change fixedCodim σ (restrictedSubgroup ρ O A) ≤ 2 * rank (restrictedSubgroup ρ O A) at hupper
  change 2*(2*m+1) ≤ rank α.range
  omega

/-- In particular the support automorphism group must have large two-rank. -/
theorem suzuki_centralizing_support_rank
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (K : Subgroup G) (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A X : Subgroup G) [Group.IsPerfect X]
    (hA : A ∈ QhatStar ρ) (hAc : A ≤ centralizer (K : Set G))
    (hXn : X ≠ ⊥) (hAX : A ≤ normalizer (X : Set G)) (hXA : ⁅X,A⁆ = X) :
    2 * (2*m+1) ≤ primeRank 2 (MulAut X) := by
  let α := X.normalizerMonoidHom.comp (inclusion hAX)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have he : IsElementaryAbelian 2 α.range :=
    IsElementaryAbelian.of_surjective α.rangeRestrict α.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (p := 2) (MulAut X)).mp
    le_rfl α.range he
  have hr : rank α.range ≤ primeRank 2 (MulAut X) := by
    have hh := Nat.log_mono_right (b := 2) hc
    simpa only [rank,Nat.log_pow (by decide : 1 < 2)] using hh
  exact (suzuki_centralizing_support_image_rank ρ hf K hfix m hm e A X hA hAc
    hXn hAX hXA).trans hr
end CFSG.Quasithin.ChapterD
