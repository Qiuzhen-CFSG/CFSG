module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowOffenderGeometry
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# An offender on a constituent exchanged by a cubic actor

Fixed vectors on two exchanged summands inject into the stabilizer-fixed
vectors on the first summand through its diagonal. Hence the common actor
has fixed codimension at least n+m, where n is the summand dimension and
m its stabilizer codimension. The stabilizer has rank b when the actor has
rank b+1. A nonzero stabilizer-fixed vector gives m<n; thus the bound
n+m≤2(b+1) forces m≤b. Faithful restriction makes this an actual offender
in the original constituent's stabilizer image.

This is the narrow offender-extraction step needed in D.3.5(2); it avoids
invoking the stronger starred-actor classification of D.2.9(5--6).
The consumer is `MovedSylowOffenderExtraction` and its chosen-module
application `SeedAlternativesMovedSylowOffender`.
Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
D.2.9, printed pp.181--182, and D.3.5(2), pp.195--196.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) H W)

/-- Fixed vectors on an exchanged pair project injectively into the fixed
vectors of its stabilizer on either constituent. -/
theorem fixed_pair_le_stabilizer_diagonal
    (I : Submodule (ZMod 2) W) (A : Subgroup H) [IsMulCommutative A]
    {a : H} (ha : a ∈ A) (ha2 : a*a = 1) (hd : Disjoint I (I.map (ρ a))) :
    (I ⊔ I.map (ρ a)) ⊓ fixedSpace ρ A ≤
      diagonalSubspace ρ (I ⊓ fixedSpace ρ (A ⊓ subspaceStabilizer ρ I)) a := by
  rintro v ⟨hv,hf⟩
  obtain ⟨i,hi,j,hj,rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨k,hk,rfl⟩ := hj
  have he := hf ⟨a,ha⟩
  change ρ a (i + ρ a k) = i + ρ a k at he
  rw [map_add, ← Module.End.mul_apply, ← map_mul, ha2,map_one,Module.End.one_apply] at he
  have hik : i = k := by
    have hw : i-k ∈ I := I.sub_mem hi hk
    have hew : ρ a (i-k) = i-k := by
      rw [map_sub]
      calc
        ρ a i - ρ a k = (ρ a i+k) - (k+ρ a k) := by abel
        _ = i-k := by rw [he]; abel
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd (i-k) hw ⟨i-k,hw,hew⟩)
  subst k
  have hif : i ∈ fixedSpace ρ (A ⊓ subspaceStabilizer ρ I) := by
    intro b
    have hbi : ρ b i - i ∈ I := I.sub_mem ((b.property.2 i).2 hi) hi
    have hba : (b : H)*a = a*(b : H) := congrArg Subtype.val
      (mul_comm (⟨b,b.property.1⟩ : A) ⟨a,ha⟩)
    have hbv := hf ⟨b,b.property.1⟩
    change ρ b (i + ρ a i) = i + ρ a i at hbv
    rw [map_add, ← Module.End.mul_apply, ← map_mul, hba,map_mul,Module.End.mul_apply] at hbv
    have hew : ρ a (ρ b i-i) = -(ρ b i-i) := by
      rw [map_sub]
      calc
        ρ a (ρ b i)-ρ a i = (ρ b i + ρ a (ρ b i)) - (ρ b i+ρ a i) := by abel
        _ = -(ρ b i-i) := by rw [hbv]; abel
    have hmem : ρ b i-i ∈ I.map (ρ a) := by
      refine ⟨-(ρ b i-i),I.neg_mem hbi,?_⟩
      rw [map_neg,hew,neg_neg]
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hd _ hbi hmem)
  refine ⟨i,⟨hi,hif⟩,?_⟩
  change ρ a i-i = i+ρ a i
  rw [sub_eq_add_neg,ZModModule.neg_eq_self,add_comm]

/-- The swapped pair costs the constituent dimension plus the stabilizer
fixed codimension, measured against the original actor. -/
theorem swapped_pair_codim_lower_bound [FiniteDimensional (ZMod 2) W]
    (I : Submodule (ZMod 2) W) (A : Subgroup H) [IsMulCommutative A]
    {a : H} (ha : a ∈ A) (ha2 : a*a = 1) (hd : Disjoint I (I.map (ρ a))) :
    Module.finrank (ZMod 2) I +
      fixedCodim (subspaceImageRepresentation ρ I)
        (restrictedSubgroup ρ I (A ⊓ subspaceStabilizer ρ I)) ≤ fixedCodim ρ A := by
  let B := A ⊓ subspaceStabilizer ρ I
  let C := I ⊓ fixedSpace ρ B
  have hdiag : Module.finrank (ZMod 2) (diagonalSubspace ρ C a) = Module.finrank (ZMod 2) C :=
    finrank_diagonal_eq_of_disjoint ρ C a (hd.mono inf_le_left (Submodule.map_mono inf_le_left))
  have hc := Submodule.finrank_mono (fixed_pair_le_stabilizer_diagonal ρ I A ha ha2 hd)
  change _ ≤ Module.finrank (ZMod 2) (diagonalSubspace ρ C a) at hc
  rw [hdiag] at hc
  have hI := fixedCodim_add_finrank (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B)
  rw [(restrictedFixedSpaceEquiv ρ I B inf_le_right).finrank_eq] at hI
  have hdim := I.finrank_sup_add_finrank_inf_eq (I.map (ρ a))
  rw [hd.eq_bot,finrank_bot,add_zero,finrank_map_action] at hdim
  have hs := (I ⊔ I.map (ρ a)).finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
  have ht := (I ⊔ I.map (ρ a) ⊔ fixedSpace ρ A).finrank_le
  have hw := fixedCodim_add_finrank ρ A
  change fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) +
    Module.finrank (ZMod 2) C = _ at hI
  change Module.finrank (ZMod 2) I +
    fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) ≤ fixedCodim ρ A
  omega

/-- An elementary actor with exactly two translates has a stabilizer of
binary rank one less, retaining the literal subgroup intersection. -/
theorem pair_stabilizer_rank [Finite H]
    (I : Submodule (ZMod 2) W) (A : Subgroup H) (hA : IsElementaryTwo A)
    {a : H} (ha : a ∈ A) (ha2 : a*a = 1)
    (hm : I.map (ρ a) ≠ I)
    (htwo : ∀ b ∈ A, I.map (ρ b) = I ∨ I.map (ρ b) = I.map (ρ a)) :
    rank A = rank (A ⊓ subspaceStabilizer ρ I) + 1 := by
  let B := A ⊓ subspaceStabilizer ρ I
  have hi : B.relIndex A = 2 := by
    apply relIndex_eq_two_iff_exists_notMem_and'.mpr
    refine ⟨a,ha,fun hh => hm ((subspace_map_eq_iff ρ I a).mpr hh.2),?_⟩
    intro b hb
    rcases htwo b hb with he | he
    · exact Or.inr ⟨hb,(subspace_map_eq_iff ρ I b).mp he⟩
    · refine Or.inl ⟨A.mul_mem ha hb,(subspace_map_eq_iff ρ I (a*b)).mp ?_⟩
      rw [subspace_map_mul,he,←subspace_map_mul,ha2,map_one,Module.End.one_eq_id,Submodule.map_id]
  have hc := (B.subgroupOf A).card_mul_index
  change Nat.card (B.subgroupOf A) * B.relIndex A = Nat.card A at hc
  rw [Nat.card_congr (subgroupOfEquivOfLe (show B ≤ A from inf_le_left)).toEquiv,hi] at hc
  let : IsElementaryAbelian 2 A := hA.2
  have hp : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).of_injective
    (inclusion (show B ≤ A from inf_le_left)) (inclusion_injective _)
  obtain ⟨b,hb⟩ := hp.exists_card_eq
  change Nat.log 2 (Nat.card A) = Nat.log 2 (Nat.card B) + 1
  rw [←hc,hb,←pow_succ,Nat.log_pow (by decide : 1 < 2),Nat.log_pow (by decide : 1 < 2)]

/-- The stabilizer of a swapped pair is an actual offender on the original
constituent. This only uses the common two-rank bound and faithful restriction;
it does not require the full D.2.9(5--6) classification. -/
theorem pair_stabilizer_isOffender [Finite H] [FiniteDimensional (ZMod 2) W]
    (I : Submodule (ZMod 2) W) (hI : I ≠ ⊥)
    (A : Subgroup H) (hA : IsElementaryTwo A)
    {a : H} (ha : a ∈ A) (ha2 : a*a = 1) (hd : Disjoint I (I.map (ρ a)))
    (hm : I.map (ρ a) ≠ I)
    (htwo : ∀ b ∈ A, I.map (ρ b) = I ∨ I.map (ρ b) = I.map (ρ a))
    (hB : A ⊓ subspaceStabilizer ρ I ≠ ⊥)
    (hk : subspaceKernel ρ I (A ⊓ subspaceStabilizer ρ I) = ⊥)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    IsOffender (subspaceImageRepresentation ρ I)
      (restrictedSubgroup ρ I (A ⊓ subspaceStabilizer ρ I)) := by
  let B := A ⊓ subspaceStabilizer ρ I
  have he := hA.of_le (show B ≤ A from inf_le_left) hB
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 B := he.2
  have hp := IsElementaryAbelian.isPGroup 2 B
  have hn : ¬ I ≤ fixedSpace ρ B := by
    intro hn
    apply hB
    apply bot_unique
    intro b hb
    exact hk.le ⟨hb,fun v hv => hn hv ⟨b,hb⟩⟩
  refine ⟨he.restrictedSubgroup ρ I inf_le_right hn,?_⟩
  have hr := pair_stabilizer_rank ρ I A hA ha ha2 hm htwo
  have hrB := rank_subspaceKernel_add_image ρ I B inf_le_right hp
  rw [hk,Representation.BinaryOffender.rank_bot,zero_add] at hrB
  rw [hrB]
  have hcodim := swapped_pair_codim_lower_bound ρ I A ha ha2 hd
  have hfixed := fixedCodim_add_finrank (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B)
  rw [(restrictedFixedSpaceEquiv ρ I B inf_le_right).finrank_eq] at hfixed
  obtain ⟨v,hv,hv0,hvf⟩ := PermutedSupports.exists_nonzero_fixed ρ B hp I hI inf_le_right
  have hC : I ⊓ fixedSpace ρ B ≠ ⊥ := by
    intro he
    exact hv0 (he.le ⟨hv,hvf⟩)
  have hpos : 0 < Module.finrank (ZMod 2) (I ⊓ fixedSpace ρ B : Submodule (ZMod 2) W) := by
    exact Nat.pos_of_ne_zero (fun hz => hC (Submodule.finrank_eq_zero.mp hz))
  change rank A = rank B + 1 at hr
  change Module.finrank (ZMod 2) I + fixedCodim (subspaceImageRepresentation ρ I)
    (restrictedSubgroup ρ I B) ≤ fixedCodim ρ A at hcodim
  change fixedCodim (subspaceImageRepresentation ρ I) (restrictedSubgroup ρ I B) ≤ rank B
  omega

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
