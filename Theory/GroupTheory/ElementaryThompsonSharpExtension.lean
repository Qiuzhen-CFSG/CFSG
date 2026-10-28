module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Rank
public import Stellmacher.ElementaryAbelianMaxJ
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Sharp fixed-space bounds on an elementary extension

Let V ≤ W ≤ S be elementary binary subgroups. If the kernel on V of a
maximum elementary subgroup A of S fixes W, the sharp fixed-space bound
on V forces W = C_W(A)V. Counting W C_A(V), whose order cannot exceed
|A|, gives the opposite inequality, and equality of relative indices gives
the supplement. Thus J(S) acts trivially on W/V. If K = [K,J(S)] inside
an overgroup preserving W and V, then K also acts trivially on W/V.

Source application: the FF step in Aschbacher--Smith, 10.2.8, printed p.749;
the maximum elementary counting argument is B.2.4, pp.75--76.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A sharp rank bound and a common action kernel force the fixed supplement. -/
theorem maxElementary_fixed_supplement (S V W A : Subgroup G)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hVW : V ≤ W) (hWS : W ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hkernel : A ⊓ centralizer (V : Set G) ≤ centralizer (W : Set G))
    (hsharp : (centralizer (V : Set G)).relIndex A ≤
      (centralizer (A : Set G)).relIndex V) :
    W = (W ⊓ centralizer (A : Set G)) ⊔ V := by
  let C := A ⊓ centralizer (V : Set G)
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ A from inf_le_left)
  have hE : IsElementaryAbelian 2 (W ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hkernel
  have hmax := hA.2.2 (W ⊔ C) (sup_le hWS (inf_le_left.trans hA.1)) hE
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes W C
    (hkernel.trans (Subgroup.centralizer_le_normalizer _))
  have hI : W ⊓ C ≤ W ⊓ centralizer (A : Set G) :=
    le_inf inf_le_left ((inf_le_right.trans inf_le_left).trans A.le_centralizer)
  have hIc := Nat.card_le_card_of_injective _ (inclusion_injective hI)
  have hAc : Nat.card C * (centralizer (V : Set G)).relIndex A = Nat.card A := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) C A bot_le inf_le_left
    simpa only [relIndex_bot_left, inf_relIndex_left, C] using h
  have hWc : Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) *
      (centralizer (A : Set G)).relIndex W = Nat.card W := by
    simpa only [relIndex_bot_left, inf_relIndex_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (W ⊓ centralizer (A : Set G)) W bot_le inf_le_left
  have hineq : Nat.card W ≤ Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) *
      (centralizer (V : Set G)).relIndex A := by
    have hh := calc
      Nat.card W * Nat.card C = Nat.card (W ⊓ C : Subgroup G) * Nat.card (W ⊔ C : Subgroup G) := hprod
      _ ≤ Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) * Nat.card A := Nat.mul_le_mul hIc hmax
      _ = (Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) *
          (centralizer (V : Set G)).relIndex A) * Nat.card C := by rw [←hAc]; ac_rfl
    exact (mul_le_mul_iff_left₀ (Nat.card_pos (α := C))).mp hh
  have hi : (centralizer (A : Set G)).relIndex W ≤ (centralizer (A : Set G)).relIndex V := by
    rw [←hWc] at hineq
    exact ((mul_le_mul_iff_right₀ (Nat.card_pos (α := (W ⊓ centralizer (A : Set G) : Subgroup G)))).mp hineq).trans hsharp
  apply (Representation.BinaryInternalFixedSpaceCodimension.rank_eq_iff_supplement V W _ hVW).mp
  rw [Representation.BinaryInternalFixedSpaceCodimension.rank_eq_log_index,
    Representation.BinaryInternalFixedSpaceCodimension.rank_eq_log_index]
  exact congrArg (Nat.log 2) (le_antisymm
    (relIndex_le_of_le_right hVW ((centralizer (A : Set G)).subgroupOf W).index_ne_zero_of_finite) hi)

omit [Finite G] in
/-- A fixed supplement makes the quotient action trivial. -/
theorem commutator_le_of_fixed_supplement (W V A : Subgroup G)
    (hWV : W ≤ normalizer (V : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (hspan : W = (W ⊓ centralizer (A : Set G)) ⊔ V) : ⁅W,A⁆ ≤ V := by
  have hle : W ≤ commutatorPreimage W A V := by
    conv_lhs => rw [hspan]
    refine sup_le (le_commutatorPreimage inf_le_left ?_)
      (le_commutatorPreimage (hspan ▸ le_sup_right) ?_)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
    · exact le_normalizer_iff_commutator_le_left.mp hAV
  exact (commutator_mono hle le_rfl).trans (commutator_commutatorPreimage_le W A V hWV)

omit [Finite G] in
/-- Fixed supplements for all maximum elementary subgroups control the Thompson action. -/
theorem thompson_commutator_le_of_max_fixed_supplements (S V W : Subgroup G)
    (hSV : S ≤ normalizer (V : Set G)) (hWV : W ≤ normalizer (V : Set G))
    (hspan : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      W = (W ⊓ centralizer (A : Set G)) ⊔ V) :
    ⁅W,elementaryAbelianMaxJ S⁆ ≤ V := by
  have hJ : elementaryAbelianMaxJ S ≤ commutatorPreimage S W V := by
    apply sSup_le
    intro A hA
    apply le_commutatorPreimage hA.1
    rw [commutator_comm]
    exact commutator_le_of_fixed_supplement W V A hWV (hA.1.trans hSV) (hspan A hA)
  rw [commutator_comm]
  exact (commutator_mono hJ le_rfl).trans (commutator_commutatorPreimage_le S W V hSV)

omit [Finite G] in
/-- Thompson commutator generation extends trivial quotient action to the actor. -/
theorem actor_commutator_le_of_thompson_generation (H K S V W : Subgroup G)
    (hKV : K ≤ H) (hSV : S ≤ H)
    (hHV : H ≤ normalizer (V : Set G)) (hHW : H ≤ normalizer (W : Set G))
    (hgen : K = ⁅K,elementaryAbelianMaxJ S⁆)
    (hJ : ⁅W,elementaryAbelianMaxJ S⁆ ≤ V) : ⁅W,K⁆ ≤ V := by
  let C := commutatorPreimage H W V
  have hNC : H ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized H W V H hHV H.le_normalizer hHW hHV
  have hJC : elementaryAbelianMaxJ S ≤ C :=
    le_commutatorPreimage ((sSup_le fun _ hA => hA.1).trans hSV)
      (by rwa [commutator_comm])
  have hKC : K ≤ C := by
    conv_lhs => rw [hgen]
    exact (commutator_mono le_rfl hJC).trans
      (le_normalizer_iff_commutator_le_right.mp (hKV.trans hNC))
  rw [commutator_comm]
  exact (commutator_mono hKC le_rfl).trans (commutator_commutatorPreimage_le H W V hHV)
end Theory.GroupTheory
