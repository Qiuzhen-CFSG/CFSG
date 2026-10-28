module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Recognition.Space
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Recognition
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Recognition from the size of the full moving subspace

The cubic norm vanishes on cubic differences. Thus a nontrivial cubic action
remains nontrivial on the full moving space. The existing order-four natural
recognition then supplies equivariant coordinates. Its onto actor map is an
isomorphism because the literal SL2(2) is isomorphic to S3.

Only the order bound on the moving subspace remains explicit. No bound on the
whole auxiliary quotient, or preselected natural action, is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing.Transport.Natural.Kernel

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) BinaryS3.Actor W)

/-- Nontrivial two-residual action is nontrivial cubic action. -/
lemma cubic_ne_one_of_residual_moves (hm : ¬ pResidual 2 BinaryS3.Actor ≤ ρ.ker) :
    ρ BinaryS3.cubic ≠ 1 := by
  intro hc
  apply hm
  intro g hg
  rw [Equiv.Perm.twoResidual_eq_alternating] at hg
  have words : ∀ g : BinaryS3.Actor, Equiv.Perm.sign g = 1 →
      g = 1 ∨ g = BinaryS3.cubic ∨ g = BinaryS3.cubic ^ 2 := by decide +kernel
  rcases words g (Equiv.Perm.mem_alternatingGroup.mp hg) with rfl | rfl | rfl
  · exact ρ.map_one
  · exact hc
  · change ρ (BinaryS3.cubic ^ 2) = 1
    rw [map_pow, hc, one_pow]

/-- Passing to the full moving subspace retains the nontrivial cubic action. -/
lemma movedSpace_residual_moves (hm : ¬ pResidual 2 BinaryS3.Actor ≤ ρ.ker) :
    ¬ pResidual 2 BinaryS3.Actor ≤ (movedSpace ρ).toRepresentation.ker := by
  intro hk
  apply cubic_ne_one_of_residual_moves ρ hm
  have hc : BinaryS3.cubic ∈ pResidual 2 BinaryS3.Actor :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one BinaryS3.cubic_cube))
  ext w
  let v : (movedSpace ρ).toSubmodule :=
    ⟨ρ BinaryS3.cubic w - w,
      Submodule.subset_span ⟨BinaryS3.cubic, mem_top _, w, Submodule.mem_top, rfl⟩⟩
  have hf : ρ BinaryS3.cubic v.val = v.val :=
    congrArg Subtype.val (LinearMap.congr_fun (hk hc) v)
  have hz : BinaryS3.norm ρ v.val = 0 := by
    change BinaryS3.norm ρ (ρ BinaryS3.cubic w - w) = 0
    rw [map_sub, BinaryS3.norm_equivariant, BinaryS3.norm_fixed, sub_self]
  rw [BinaryS3.norm_of_fixed ρ hf] at hz
  exact sub_eq_zero.mp hz

/-- Recognize the actual moving action once its order is bounded by four.
Surjectivity between the two groups of order six upgrades the actor map to an
isomorphism, retaining the kernel when this marking is composed upstream. -/
lemma naturalMoving_of_card [Finite W]
    (hm : ¬ pResidual 2 BinaryS3.Actor ≤ ρ.ker)
    (hc : Nat.card (movedSpace ρ).toSubmodule ≤ 4) : Nonempty (NaturalMoving ρ) := by
  have hprime : primeToResidual 2 BinaryS3.Actor = ⊤ := by
    apply top_unique
    intro x _
    refine Equiv.Perm.swap_induction_on x (primeToResidual 2 _).one_mem ?_
    intro y a b _ hy
    apply (primeToResidual 2 _).mul_mem _ hy
    apply mem_primeToResidual_of_pow (n := 1)
    simp [pow_two]
  obtain ⟨π, hπ, e, he⟩ := exists_natural_sl2_of_residuals_card_le_four
    (movedSpace ρ).toRepresentation hprime (movedSpace_residual_moves ρ hm) hc
  obtain ⟨f⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  have hinj : Function.Injective (fun a => f (π a)) :=
    Finite.injective_iff_surjective.mpr (f.surjective.comp hπ)
  let m := MulEquiv.ofBijective π ⟨fun a b h => hinj (congrArg f h), hπ⟩
  exact ⟨⟨m, e, he⟩⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
