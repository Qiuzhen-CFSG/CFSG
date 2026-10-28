module
public import CFSG.Quasithin.Chapter14.Section02.ProperQuasisimpleSource
public import Theory.SpecificGroups.PSL3Even.InnerFixedSolvable

/-!
# Excluding the original binary linear-three inner action

The selected local component K lies in the canonical containing residual L
and centralizes the original central involution z. Thus K embeds in the
fixed subgroup of the literal conjugation action. That action has order two:
z is an involution and L lies outside its centralizer's containing group Mc.

The native binary PSL₃ calculation makes the fixed group solvable, contradicting
K's nonsolvability. Faithfulness on a perfect central quotient and its central
kernel give the same contradiction for the PSL₃(4) two-cover. The proof retains
the actual quotient by O₂(L) and the source equality Z(L)=O₂(L).

Source: Aschbacher–Smith 14.2.15, printed pp.985–986, and 1.1.5(3)(a),(b).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.Candidates.ComponentStructure
variable {G : Type*} [Group G] [Finite G]

/-- The original marked action excludes binary PSL₃, including the central
PSL₃(4) covering row of 1.1.5(3). -/
theorem source_proper_completion_linear_three_action_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    ∀ (z : G), z ∈ centralInvolutions T → orderOf z = 2 → ¬L ≤ Mc →
    ∀ (α : MulAut L), (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) →
    α ∈ (MulAut.conj (G := L)).range →
    ∀ (n : ℕ), 1 ≤ n →
      ¬ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      (IsQuasisimple L → center L = pCore 2 L →
        ¬ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ n)) := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  change ∀ z : G, z ∈ centralInvolutions T → orderOf z = 2 → ¬L ≤ Mc →
    ∀ α : MulAut L, (∀ x : L, (α x : G) = z * (x : G) * z⁻¹) →
    α ∈ (MulAut.conj (G := L)).range →
    ∀ n : ℕ, 1 ≤ n →
      ¬ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      (IsQuasisimple L → center L = pCore 2 L →
        ¬ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 (2 ^ n))
  intro z hzZ hz hout α hα hinner n hn
  have hcZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hspan : zpowers z = centralInvolutions T :=
    eq_of_le_of_card_ge (zpowers_le.mpr hzZ) (by rw [Nat.card_zpowers,hz,hcZ])
  have hCz : centralizer ({z} : Set G) ≤ Mc := by
    rw [←centralizer_closure,←zpowers_eq_closure,hspan]
    exact (show Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) from hu.symm ▸ Set.mem_singleton Mc).2
  have hαpow : α ^ 2 = 1 := by
    ext x
    change (α (α x) : G) = (x : G)
    calc
      (α (α x) : G) = MulAut.conj z (MulAut.conj z (x : G)) := by rw [hα,hα]; rfl
      _ = (MulAut.conj z ^ 2) (x : G) := rfl
      _ = (x : G) := by
        rw [←map_pow,show z ^ 2 = 1 from hz ▸ pow_orderOf_eq_one z,map_one]
        rfl
  have hαne : α ≠ 1 := by
    intro he
    apply hout
    intro x hx
    apply hCz
    rw [mem_centralizer_singleton_iff]
    have hf := hα ⟨x,hx⟩
    rw [he,MulAut.one_apply] at hf
    exact (mul_inv_eq_iff_eq_mul.mp hf.symm).symm
  have hao : orderOf α = 2 := orderOf_eq_prime hαpow hαne
  have hai : ∃ x : L, α = MulAut.conj x := by
    obtain ⟨x,hx⟩ := hinner
    exact ⟨x,hx.symm⟩
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨_,hKL,_⟩ := source_proper_completion_component hG T hempty hM hu hmany
    hcard e K S hST hK hSN hcorea hs
  have hKC : K ≤ centralizer ({z} : Set G) :=
    ((le_sup_left.trans_eq hgen).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hzZ))
  have hnot : ¬Group.IsSolvable α.fixedSubgroup := by
    intro hsol
    let := hsol
    let f : K →* α.fixedSubgroup := (inclusion hKL).codRestrict _ (by
      intro x
      rw [MulAut.mem_fixedSubgroup]
      apply Subtype.ext
      rw [hα]
      change z * (x : G) * z⁻¹ = (x : G)
      have hc := mem_centralizer_singleton_iff.mp (hKC x.property)
      rw [←hc,mul_inv_cancel_right])
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun v : α.fixedSubgroup => ((v : L) : G)) h
    exact Chapter1.mem_L_not_isSolvable hK
      (Group.isSolvable_of_isSolvable_injective (f := f) hf)
  constructor
  · rintro ⟨F,_,_,hF,⟨d⟩⟩
    exact hnot (Matrix.PSL3Even.inner_fixed_solvable F hn hF α hao hai d)
  · intro hq hcenter hmodel
    let := hq
    obtain ⟨F,_,_,hF,⟨d⟩⟩ := hmodel
    let c := (QuotientGroup.quotientMulEquivOfEq hcenter).trans d
    exact hnot (Matrix.PSL3Even.central_cover_inner_fixed_solvable F hn hF α hao hai c)

end CFSG.Quasithin.Chapter14.Section02
