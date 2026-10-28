module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Inputs
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.FieldFixedResidual

/-!
# Recognizing the symplectic field exception

The actual component of a half-Frobenius fixed group is the embedded derived
symplectic group over the fixed field. If that component is A₆, the fixed field
must have order two: for every larger binary field the symplectic group is
perfect and its order exceeds 360. Thus the ambient field has order four.
The supplied intertwining equivalence is retained, identifying the specified
involution itself with the first Frobenius representative.

This proves the field branch, conditional only on its compatible conjugator.
It does not classify arbitrary symplectic automorphisms.

Source: Aschbacher–Smith, 16.1.4(4), printed p.1171; E.6.23, printed p.254.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- An actual A₆ component forces the half-field degree to be one. -/
private theorem field_degree_one {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (2 * n)) (S : Subgroup (Sp F))
    (hS : IsComponentIn S (representative (F := F) n).fixedSubgroup)
    (hSix : Nonempty (S ≃* alternatingGroup (Fin 6))) : n = 1 := by
  obtain ⟨e⟩ := hSix
  have hs := FieldComponent.component_eq_embedded hn hF S hS
  let K := halfField (F := F) n
  let j := coefficientInclusion K
  let ed : commutator (Sp K) ≃* S :=
    ((commutator (Sp K)).equivMapOfInjective j
      (coefficientInclusion_injective K)).trans (MulEquiv.subgroupCongr hs.symm)
  have hd : Nat.card (commutator (Sp K)) = 360 :=
    (Nat.card_congr (ed.trans e).toEquiv).trans
      alternatingGroup.SixSubgroupObstructions.card_six
  by_contra hne
  have hn2 : 2 ≤ n := by omega
  have hK : Nat.card K = 2 ^ n := card_halfField hn hF
  have hfour : 4 ≤ Nat.card K := by
    rw [hK]
    exact Nat.pow_le_pow_right (show 1 ≤ 2 by omega) hn2
  let := perfect_of_card_gt_two (by omega : 2 < Nat.card K)
  have hfull : Nat.card (Sp K) = 360 := by
    rw [Group.IsPerfect.commutator_eq_top, Nat.card_congr Subgroup.topEquiv.toEquiv] at hd
    exact hd
  have hbig : 979200 ≤ Nat.card (Sp K) := by
    rw [card_sp]
    calc
      979200 = 4 ^ 4 * (4 ^ 2 - 1) * (4 ^ 4 - 1) := by norm_num
      _ ≤ (Nat.card K) ^ 4 * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) := by
        gcongr
  omega

variable {D : Type*} [Group D]
/-- Retain the conjugator while recognizing the four-element field. -/
theorem field_recognition {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ (2 * n))
    (e : D ≃* Sp F) (a : MulAut D)
    (he : MulAut.congr e a = representative n)
    (S : Subgroup D) (hS : IsComponentIn S a.fixedSubgroup)
    (hSix : Nonempty (S ≃* alternatingGroup (Fin 6))) :
    Nat.card F = 4 ∧ MulAut.congr e a = representative 1 := by
  have hfix : a.fixedSubgroup.map e.toMonoidHom = (representative n).fixedSubgroup := by
    ext x
    rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
    rw [← e.injective.eq_iff]
    have hx := congrArg (fun b : MulAut (Sp F) => b x) he
    change e (a (e.symm x)) = representative n x at hx
    rw [hx, e.apply_symm_apply]
  have hn1 := field_degree_one hn hF (S.map e.toMonoidHom)
    (hfix ▸ hS.map e) (hSix.map (fun s => (e.subgroupMap S).symm.trans s))
  subst n
  exact ⟨by simpa using hF, he⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Classical
