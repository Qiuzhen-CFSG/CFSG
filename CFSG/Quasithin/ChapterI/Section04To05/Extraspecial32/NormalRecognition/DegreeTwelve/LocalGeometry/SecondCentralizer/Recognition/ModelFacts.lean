module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.ModelTypes
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The local alternating four-group and its cubic fusion

The subgroup with trivial central coordinate and even permutation is the
literal A₄ in the local C₂ × S₄. A specified three-cycle fuses its three
involutions. The centralizer of the specified double transposition is the
standard Klein four-group. These small certificates use kernel reduction.

The first-four-letters embedding into C₂ × Sₙ preserves the central mark and
FirstClass. FirstClass is also invariant under internal conjugacy.

Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemma 4.2.
-/

@[expose] public section
namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
open Subgroup Equiv Equiv.Perm
abbrev A4 := alternatingGroup (Fin 4)
def evenEmbed : A4 →* Model 4 := (1 : A4 →* Multiplicative (ZMod 2)).prod
  (alternatingGroup (Fin 4)).subtype

theorem evenEmbed_injective : Function.Injective evenEmbed := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd h)

def evenInvolution : A4 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [mem_alternatingGroup]; decide⟩
def evenCycle : A4 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [mem_alternatingGroup]; decide⟩

theorem evenInvolution_order : orderOf evenInvolution = 2 := by
  rw [orderOf_eq_prime_iff]
  decide

theorem evenCycle_order : orderOf evenCycle = 3 := by
  rw [orderOf_eq_prime_iff]
  decide

theorem even_cubic_fusion (a : A4) (ha : orderOf a = 2) :
    ∃ k : Fin 3, evenCycle ^ k.val * a * (evenCycle ^ k.val)⁻¹ = evenInvolution := by
  have h : ∀ a : A4, a ^ 2 = 1 → a ≠ 1 →
      ∃ k : Fin 3, evenCycle ^ k.val * a * (evenCycle ^ k.val)⁻¹ = evenInvolution := by
    decide +kernel
  exact h a ((orderOf_eq_prime_iff.mp ha).1) ((orderOf_eq_prime_iff.mp ha).2)

theorem even_centralizer : centralizer ({evenInvolution} : Set A4) =
    alternatingGroup.kleinFour (Fin 4) := by
  ext a
  rw [mem_centralizer_singleton_iff, ← SetLike.mem_coe,
    alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
  exact (by decide +kernel : ∀ a : A4,
    a * evenInvolution = evenInvolution * a ↔
      a ∈ ({1} ∪ {g : A4 | (g : Equiv.Perm (Fin 4)).cycleType = {2, 2}})) a

theorem even_centralizer_equiv : Nonempty
    (centralizer ({evenInvolution} : Set A4) ≃* DihedralGroup 2) := by
  have := alternatingGroup.kleinFour_isKleinFour (show Nat.card (Fin 4) = 4 by simp)
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv
    (G₁ := alternatingGroup.kleinFour (Fin 4)) (G₂ := DihedralGroup 2)
  exact ⟨(MulEquiv.subgroupCongr even_centralizer).trans e⟩

theorem evenEmbed_first : FirstClass (evenEmbed evenInvolution) := by
  refine ⟨(orderOf_injective evenEmbed evenEmbed_injective _).trans evenInvolution_order, rfl, ?_⟩
  exact mem_alternatingGroup.mp evenInvolution.property


 theorem conjugate_order {H : Type*} [Group H] {a b : H}
    (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

theorem firstClass_conj_iff {n : ℕ} {a b : Model n} (h : IsConj a b) :
    FirstClass a ↔ FirstClass b := by
  have hfst : a.1 = b.1 := (isConj_iff_eq.mp ((MonoidHom.fst _ _).map_isConj h))
  have hsign : sign a.2 = sign b.2 :=
    isConj_iff_eq.mp ((sign.comp (MonoidHom.snd _ _)).map_isConj h)
  simp only [FirstClass, conjugate_order h, hfst, hsign]

def firstFour (n : ℕ) (hn : 4 ≤ n) : Fin 4 ≃ {x : Fin n // x.val < 4} where
  toFun x := ⟨⟨x.val, lt_of_lt_of_le x.isLt hn⟩, x.isLt⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def modelInclusion (n : ℕ) (hn : 4 ≤ n) : Model 4 →* Model n :=
  (MonoidHom.id _).prodMap (extendDomainHom (firstFour n hn))

theorem modelInclusion_injective (n : ℕ) (hn : 4 ≤ n) :
    Function.Injective (modelInclusion n hn) := by
  intro a b h
  exact Prod.ext (congrArg (fun x : Model n => x.1) h)
    (extendDomainHom_injective (firstFour n hn) (congrArg (fun x : Model n => x.2) h))

theorem modelInclusion_central (n : ℕ) (hn : 4 ≤ n) :
    modelInclusion n hn (centralInvolution 4) = centralInvolution n := by
  apply Prod.ext
  · rfl
  · exact (extendDomainHom (firstFour n hn)).map_one

theorem modelInclusion_first (n : ℕ) (hn : 4 ≤ n) (a : Model 4) :
    FirstClass (modelInclusion n hn a) ↔ FirstClass a := by
  simp only [FirstClass, orderOf_injective _ (modelInclusion_injective n hn)]
  change (_ ∧ a.1 = 1 ∧ sign (a.2.extendDomain (firstFour n hn)) = 1) ↔ _
  rw [sign_extendDomain]

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer
end
