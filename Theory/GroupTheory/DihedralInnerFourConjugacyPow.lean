module

public import GorensteinWalter.DihedralCore
public import GorensteinWalter.Section2.Lemma27Infra
public import Theory.GroupTheory.QuotientTrivialIntersection
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

/-!
# Fusion of four-groups in dihedral two-groups

Two Klein four subgroups inside the same index-two subgroup of a dihedral
two-group of order at least eight are conjugate in the full dihedral group.
Each four-group contains a reflection and is its centralizer. The common
index-two subgroup gives the two reflections the same parity, so a rotation
conjugates them and their centralizers.

The ambient form retains the actual subgroups and conjugation map. Only the
intersection of the containing subgroup with the dihedral subgroup needs
index two; the containing subgroup itself need not lie in the dihedral group.

Source: quasithin classification, Lemma 2.5.21, printed p.565, the order-two
core branches with prime-field PGL₂ quotients. The selected four-group
images lie in the inner index-two subgroup of a dihedral Sylow subgroup.
This fusion lifts to the selected eight-groups and contradicts the escaping
conjugate. The argument also includes the dihedral group of order eight,
where a containing index-two subgroup is itself the four-group.
-/

noncomputable section

namespace Theory.GroupTheory
open Subgroup GorensteinWalter

private theorem four_contains_reflection
    {m : ℕ}
    (U : Subgroup (DihedralGroup (2 ^ m))) (hU : IsKleinFour U) :
    ∃ j : ZMod (2 ^ m), DihedralGroup.sr j ∈ U := by
  let R : Subgroup (DihedralGroup (2 ^ m)) := zpowers (DihedralGroup.r 1)
  let : IsKleinFour U := hU
  have hn : ¬ U ≤ R := fun h =>
    IsKleinFour.not_isCyclic (Subgroup.isCyclic_of_le h)
  obtain ⟨s, hs, hsR⟩ := SetLike.not_le_iff_exists.mp hn
  cases s with
  | r i => exact (hsR (r_mem_zpowers_r_one i)).elim
  | sr i => exact ⟨i, hs⟩

private theorem four_eq_reflection_centralizer
    {m : ℕ} (hm : 2 ≤ m)
    (U : Subgroup (DihedralGroup (2 ^ m))) (hU : IsKleinFour U)
    (j : ZMod (2 ^ m)) (hj : DihedralGroup.sr j ∈ U) :
    U = centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 ^ m))) := by
  let : IsKleinFour U := hU
  let : IsMulCommutative U := IsKleinFour.isMulCommutative
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : U) (⟨DihedralGroup.sr j, hj⟩ : U))
  · rw [hU.card_four]
    exact le_of_eq (card_centralizer_sr_eq_four hm j)

private theorem dihedral_inner_four_model
    {m : ℕ} (hm : 2 ≤ m)
    (D U V : Subgroup (DihedralGroup (2 ^ m))) (hindex : D.index = 2)
    (hUD : U ≤ D) (hVD : V ≤ D) (hU : IsKleinFour U) (hV : IsKleinFour V) :
    ∃ s : DihedralGroup (2 ^ m), U.map (MulAut.conj s).toMonoidHom = V := by
  classical
  have hDnormal : D.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDnoncyclic : ¬ IsCyclic D := by
    intro hDcyclic
    let : IsCyclic D := hDcyclic
    let : IsKleinFour U := hU
    exact IsKleinFour.not_isCyclic (Subgroup.isCyclic_of_le hUD)
  obtain hDtop | ⟨j, hDj⟩ :=
    normal_noncyclic_subgroup_dihedral_two_pow (by omega : 1 ≤ m) D hDnormal hDnoncyclic
  · rw [hDtop, Subgroup.index_top] at hindex
    norm_num at hindex
  obtain ⟨i, hi⟩ := four_contains_reflection U hU
  obtain ⟨k, hk⟩ := four_contains_reflection V hV
  have hiD : DihedralGroup.sr i ∈ dihedralIndexTwoSubgroup m j := hDj ▸ hUD hi
  have hkD : DihedralGroup.sr k ∈ dihedralIndexTwoSubgroup m j := hDj ▸ hVD hk
  obtain ⟨p, hp⟩ : ∃ p : ℤ, i = j + 2 * (p : ZMod (2 ^ m)) := by
    rcases (mem_dihedralIndexTwoSubgroup_iff (by omega : 1 ≤ m) j _).mp hiD with ⟨p, hp⟩ | ⟨p, hp⟩
    · cases hp
    · exact ⟨p, DihedralGroup.sr.inj hp⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, k = j + 2 * (q : ZMod (2 ^ m)) := by
    rcases (mem_dihedralIndexTwoSubgroup_iff (by omega : 1 ≤ m) j _).mp hkD with ⟨q, hq⟩ | ⟨q, hq⟩
    · cases hq
    · exact ⟨q, DihedralGroup.sr.inj hq⟩
  let s : DihedralGroup (2 ^ m) := DihedralGroup.r ((p : ZMod (2 ^ m)) - (q : ZMod (2 ^ m)))
  have hconj : MulAut.conj s (DihedralGroup.sr i) = DihedralGroup.sr k := by
    simp only [MulAut.conj_apply, s, DihedralGroup.r_mul_sr, DihedralGroup.inv_r,
      DihedralGroup.sr_mul_r]
    congr 1
    rw [hp, hq]
    ring
  refine ⟨s, ?_⟩
  have hUeq := four_eq_reflection_centralizer hm U hU i hi
  have hVeq := four_eq_reflection_centralizer hm V hV k hk
  apply Subgroup.eq_of_le_of_card_ge
  · rw [hUeq, hVeq]
    have hm := map_centralizer_le_centralizer_image
      ({DihedralGroup.sr i} : Set (DihedralGroup (2 ^ m))) (MulAut.conj s).toMonoidHom
    simpa only [Set.image_singleton, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hconj] using hm
  · let ec := U.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
    rw [← Nat.card_congr ec.toEquiv, hU.card_four, hV.card_four]

/-- Four-groups inside a common index-two subgroup of a dihedral two-group
of order at least eight are conjugate in that dihedral group. -/
public theorem dihedral_inner_four_conjugacy_pow
    {P : Type*} [Group P] [Finite P] {m : ℕ} (hm : 2 ≤ m) (e : P ≃* DihedralGroup (2 ^ m))
    (D U V : Subgroup P) (hindex : D.index = 2)
    (hUD : U ≤ D) (hVD : V ≤ D) (hU : IsKleinFour U) (hV : IsKleinFour V) :
    ∃ s : P, U.map (MulAut.conj s).toMonoidHom = V := by
  classical
  let D' := D.map e.toMonoidHom
  let U' := U.map e.toMonoidHom
  let V' := V.map e.toMonoidHom
  let eU := U.equivMapOfInjective e.toMonoidHom e.injective
  let eV := V.equivMapOfInjective e.toMonoidHom e.injective
  have hU' : IsKleinFour U' := {
    card_four := (Nat.card_congr eU.toEquiv).symm.trans hU.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eU).symm.trans hU.exponent_two }
  have hV' : IsKleinFour V' := {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two }
  have hD'index : D'.index = 2 := (D.index_map_equiv e).trans hindex
  obtain ⟨s, hs⟩ := dihedral_inner_four_model hm D' U' V' hD'index
    (Subgroup.map_mono hUD) (Subgroup.map_mono hVD) hU' hV'
  refine ⟨e.symm s, ?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.image_conjugate]
  change U'.map (MulAut.conj (e (e.symm s))).toMonoidHom = V'
  rw [e.apply_symm_apply]
  exact hs

/-- Ambient four-groups inside `P ∩ I` are conjugate by an element of the
dihedral two-subgroup `P`, provided `[P : P ∩ I] = 2` and `|P| ≥ 8`. -/
public theorem dihedral_inner_four_ambient_conjugacy_pow
    {G : Type*} [Group G] {m : ℕ} (hm : 2 ≤ m) (P I U V : Subgroup G)
    (eP : P ≃* DihedralGroup (2 ^ m)) (hindex : (I.subgroupOf P).index = 2)
    (hUP : U ≤ P) (hVP : V ≤ P) (hUI : U ≤ I) (hVI : V ≤ I)
    (hU : IsKleinFour U) (hV : IsKleinFour V) :
    ∃ s : P, U.map (MulAut.conj (s : G)).toMonoidHom = V := by
  let : Finite P := Finite.of_equiv (DihedralGroup (2 ^ m)) eP.symm.toEquiv
  let eU := Subgroup.subgroupOfEquivOfLe hUP
  let eV := Subgroup.subgroupOfEquivOfLe hVP
  have hU' : IsKleinFour (U.subgroupOf P) := {
    card_four := (Nat.card_congr eU.toEquiv).trans hU.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eU).trans hU.exponent_two }
  have hV' : IsKleinFour (V.subgroupOf P) := {
    card_four := (Nat.card_congr eV.toEquiv).trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).trans hV.exponent_two }
  obtain ⟨s, hs⟩ := dihedral_inner_four_conjugacy_pow hm eP (I.subgroupOf P)
    (U.subgroupOf P) (V.subgroupOf P) hindex
    (fun _ h => hUI h) (fun _ h => hVI h) hU' hV'
  refine ⟨s, ?_⟩
  have hm := congrArg (fun W : Subgroup P => W.map P.subtype) hs
  have he : P.subtype.comp (MulAut.conj s).toMonoidHom =
      (MulAut.conj (s : G)).toMonoidHom.comp P.subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, he, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hUP, Subgroup.map_subgroupOf_eq_of_le hVP] at hm
  exact hm

end Theory.GroupTheory
