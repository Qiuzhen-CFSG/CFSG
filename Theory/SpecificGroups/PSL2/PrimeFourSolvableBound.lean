module
public import Theory.SpecificGroups.PSL2.PrimeFourSolvable
public import Theory.GroupTheory.Hall.TwoClosedNormal
import all Theory.SpecificGroups.PSL2.PrimeFourSolvable
/-!
# Full odd actors in solvable prime-field PSL₂ extensions

Dickson's classification bounds a solvable subgroup containing an actual A₄
by order twenty-four. The two-group outer automorphism quotient then places
any odd actor in the inner group; pulling back the solvable group through
conjugation bounds that actor by order three.

The internal import reuses the cyclic, dihedral and affine exclusions from
the companion PrimeFourSolvable proof without changing its public boundary.
The local Cartan consumer uses the full original odd intersection, with no
assumed escaping cubic. Source: Huppert II.8.27 and Aschbacher--Smith 5.1.13,
printed p.636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace Theory.PSL2.PrimeFourSolvable
local notation "A4" => alternatingGroup (Fin 4)
/-- A solvable subgroup of odd prime-field PSL₂ containing A₄ has order dividing twenty-four. -/
theorem card_dvd_twentyFour_of_alternating_four
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (H : Subgroup (PSL2MatrixGroup F)) [_root_.Group.IsSolvable H]
    (f : A4 →* H) (hi : Function.Injective f) : Nat.card H ∣ 24 := by
  have hcardF : Nat.card F = p ^ 1 := by simpa using hF
  have h4 : 4 ∣ Nat.card H := by
    have hd := card_dvd_of_injective f hi
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact (by decide : 4 ∣ 12).trans hd
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcardF H with hEl | hCy | hDi | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup p H).exists_card_eq
    exact ((ha ▸ ho.pow).not_two_dvd_nat ((by decide : 2 ∣ 4).trans h4)).elim
  · let : IsCyclic H := hCy.choose_spec.2.2
    exact (a4_not_cyclic (isCyclic_of_injective f hi)).elim
  · obtain ⟨_,_,_,⟨e⟩⟩ := hDi
    exact (no_dihedral_embedding (e.toMonoidHom.comp f) (e.injective.comp hi)).elim
  · obtain ⟨_,⟨e⟩⟩ := hA4
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · obtain ⟨_,⟨e⟩⟩ := hS4
    rw [Nat.card_congr e.toEquiv,Nat.card_perm]
    norm_num [Nat.factorial]
  · obtain ⟨_,⟨e⟩⟩ := hA5
    let : _root_.Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact False.elim <| _root_.Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (_root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,t,_,_,N,C,hN,_,hcN,hC,_,hd,hs⟩ := hAff
    let := hN
    let := hC
    exact (no_odd_cyclic_embedding N C (by rw [hcN]; exact ho.pow) hd hs f hi).elim
  · obtain ⟨a,ha,had,⟨e⟩⟩ := hPSL
    have he : a = 1 := Nat.eq_one_of_dvd_one had
    subst a
    have hc : Nat.card (GaloisField p 1) = p := by simpa using GaloisField.card p 1 (by decide)
    let : _root_.Group.IsPerfect (PSL2MatrixGroup (GaloisField p 1)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by rw [hc]; exact hp)
    exact False.elim <| _root_.Group.IsPerfect.not_isSolvable (PSL2MatrixGroup (GaloisField p 1))
      (_root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,ha,had,_⟩ := hPGL
    have := Nat.le_of_dvd (by decide : 0 < 1) had
    omega


/-- An odd group of automorphisms in a solvable group containing an inner A₄
has order at most three. -/
theorem odd_aut_card_le_three
    {X : Type*} [_root_.Group X] [Finite X]
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hp : 3 < p) (hF : Nat.card F = p)
    (e : X ≃* PSL2MatrixGroup F)
    (J E : Subgroup (MulAut X)) [_root_.Group.IsSolvable J]
    (hE : E ≤ J) (hodd : Odd (Nat.card E))
    (a : A4 →* X) (ha : Function.Injective a)
    (hJ : ∀ x, MulAut.conj (a x) ∈ J) : Nat.card E ≤ 3 := by
  obtain ⟨hz,hout⟩ := primeField_center_outer_of_equiv (Fact.out : p.Prime) ho hF e
  let i : X →* MulAut X := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hEin : E ≤ MulAut.innerSubgroup X :=
    OddHall.odd_subgroup_le _ E hout hodd
  let ec : X ≃* MulAut.innerSubgroup X := MonoidHom.ofInjective hi
  let b : E →* MulAut.innerSubgroup X := E.subtype.codRestrict _ (fun x => hEin x.property)
  let g := ec.symm.toMonoidHom.comp b
  have hg (x : E) : i (g x) = x := congrArg Subtype.val (ec.apply_symm_apply (b x))
  have hgi : Function.Injective g := by
    intro x y he
    exact Subtype.ext ((hg x).symm.trans ((congrArg i he).trans (hg y)))
  let M := J.comap i
  let : _root_.Group.IsSolvable M := _root_.Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap J) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hM (x : A4) : a x ∈ M := hJ x
  have hgm (x : E) : g x ∈ M := by
    change i (g x) ∈ J
    rw [hg]
    exact hE x.property
  have hd : Nat.card E ∣ Nat.card M := card_dvd_of_injective
    (g.codRestrict M hgm) (fun x y he => hgi (congrArg Subtype.val he))
  let eM := M.equivMapOfInjective e.toMonoidHom e.injective
  let : _root_.Group.IsSolvable (M.map e.toMonoidHom) :=
    _root_.Group.isSolvable_of_surjective (f := eM.toMonoidHom) eM.surjective
  have hc := card_dvd_twentyFour_of_alternating_four ho hp hF (M.map e.toMonoidHom)
    (eM.toMonoidHom.comp (a.codRestrict M hM))
    (eM.injective.comp (fun _ _ he => ha (congrArg Subtype.val he)))
  rw [card_map_of_injective e.injective] at hc
  have hd3 : Nat.card E ∣ 3 := (hodd.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left
    (show Nat.card E ∣ 2^3 * 3 from hd.trans hc)
  exact Nat.le_of_dvd (by decide) hd3
end Theory.PSL2.PrimeFourSolvable
