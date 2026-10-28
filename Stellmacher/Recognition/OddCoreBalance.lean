module

public import Stellmacher.MainDefs
public import FeitThompson.PCore.CentralizerControl
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Odd-core balance for commuting involution centralizers

For commuting involutions s and t in a finite N₂ group, the ambient image of
O₂′(C_G(s)), intersected with C_G(t), lies in the ambient image of O₂′(C_G(t)).
This is the balance condition needed for the odd-core signalizer argument;
no rank, simplicity, or additional local hypothesis is imposed.

Set L = C_G(t). The N₂ condition makes L solvable. Since s lies in L, the
centralizer C = C_L(⟨s⟩) maps injectively to C_G(s) by the actual subgroup
inclusions. Pulling O₂′(C_G(s)) back along this map gives a normal odd subgroup
of C, hence a subgroup of O₂′(C). Solvable centralizer control for the cyclic
two-subgroup ⟨s⟩ of L then maps O₂′(C) into O₂′(L). Every element in the
stated ambient intersection lifts to this pullback.

This is an elementary consequence of the N₂ condition from Stellmacher's
introduction, `refs/latex/stellmacher-n-group.tex`, and the solvable
centralizer-control theorem formalized in
`FeitThompson/PCore/CentralizerControl.lean`, Proposition 1.15(b). It proves
balance only; global signalizer completion remains a separate step.
-/

namespace Stellmacher.Recognition

/-- The odd cores of commuting involution centralizers satisfy ambient balance. -/
public theorem involution_oddCore_balance
    {G : Type*} [Group G] [Finite G] {s t : G}
    (hN : IsNTwoGroup G) (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hst : Commute s t) :
    (pPrimeCore 2 (Subgroup.centralizer ({s} : Set G))).map
        (Subgroup.centralizer ({s} : Set G)).subtype ⊓
        Subgroup.centralizer ({t} : Set G) ≤
      (pPrimeCore 2 (Subgroup.centralizer ({t} : Set G))).map
        (Subgroup.centralizer ({t} : Set G)).subtype := by
  let Cs := Subgroup.centralizer ({s} : Set G)
  let L := Subgroup.centralizer ({t} : Set G)
  have hLsolv : Group.IsSolvable L := by
    by_contra hnot
    obtain ⟨U, hU, hUnot⟩ :=
      Theory.GroupTheory.exists_nonsolvable_twoLocal_of_involution_centralizer ht hnot
    exact hUnot (hN U hU)
  have hsL : s ∈ L := Subgroup.mem_centralizer_singleton_iff.mpr hst.eq
  let a : L := ⟨s, hsL⟩
  have ha : orderOf a = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hs
  let Q : Subgroup L := Subgroup.zpowers a
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    simpa only [Q, Nat.card_zpowers, pow_one] using ha)
  let C := Subgroup.centralizer (Q : Set L)
  have hCmem (c : L) : c ∈ C ↔ c * a = a * c := by
    change c ∈ Subgroup.centralizer (Subgroup.zpowers a : Set L) ↔ _
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff]
  have hCs (c : C) : ((c : L) : G) ∈ Cs := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg (fun x : L => (x : G)) ((hCmem c.val).mp c.property)
  let f : C →* Cs :=
    { toFun := fun c => ⟨c.val.val, hCs c⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Cs => (x : G)) hxy
  let R : Subgroup C := (pPrimeCore 2 Cs).comap f
  have hRnormal : R.Normal := inferInstance
  have hRcop : Nat.Coprime 2 (Nat.card R) :=
    (pPrimeCore_coprime_card (G := Cs) (p := 2)).of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ f hf)
  have hRcore : R ≤ pPrimeCore 2 C := le_sSup ⟨hRnormal, hRcop⟩
  have hcontrol : (pPrimeCore 2 C).map C.subtype ≤ pPrimeCore 2 L :=
    pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable hLsolv 2 Q hQ
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx.1
  have huL : (u : G) ∈ L := hx.2
  let uL : L := ⟨u, huL⟩
  have huC : uL ∈ C := by
    apply (hCmem uL).mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp u.property
  have huR : (⟨uL, huC⟩ : C) ∈ R := hu
  have huCore : uL ∈ pPrimeCore 2 L :=
    hcontrol ⟨⟨uL, huC⟩, hRcore huR, rfl⟩
  exact ⟨uL, huCore, rfl⟩

end Stellmacher.Recognition
