module
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Transfer

/-!
# Normal abelian Sylow subgroups in groups with trivial prime-complement core

A normal abelian Sylow `p`-subgroup of a finite group with trivial `p'`-core
is its own centralizer. This is a reusable final step after establishing
normality of a homocyclic Sylow subgroup, as required by the exceptional
case of ABG II.3 Proposition 4 (article page 28).

The centralizer is normal and contains the given Sylow subgroup as a central
Sylow subgroup. Its characteristic `p'`-core maps to a normal `p'`-subgroup
of the ambient group, so is trivial. Burnside's transfer theorem gives a
normal `p`-complement in the centralizer; that complement lies in its trivial
`p'`-core. Transfer is therefore injective into the Sylow subgroup, making
the centralizer a `p`-group. Sylow maximality gives the claimed equality.
-/

open Subgroup
open scoped IsMulCommutative

namespace Sylow

public theorem centralizer_eq_self_of_normal_of_pPrimeCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) [(S : Subgroup G).Normal] [IsMulCommutative S]
    (hcore : pPrimeCore p G = ⊥) : centralizer (S : Set G) = S := by
  let C : Subgroup G := centralizer (S : Set G)
  let : C.Normal := Subgroup.normal_centralizer
  have hSC : (S : Subgroup G) ≤ C := by
    intro s hs
    rw [mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (mul_comm (⟨t, ht⟩ : S) ⟨s, hs⟩)
  let P : Sylow p C := S.subtype hSC
  have hPC : normalizer (P : Set C) ≤ centralizer (P : Set C) := by
    intro c _
    rw [mem_centralizer_iff]
    intro s hs
    apply Subtype.ext
    exact (mem_centralizer_iff.mp c.property) s.val hs
  have hmap : (pPrimeCore p C).map C.subtype = ⊥ :=
    pPrimeCore_eq_bot_iff.mp hcore _ inferInstance
      (Nat.Coprime.of_dvd_right (card_map_dvd _ C.subtype) pPrimeCore_coprime_card)
  have hcoreC : pPrimeCore p C = ⊥ :=
    map_injective (f := C.subtype) Subtype.val_injective
      (by simpa only [Subgroup.map_bot] using hmap)
  let f := MonoidHom.transferSylow P hPC
  have hfker : f.ker = ⊥ := by
    apply bot_unique
    rw [← hcoreC]
    exact le_sSup ⟨inferInstance,
      (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
        (MonoidHom.not_dvd_card_ker_transferSylow P hPC)⟩
  have hCp : IsPGroup p C := P.isPGroup'.of_injective f
    ((MonoidHom.ker_eq_bot_iff f).mp hfker)
  exact S.is_maximal' hCp hSC

end Sylow
