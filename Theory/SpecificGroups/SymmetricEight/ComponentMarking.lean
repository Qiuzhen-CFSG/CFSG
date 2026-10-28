module

public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.Extension
/-!
# A compatible A₈–A₆ transposition marking

Let K ≃ A₈, let z be an involution normalizing K, and let L < K be a
component of K∩C_G(z) of order 360. The normalizer action identifies K⟨z⟩
with S₈ and z with a transposition. Conjugating that one action marks the
transposition as `(0 1)`. Perfectness makes the image of L fix both marked
points, and equality of orders identifies it with their even pointwise
stabilizer.

All three identifications use the same equivalence of the actual extension.
The component hypothesis supplies perfectness and excludes the identity
action. No graph-automorphism classification is required beyond the given
identification of K with A₈.

Source: Aschbacher–Smith, 16.3.11(3) and the setup for 16.3.12,
combined manuscript of 1 March 2004, printed p.1181 (PDF p.1198).
-/

open Subgroup Equiv Equiv.Perm Theory.GroupTheory
public noncomputable section
namespace Theory.SpecificGroups.SymmetricEight.ComponentMarking
variable {G : Type*} [Group G] {K L : Subgroup G} {z : G}

/-- One equivalence marks the involution, the alternating subgroup, and its component. -/
theorem exists_marked_equiv (e : K ≃* alternatingGroup (Fin 8))
    (hz : z ∈ normalizer (K : Set G)) (ho : orderOf z = 2) (hLK : L < K)
    (hL : IsComponentIn L (K ⊓ centralizer ({z} : Set G)))
    (hcardL : Nat.card L = 360) :
    ∃ f : (K ⊔ zpowers z : Subgroup G) ≃* Perm (Fin 8),
      f ⟨z, mem_sup_right (mem_zpowers z)⟩ = swap 0 1 ∧
      (K.subgroupOf (K ⊔ zpowers z)).map f.toMonoidHom = alternatingGroup (Fin 8) ∧
      (L.subgroupOf (K ⊔ zpowers z)).map f.toMonoidHom =
        alternatingGroup (Fin 8) ⊓
          (MulAction.stabilizer (Perm (Fin 8)) (0 : Fin 8) ⊓
           MulAction.stabilizer (Perm (Fin 8)) (1 : Fin 8)) := by
  let J := K ⊔ zpowers z
  let zJ : J := ⟨z, mem_sup_right (mem_zpowers z)⟩
  have hq := normalizerRepresentation_isSwap e hz ho hLK hL hcardL
  let E : J ≃* Perm (Fin 8) := MulEquiv.ofBijective (extensionRepresentation e hz)
    (extensionRepresentation_bijective e hz ho hq)
  have hconj : IsConj (E zJ) (swap (0 : Fin 8) 1) := by
    apply isConj_iff_cycleType_eq.mpr
    exact (isSwap_iff_cycleType.mp hq).trans
      (isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (0 : Fin 8) ≠ 1))).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  let f : J ≃* Perm (Fin 8) := E.trans (MulAut.conj c)
  have hfz : f zJ = swap 0 1 := hc
  have hKf : (K.subgroupOf J).map f.toMonoidHom = alternatingGroup (Fin 8) := by
    change (K.subgroupOf J).map ((MulAut.conj c).toMonoidHom.comp
      (extensionRepresentation e hz)) = _
    rw [← Subgroup.map_map, extensionRepresentation_larger_image]
    exact Subgroup.Normal.map_conj_eq _ c
  let P := (L.subgroupOf J).map f.toMonoidHom
  have hLJ : L ≤ J := hLK.le.trans le_sup_left
  let : IsQuasisimple L := hL.quasisimple
  let : Group.IsPerfect (L.subgroupOf J) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLJ).symm.toMonoidHom)
      (subgroupOfEquivOfLe hLJ).symm.surjective
  let : Group.IsPerfect P := Group.IsPerfect.map f.toMonoidHom
  have hPC : P ≤ centralizer ({swap (0 : Fin 8) 1} : Set (Perm (Fin 8))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hcomm : Commute x zJ := by
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp (hL.1 hx).2
    exact mem_centralizer_singleton_iff.mpr (by
      simpa only [MulEquiv.coe_toMonoidHom, hfz] using (hcomm.map f.toMonoidHom).eq)
  have hPA : P ≤ alternatingGroup (Fin 8) := by
    rw [← hKf]
    exact map_mono (fun x hx => hLK.le hx)
  have hcardP : Nat.card P = 360 := by
    calc
      Nat.card P = Nat.card (L.subgroupOf J) :=
        Nat.card_congr (f.subgroupMap (L.subgroupOf J)).symm.toEquiv
      _ = Nat.card L := Nat.card_congr (subgroupOfEquivOfLe hLJ).toEquiv
      _ = 360 := hcardL
  refine ⟨f, hfz, hKf, ?_⟩
  apply eq_of_le_of_card_ge (le_inf hPA (perfect_le_pairFixer P hPC))
  rw [card_evenPairFixer, hcardP]

end Theory.SpecificGroups.SymmetricEight.ComponentMarking
