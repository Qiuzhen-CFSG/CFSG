module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Constructions
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The dihedral Sylow subgroup of the cubic centralizer

These deductions take an actual internal product D × J with |D| = 3 and
J isomorphic to the four-point symmetric group. The ambient image of any
Sylow two-subgroup of J is dihedral of order eight, and has odd relative
index in D × J. When arranged inside T, it preserves V₁ = O₂(J). The
marked fixed involution belongs to it and centralizes it, so generates
its center of order two.

Two noncommuting dihedral reflections also supply an involution outside
any abelian subgroup, hence outside the marked plane. These are conditional
consequences of the symmetric factor; this module does not construct that
factor from the P/V representation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the setup
of 15.3.60 on printed p.1150.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
variable {G : Type*} [Group G]

/-- The ambient image of a Sylow two-subgroup of the symmetric factor. -/
def factorSylow (J : Subgroup G) (Q : Sylow 2 J) : Subgroup G :=
  (Q : Subgroup J).map J.subtype

theorem factorSylow_le (J : Subgroup G) (Q : Sylow 2 J) : factorSylow J Q ≤ J :=
  map_subtype_le _

theorem factorSylow_dihedral [Finite G] (J : Subgroup G) (e : J ≃* Equiv.Perm (Fin 4))
    (Q : Sylow 2 J) : Nonempty (factorSylow J Q ≃* DihedralGroup 4) := by
  let R := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨hR⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four R
  let hQ : Q ≃* R := e.subgroupMap (Q : Subgroup J)
  exact ⟨((Q : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective).symm.trans
    (hQ.trans hR)⟩

theorem card_factorSylow [Finite G] (J : Subgroup G) (e : J ≃* Equiv.Perm (Fin 4))
    (Q : Sylow 2 J) : Nat.card (factorSylow J Q) = 8 := by
  obtain ⟨hQ⟩ := factorSylow_dihedral J e Q
  rw [Nat.card_congr hQ.toEquiv, DihedralGroup.nat_card]

theorem factorSylow_isPGroup (J : Subgroup G) (Q : Sylow 2 J) :
    IsPGroup 2 (factorSylow J Q) := Q.isPGroup'.map J.subtype

/-- An internal cubic times symmetric-four product has order 72. -/
theorem card_cubic_symmetric_product (D J : Subgroup G) (hD : Nat.card D = 3)
    (e : J ≃* Equiv.Perm (Fin 4)) (hd : Disjoint D J)
    (hc : D ≤ centralizer (J : Set G)) : Nat.card (D ⊔ J : Subgroup G) = 72 := by
  obtain ⟨f, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting D J hd hc
  rw [← Nat.card_congr f.toEquiv, Nat.card_prod, hD, Nat.card_congr e.toEquiv]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The factor Sylow has odd local index in the full cubic centralizer. -/
theorem factorSylow_local_index [Finite G] (M D J : Subgroup G) (hD : Nat.card D = 3)
    (e : J ≃* Equiv.Perm (Fin 4)) (hd : Disjoint D J)
    (hc : D ≤ centralizer (J : Set G))
    (hprod : M ⊓ centralizer (D : Set G) = D ⊔ J) (Q : Sylow 2 J) :
    ¬ 2 ∣ (factorSylow J Q).relIndex (M ⊓ centralizer (D : Set G)) := by
  have hle : factorSylow J Q ≤ D ⊔ J := (factorSylow_le J Q).trans le_sup_right
  have h := (⊥ : Subgroup G).relIndex_mul_relIndex (factorSylow J Q) (D ⊔ J) bot_le hle
  rw [relIndex_bot_left, relIndex_bot_left, card_factorSylow J e Q,
    card_cubic_symmetric_product D J hD e hd hc] at h
  have hi : (factorSylow J Q).relIndex (D ⊔ J) = 9 := by omega
  rw [hprod, hi]
  decide

theorem twoCore_le_factorSylow (J : Subgroup G) (Q : Sylow 2 J) :
    Stellmacher.twoCoreAmbient J ≤ factorSylow J Q := by
  exact map_mono (pCore_isPGroup.le_sylow_of_normal Q)

private theorem normalizes_twoCore (J : Subgroup G) :
    J ≤ normalizer (Stellmacher.twoCoreAmbient J : Set G) := by
  have h := (pCore 2 J).le_normalizer_map J.subtype
  rw [normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

/-- The Sylow subgroup of the symmetric factor lies in the source plane stabilizer. -/
theorem factorSylow_le_planeStabilizer (J V₁ : Subgroup G) (T : Sylow 2 G)
    (hcore : V₁ = Stellmacher.twoCoreAmbient J) (Q : Sylow 2 J)
    (hQT : factorSylow J Q ≤ (T : Subgroup G)) :
    factorSylow J Q ≤ planeStabilizer T V₁ := by
  apply le_inf hQT
  rw [hcore]
  exact (factorSylow_le J Q).trans (normalizes_twoCore J)

private theorem dihedral_center_card : Nat.card (center (DihedralGroup 4)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The source fixed vector generates the center of this dihedral Sylow subgroup. -/
theorem factorSylow_center [Finite G] (J V V₁ : Subgroup G)
    (e : J ≃* Equiv.Perm (Fin 4)) (T : Sylow 2 G)
    (hcore : V₁ = Stellmacher.twoCoreAmbient J) (Q : Sylow 2 J)
    (hQT : factorSylow J Q ≤ (T : Subgroup G)) (v : G) (hv : orderOf v = 2)
    (hmark : v ∈ fixedPlane V (planeStabilizer T V₁) ⊓ V₁) :
    (center (factorSylow J Q)).map (factorSylow J Q).subtype = zpowers v := by
  let P := factorSylow J Q
  have hvP : v ∈ P := (hcore ▸ twoCore_le_factorSylow J Q) hmark.2
  have hvC : v ∈ (center P).map P.subtype := by
    refine ⟨⟨v, hvP⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro p
    apply Subtype.ext
    exact hmark.1.2 p ((factorSylow_le_planeStabilizer J V₁ T hcore Q hQT) p.property)
  have hle := zpowers_le.mpr hvC
  apply (eq_of_le_of_card_ge hle ?_).symm
  obtain ⟨f⟩ := factorSylow_dihedral J e Q
  rw [card_map_of_injective P.subtype_injective,
    Nat.card_congr (centerCongr f).toEquiv, dihedral_center_card, Nat.card_zpowers, hv]

/-- A dihedral eight contains an involution outside any abelian ambient subgroup. -/
theorem dihedral_involution_outside_abelian (P A : Subgroup G)
    (e : P ≃* DihedralGroup 4) [IsMulCommutative A] :
    ∃ t : G, t ∈ P ∧ orderOf t = 2 ∧ t ∉ A := by
  let a : P := e.symm (.sr 0)
  let b : P := e.symm (.sr 1)
  have ha : orderOf (a : G) = 2 := by
    rw [orderOf_coe, ← e.orderOf_eq a]
    change orderOf (e (e.symm (.sr 0))) = 2
    rw [e.apply_symm_apply]
    exact DihedralGroup.orderOf_sr _
  have hb : orderOf (b : G) = 2 := by
    rw [orderOf_coe, ← e.orderOf_eq b]
    change orderOf (e (e.symm (.sr 1))) = 2
    rw [e.apply_symm_apply]
    exact DihedralGroup.orderOf_sr _
  by_cases haA : (a : G) ∈ A
  · refine ⟨b, b.property, hb, ?_⟩
    intro hbA
    have hc : a * b = b * a := Subtype.ext (congrArg (fun x : A => (x : G))
      (mul_comm (⟨a, haA⟩ : A) ⟨b, hbA⟩))
    have hf := congrArg e hc
    simp only [map_mul, a, b, e.apply_symm_apply] at hf
    exact (by decide : DihedralGroup.sr (0 : ZMod 4) * .sr 1 ≠ .sr 1 * .sr 0) hf
  · exact ⟨a, a.property, ha, haA⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
