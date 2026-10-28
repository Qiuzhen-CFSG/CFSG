module
public import ABG.Basic
public import ABG.ChapterII.Section1.SemidihedralEquiv
public import Theory.SpecificGroups.GL2.SemidihedralSylow
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic

/-!
# The exact hypotheses of Aschbacher–Smith I.4.2

One involution class and an actual GL₂(3) centralizer suffice to place an
ambient Sylow two-subgroup in that centralizer. Transport of the explicit
matrix Sylow construction then gives semidihedral Sylow subgroups of order
sixteen. No simplicity or ambient order is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.4.2,
printed p.416; the local matrix construction is documented in
`Theory.SpecificGroups.GL2.SemidihedralSylow`.
-/

open scoped Pointwise
namespace CFSG.Quasithin

/-- Exactly the local and fusion hypotheses of I.4.2. -/
public structure GL23InvolutionCentralizerHypotheses
    (G : Type*) [Group G] [Finite G] where
  z : G
  involution : orderOf z = 2
  involutions_conjugate : ∀ u : G, orderOf u = 2 → ∃ g : G, g * u * g⁻¹ = z
  centralizer_equiv : Nonempty (Subgroup.centralizer ({z} : Set G) ≃* ABG.GL2 3 1)

namespace GL23InvolutionCentralizerHypotheses
variable {G : Type*} [Group G] [Finite G]

/-- Conjugating the marked centralizer supplies the same actual model at every involution. -/
public theorem centralizer_equiv_of_involution (h : GL23InvolutionCentralizerHypotheses G)
    (u : G) (hu : orderOf u = 2) :
    Nonempty (Subgroup.centralizer ({u} : Set G) ≃* ABG.GL2 3 1) := by
  obtain ⟨g, hg⟩ := h.involutions_conjugate u hu
  let e := MulAut.conj g
  have he : e u = h.z := hg
  let f : Subgroup.centralizer ({u} : Set G) ≃*
      Subgroup.centralizer ({h.z} : Set G) := {
    toFun := fun a => ⟨e a, Subgroup.mem_centralizer_singleton_iff.mpr (by
      rw [← he, ← map_mul, ← map_mul]
      exact congrArg e (Subgroup.mem_centralizer_singleton_iff.mp a.property))⟩
    invFun := fun a => ⟨e.symm a, Subgroup.mem_centralizer_singleton_iff.mpr (by
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply, he] using
        Subgroup.mem_centralizer_singleton_iff.mp a.property)⟩
    left_inv := fun a => Subtype.ext (e.symm_apply_apply a)
    right_inv := fun a => Subtype.ext (e.apply_symm_apply a)
    map_mul' := fun a b => Subtype.ext (map_mul e (a : G) (b : G)) }
  exact ⟨f.trans h.centralizer_equiv.some⟩

/-- Fusion of a central Sylow involution puts a whole Sylow subgroup in C_G(z). -/
public theorem exists_sylow_le_centralizer (h : GL23InvolutionCentralizerHypotheses G) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.centralizer ({h.z} : Set G) := by
  classical
  have htwo : IsPGroup 2 (Subgroup.zpowers h.z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.involution]; norm_num)
  obtain ⟨Q, hCQ⟩ := htwo.exists_le_sylow
  have hzQ : h.z ∈ (Q : Subgroup G) := hCQ (Subgroup.mem_zpowers _)
  have hz1 : h.z ≠ 1 := by intro hz; simpa [hz] using h.involution
  let : Nontrivial Q := ⟨⟨⟨h.z, hzQ⟩, 1, fun he => hz1 (congrArg Subtype.val he)⟩⟩
  let : Nontrivial (Subgroup.center Q) := Q.isPGroup'.center_nontrivial
  have hdiv : 2 ∣ Nat.card (Subgroup.center Q) :=
    ((Q.isPGroup'.to_subgroup (Subgroup.center Q)).card_eq_or_dvd.resolve_left
      (by have := Finite.one_lt_card (α := Subgroup.center Q); omega))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 hdiv
  have htG : orderOf ((t : Q) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  obtain ⟨g, hgt⟩ := h.involutions_conjugate ((t : Q) : G) htG
  refine ⟨g • Q, ?_⟩
  intro x hx
  rw [Sylow.coe_subgroup_smul] at hx
  rcases Set.mem_smul_set.mp hx with ⟨q, hqQ, rfl⟩
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have hcomm : q * ((t : Q) : G) = ((t : Q) : G) * q :=
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp t.property) ⟨q, hqQ⟩)
  change g * q * g⁻¹ * h.z = h.z * (g * q * g⁻¹)
  rw [← hgt]
  calc
    _ = g * (q * ((t : Q) : G)) * g⁻¹ := by group
    _ = g * (((t : Q) : G) * q) * g⁻¹ := by rw [hcomm]
    _ = _ := by group

/-- Every ambient Sylow two-subgroup is semidihedral of order sixteen. -/
public theorem sylow_structure (h : GL23InvolutionCentralizerHypotheses G)
    (S : Sylow 2 G) : Stellmacher.IsSemidihedralGroup S ∧ Nat.card S = 16 := by
  classical
  obtain ⟨Q, hQC⟩ := h.exists_sylow_le_centralizer
  let e := h.centralizer_equiv.some
  let P := (Q.subtype hQC).mapSurjective (f := e.toMonoidHom) e.surjective
  let eQP : Q ≃* P :=
    (Subgroup.subgroupOfEquivOfLe hQC).symm.trans
      ((Q.subtype hQC : Subgroup (Subgroup.centralizer ({h.z} : Set G))).equivMapOfInjective
        e.toMonoidHom e.injective)
  obtain ⟨R, n, hn, hc, a, b, ha, hb, hab, hgen, _⟩ :=
    Matrix.GeneralLinearGroup.exists_semidihedral_sylow (GaloisField 3 1)
      (by rw [GaloisField.card 3 1 (by decide)]; norm_num)
  have hR : Stellmacher.IsSemidihedralGroup R := ⟨n, hn, hc, a, b, ha, hb, hab, hgen⟩
  let eSR : S ≃* R := (Sylow.equiv S Q).trans (eQP.trans (Sylow.equiv P R))
  refine ⟨ABG.semidihedral_equiv eSR.symm hR, ?_⟩
  rw [Nat.card_congr eSR.toEquiv, R.card_eq_multiplicity]
  have hGL : Nat.card (ABG.GL2 3 1) = 48 := by
    let := Fintype.ofFinite (GaloisField 3 1)
    rw [Matrix.card_GL_field]
    simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by decide)]
    norm_num
  rw [hGL]
  decide +kernel

end GL23InvolutionCentralizerHypotheses
end CFSG.Quasithin

namespace CFSG.Quasithin.GL23InvolutionCentralizerHypotheses
/-- Coefficient transport to the explicit three-element matrix model. -/
public theorem centralizer_zmod_equiv {G : Type*} [Group G] [Finite G]
    (h : GL23InvolutionCentralizerHypotheses G) (u : G) (hu : orderOf u = 2) :
    Nonempty (Subgroup.centralizer ({u} : Set G) ≃* GL (Fin 2) (ZMod 3)) := by
  let eF : ABG.GL2 3 1 ≃* GL (Fin 2) (ZMod 3) :=
    Units.mapEquiv ((GaloisField.equivZmodP 3).toRingEquiv.mapMatrix (m := Fin 2)).toMulEquiv
  exact ⟨(h.centralizer_equiv_of_involution u hu).some.trans eF⟩
end CFSG.Quasithin.GL23InvolutionCentralizerHypotheses
