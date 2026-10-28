module
public import ABG.ChapterII.Section1.SmallSubgroups
public import ABG.ChapterII.Section1.NormalSubgroups
public import ABG.ChapterII.Section1.Omega
public import ABG.ChapterII.Section1.CentralQuotient
public import ABG.ChapterII.Section1.DihedralRotation
public import ABG.ChapterII.Section1.OrderFourClasses

/-!
# ABG Chapter II, Section 1, Lemma 1

This module assembles all eight clauses of the quasi-dihedral structure lemma
on article page 9 of `refs/latex/alperin-brauer-gorenstein.tex`. Its named
fields retain both element-conjugacy assertions, the complete four/quaternion
subgroup conjugacy and local structure assertions, the three maximal subgroup
models, the derived and Frattini equalities, both center assertions, the omega
subgroup, the proper normal subgroup alternatives, and the dihedral rotation
containment. Every clause uses one shared presentation and order parameter.

The source writes |S|=2^(n+1); the existing semidihedral predicate uses |S|=2^n.
Thus the derived subgroup here has order 2^(n-2), and the omega subgroup has
order 2^(n-1). In clause (viii), the cyclic maximal subgroup of a dihedral
subgroup of order at least eight is its unique cyclic subgroup of index two,
represented by the inverse image of the standard rotation under an actual
isomorphism. The bound and the actual ambient subgroup are retained.

The proof combines the preceding small modules. Normal forms yield the two
conjugacy classes and identify the center; explicit presentations identify the
maximal subgroups. Odd commutator powers and the finite p-group Frattini formula
identify the derived and Frattini subgroups. The four/quaternion representative
calculations and transport identify all their centralizers and normalizers.
Parity then identifies omega and proper normal subgroups, and products of
reflections give the final rotation containment. This assembly is the complete
local structure input to the following fusion proposition, not a replacement
for that proposition or for any of the three main theorems.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

/-- The eight source clauses, tied to the same quasi-dihedral presentation. -/
public structure LemmaOneConclusion (n : ℕ) (a b : G) : Prop where
  presentation : 4 ≤ n ∧ Nat.card G = 2 ^ n ∧ orderOf a = 2 ^ (n - 1) ∧
    orderOf b = 2 ∧ b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
    Subgroup.closure ({a, b} : Set G) = ⊤
  part_i :
    (∃ x y : G, orderOf x = 2 ∧ orderOf y = 2 ∧ ¬ IsConj x y ∧
      ∀ z : G, orderOf z = 2 → IsConj z x ∨ IsConj z y) ∧
    (∃ x y : G, orderOf x = 4 ∧ orderOf y = 4 ∧ ¬ IsConj x y ∧
      ∀ z : G, orderOf z = 4 → IsConj z x ∨ IsConj z y)
  part_ii :
    ∃ U V : Subgroup G, IsKleinFour U ∧ Nonempty (V ≃* QuaternionGroup 2) ∧
      (∀ T : Subgroup G, IsKleinFour T →
        ∃ g : G, U.map (MulAut.conj g).toMonoidHom = T) ∧
      (∀ T : Subgroup G, Nonempty (T ≃* QuaternionGroup 2) →
        ∃ g : G, V.map (MulAut.conj g).toMonoidHom = T) ∧
      ∀ T : Subgroup G, IsKleinFour T ∨ Nonempty (T ≃* QuaternionGroup 2) →
        Subgroup.centralizer (T : Set G) = (Subgroup.center T).map T.subtype ∧
        T.relIndex (Subgroup.normalizer (T : Set G)) = 2
  part_iii :
    let C := Subgroup.zpowers a
    let D := Subgroup.closure ({a ^ 2, b} : Set G)
    let Q := Subgroup.closure ({a ^ 2, a * b} : Set G)
    C ≠ D ∧ C ≠ Q ∧ D ≠ Q ∧
      (∀ H : Subgroup G, IsCoatom H ↔ H = C ∨ H = D ∨ H = Q) ∧
      IsCyclic C ∧ Nonempty (D ≃* DihedralGroup (2 ^ (n - 2))) ∧
        Nonempty (Q ≃* QuaternionGroup (2 ^ (n - 3)))
  part_iv :
    commutator G = frattini G ∧ frattini G = Subgroup.zpowers (a ^ 2) ∧
      IsCyclic (commutator G) ∧ Nat.card (commutator G) = 2 ^ (n - 2)
  part_v :
    Nat.card (Subgroup.center G) = 2 ∧
      Nonempty ((G ⧸ Subgroup.center G) ≃* DihedralGroup (2 ^ (n - 2)))
  part_vi :
    Stellmacher.IsDihedralGroup (omega₁ (G := G) (p := 2)) ∧
      Nat.card (omega₁ (G := G) (p := 2)) = 2 ^ (n - 1)
  part_vii :
    ∀ (H : Subgroup G) (_ : H.Normal), H ≠ ⊤ →
      IsCoatom H ∨ (IsCyclic H ∧ H ≤ commutator G)
  part_viii :
    ∀ (D : Subgroup G) {m : ℕ} (e : D ≃* DihedralGroup m), 8 ≤ Nat.card D →
      (Subgroup.zpowers (e.symm (DihedralGroup.r 1))).map D.subtype ≤ Subgroup.zpowers a

/-- All clauses of ABG II.1.1 for the given presentation witnesses. -/
public theorem lemma_one_of_presentation {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card G = 2 ^ n) (a b : G)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : orderOf b = 2)
    (hab : b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1))
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) :
    LemmaOneConclusion n a b := by
  have hG : Stellmacher.IsSemidihedralGroup G :=
    ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩
  exact {
    presentation := ⟨hn, hcard, ha, hb, hab, hgen⟩
    part_i := ⟨involution_conjugacy_classes hG, order_four_conjugacy_classes hG⟩
    part_ii := four_quaternion_subgroups hG
    part_iii := maximal_subgroups hn a b hcard ha hb hab hgen
    part_iv := derived_eq_frattini hn hcard a b ha hb hab hgen
    part_v := ⟨card_center hG, central_quotient_equiv hn hcard a b ha hb hab hgen⟩
    part_vi := omega_one_dihedral hn a b hcard ha hb hab hgen
    part_vii := fun H hH hproper => @normal_subgroup_maximal_or_cyclic G _ hG H hH hproper
    part_viii := fun D _ e hD => dihedral_subgroup_rotation_le hn a b ha hb hab hgen D e hD }

/-- ABG Chapter II, Section 1, Lemma 1, with all eight clauses. -/
public theorem lemma_one (hG : Stellmacher.IsSemidihedralGroup G) :
    ∃ (n : ℕ) (a b : G), LemmaOneConclusion n a b := by
  obtain ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩ := hG
  exact ⟨n, a, b, lemma_one_of_presentation hn hcard a b ha hb hab hgen⟩
end ABG.QuasiDihedral
