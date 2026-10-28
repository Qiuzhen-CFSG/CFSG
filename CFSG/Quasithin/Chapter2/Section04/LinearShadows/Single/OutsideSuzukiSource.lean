module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideDerivedSource
public import Theory.GroupTheory.ElementarySwappedFixed

/-!
# The fixed derived group in the nontrivial-center outside row

An outside involution exchanges the two disjoint distinguished factors of
Z(R). Its central fixed group is a full diagonal of order 2^n, and all its
members are central displacements. The elementary-pair fixed-derived theorem
therefore identifies this subgroup with the derived subgroup of C_R(a).

These are the exact Suzuki-type outputs of Aschbacher–Smith, 2.4.14(3),
used in the outside exclusion at the start of 2.4.21, printed pp.535–536.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_noncenterless_outside_center_fixed_data
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haT : a ∈ T) (haS : a ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    Nat.card (Z ⊓ centralizer ({a} : Set G) : Subgroup G)=2^n ∧
      ∀ z ∈ Z, Commute a z → ∃ w ∈ Z, z=w*(a*w*a⁻¹)⁻¹ := by
  intro R Z
  let A := distinguishedZ d
  let B := A.map (MulAut.conj a).toMonoidHom
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using ha2)
  obtain ⟨hd,hgen⟩ := source_distinguished_center_pair d hG T hST hsingle hL
    hM hTM hunique hz a haT haS
  rw [hai] at hd hgen
  have hzdata := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 A := hzdata.1
  have hBR : B≤R := le_sup_right.trans hgen.le |>.trans inf_le_left
  have hc : A≤centralizer (B:Set G) :=
    hzdata.2.2.1.trans inf_le_right |>.trans (centralizer_le hBR)
  have hα (x : G) : (MulAut.conj a) ((MulAut.conj a) x)=x := by
    change a*(a*x*a⁻¹)*a⁻¹=x
    have haa : a*a=1 := by simpa only [pow_two] using ha2
    rw [hai]
    calc a*(a*x*a)*a=(a*a)*x*(a*a) := by group
         _=x := by rw [haa,one_mul,mul_one]
  have hf := elementary_swapped_pair_fixed A B hd hc (MulAut.conj a) hα rfl
  have heq : (MulAut.conj a).toMonoidHom.eqLocus (MonoidHom.id G) = centralizer ({a}:Set G) := by
    ext x
    change a*x*a⁻¹=x ↔ x∈centralizer ({a}:Set G)
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  rw [hgen,heq,hzdata.2.1] at hf
  refine ⟨hf.1,?_⟩
  intro z hz hza
  exact hf.2 z hz (mul_inv_eq_iff_eq_mul.mpr hza.eq)

theorem source_noncenterless_outside_fixed_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) ≠ ⊥)
    (a : G) (haT : a ∈ T) (haS : a ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (ha2 : a^2=1) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := R ⊓ centralizer (R : Set G)
    let I := R ⊓ centralizer ({a} : Set G)
    ⁅I,I⁆=Z⊓centralizer ({a}:Set G) ∧ Nat.card (⁅I,I⁆ : Subgroup G)=2^n := by
  intro R Z I
  have hd := source_noncenterless_outside_center_fixed_data d hG T hST hsingle hL
    hM hTM hunique hz a haT haS ha2
  have he := source_outside_fixed_derived_of_coboundaries d hG T hST hsingle hL
    hM hTM hunique a haT haS ha2 hd.2
  exact ⟨he,he ▸ hd.1⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
