module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete
public import Theory.GroupTheory.DisjointCubicCore

/-!
# The original crossing core is the cubic commutator

The original source tuple supplies disjoint conjugate two-cores. Thompson
characteristicity puts the same crossing core inside the original R. Normality
of the binary component then converts its full coprime displacement into
containment in the component. The selected cubic's fixed-point calculation
and its normalization of this crossing core are retained for the torus and
common-Sylow-three producers, respectively.

Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/
public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Stellmacher
variable {G : Type*} [Group G] [Finite G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.crossing_core_eq_cubic_commutator_le
    (c : MathieuSourceSetup H L M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = L ⊔ (S : Subgroup H).map H.subtype)
    (e : L ⧸ center L ≃* Matrix.PSL3Four.PSL)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXL : X ≤ L)
    (hXN : X ≤ normalizer (((elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ⊓
      twoCore H).conjBy x⁻¹) : Set G))
    (hfixSylow : (((S : Subgroup H).map H.subtype) ⊓ L) ⊓
      centralizer (X : Set G) ≤ centralizer (L : Set G)) :
    let Q := (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ⊓
      twoCore H).conjBy x⁻¹
    Q = ⁅Q, X⁆ ∧ Q ≤ L := by
  let Y := (S : Subgroup H).map H.subtype
  let R := elementaryAbelianMaxJ Y
  let C := R ⊓ twoCore H
  let Q := C.conjBy x⁻¹
  let := MathieuSourceSetup.linear_nonbinary_component_normal c hG localC129Input_knownSimple
    hempty Matrix.PSL3Four.F (by decide : 1 < 2) (by simpa using Matrix.PSL3Four.card_F) e
  have hRY : R ≤ Y := sSup_le fun _ h => h.1
  have hRgen : R = (Y ⊓ L) ⊔ (R ⊓ centralizer (L : Set G)) :=
    MathieuSourceSetup.ambient_thompson_product c hgen
      (MathieuSourceSetup.linear_four_thompson_product c hG localC129Input_knownSimple
        hempty hgen e)
  have hfix : R ⊓ centralizer (X : Set G) ≤ twoCore H := by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    apply le_inf (inf_le_left.trans hRY)
    rintro r ⟨hr, hx⟩
    have hcomm : (R ⊓ centralizer (L : Set G)) ≤ centralizer ((Y ⊓ L : Subgroup G) : Set G) :=
      inf_le_right.trans (centralizer_le inf_le_right)
    have hprod : r ∈ ((Y ⊓ L : Subgroup G) : Set G) *
        ((R ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _
        (hcomm.trans (Subgroup.centralizer_le_normalizer _)), ← hRgen]
      exact hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod
    have hbX : b ∈ centralizer (X : Set G) := centralizer_le hXL hb.2
    have haX : a ∈ centralizer (X : Set G) := by
      have hh := (centralizer (X : Set G)).mul_mem hx
        ((centralizer (X : Set G)).inv_mem hbX)
      simpa only [mul_inv_cancel_right] using hh
    exact (centralizer (L : Set G)).mul_mem (hfixSylow ⟨ha, haX⟩) hb.2
  have hYN : Y ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hRconj : R.conjBy x⁻¹ = R := by
    change R.map (MulAut.conj x⁻¹).toMonoidHom = R
    rw [← elementaryAbelianMaxJ_map_injective _ (MulAut.conj x⁻¹).injective]
    have hm : Y.map (MulAut.conj x⁻¹).toMonoidHom = Y :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hxN)
    rw [hm]
  have hQR : Q ≤ R := by
    rw [← hRconj]
    exact map_mono inf_le_left
  have hp : IsPGroup 2 Q :=
    ((S.isPGroup'.map H.subtype).to_le (inf_le_left.trans hRY)).map
      (MulAut.conj x⁻¹).toMonoidHom
  have hdis0 : Disjoint (twoCore H) ((twoCore H).conjBy x⁻¹) :=
    (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le, c.component⟩ hgen hxT hxS hxN hx2).1
  have hdis : Disjoint Q C := hdis0.symm.mono
    (map_mono inf_le_right) inf_le_right
  exact disjoint_cubic_core_eq_commutator_le R C Q L X hp hX hQR
    (le_inf inf_le_left hfix) hdis hXN hXL (hQR.trans (hRY.trans hYN))
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
