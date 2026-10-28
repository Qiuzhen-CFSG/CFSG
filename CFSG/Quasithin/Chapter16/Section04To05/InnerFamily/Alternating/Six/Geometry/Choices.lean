module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup

/-!
# Compatible conjugator choices for the A₆ geometry

Sylow conjugacy inside N_G(K′) corrects the conjugator without changing
T, z, L, R, K′ or its attached component L′. The corrected choice satisfies
the transport containment of 16.4.2(4). The existing involution transport
then identifies the outer involution r with a conjugate of z when T_C = ⟨z⟩.

The conjugation is left conjugation. Thus correction multiplies the original
conjugator on the left by an element of N_G(K′). This proof uses only the
shared intersection interfaces and does not import product-model construction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.4.2(4) and proof of 16.4.9(2), printed pp.1183 and 1192.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six
variable {G : Type*} [Group G] [Finite G]

/-- Correct the conjugator while retaining the original component and involutions. -/
theorem exists_compatible_transport
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) :
    ∃ a : G, IntersectionSetup T z L a R ∧
      (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g ∧
      L.conjBy a = L.conjBy g ∧
      (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy a : Set G) ≤
        (T : Subgroup G).conjBy a := by
  have hle : (T : Subgroup G) ≤ normalizer (centralizer (L : Set G) : Set G) :=
    h.normalizers_eq ▸ h.sylow_normalizes
  have hS : SylowIn (T : Subgroup G) (normalizer (centralizer (L : Set G) : Set G)) :=
    ⟨T.subtype hle, map_subgroupOf_eq_of_le hle⟩
  have hSg := hS.map (MulAut.conj g)
  rw [map_equiv_normalizer_eq] at hSg
  let N := normalizer ((centralizer (L : Set G)).conjBy g : Set G)
  let Q := (T : Subgroup G) ⊓ N
  have hp : IsPGroup 2 Q :=
    T.isPGroup'.of_injective (inclusion inf_le_left) (inclusion_injective _)
  change SylowIn ((T : Subgroup G).conjBy g) N at hSg
  obtain ⟨S, hS⟩ := hSg
  obtain ⟨U, hU⟩ := (hp.of_equiv (subgroupOfEquivOfLe (show Q ≤ N from inf_le_right)).symm).exists_le_sylow
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq N U S
  have hQ : Q.conjBy (b : G) ≤ (T : Subgroup G).conjBy g := by
    rw [← hS]
    rintro x ⟨y, hy, rfl⟩
    refine ⟨b * ⟨y, hy.2⟩ * b⁻¹, ?_, rfl⟩
    rw [← hb]
    exact mem_map_of_mem (MulAut.conj b).toMonoidHom (hU hy)
  let a := (b : G)⁻¹ * g
  have he : (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g := by
    change (centralizer (L : Set G)).conjBy ((b : G)⁻¹ * g) = _
    rw [conjBy_mul]
    exact mem_normalizer_iff_map_conj_eq.mp (N.inv_mem b.property)
  have ht : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy a : Set G) ≤
      (T : Subgroup G).conjBy a := by
    rw [he]
    have hh := map_mono (f := (MulAut.conj (b : G)⁻¹).toMonoidHom) hQ
    change (Q.conjBy (b : G)).conjBy (b : G)⁻¹ ≤
      ((T : Subgroup G).conjBy g).conjBy (b : G)⁻¹ at hh
    simpa only [conjBy_conjBy, inv_mul_cancel, conjBy_one] using hh
  have ha : IntersectionSetup T z L a R := by
    refine ⟨h.toStandardSetup, he ▸ h.mem_delta, ?_, h.le_sylow⟩
    rw [he]
    exact h.sylow
  exact ⟨a, ha, he, h.toStandardSetup.component_conjugate_eq he, ht⟩

/-- The actual outer involution lies in the ambient conjugacy class of z. -/
theorem conjugate_outer {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hTC : commutingSylow T L = zpowers z)
    (hr : r ∈ R) (hr2 : orderOf r = 2) : IsConj z r := by
  obtain ⟨a, ha, _, _, ht⟩ := exists_compatible_transport h
  exact conjugate_outer_of_transport ha hTC ht hr hr2

end CFSG.Quasithin.Chapter16.Intersections.Six
