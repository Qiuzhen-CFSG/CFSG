module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreLifts
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.OverlapCores

/-!
# The point-core overlap as a square preimage

Inside the actual C₄³ normalizer core, the elements whose square lies in the
marked involution line form a subgroup of order sixteen. Every element of
the actual point-core intersection has this property, and that intersection
also has order sixteen. Hence the property characterizes the literal overlap.

This lets the explicit dual-plane correction retain a lift in its original
point core; it does not identify the plane centralizer with the point overlap.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims

private theorem zpowers_involution_cases {D : Type*} [Group D]
    (z : D) (hz : orderOf z = 2) (q : D) : q ∈ zpowers z ↔ q = 1 ∨ q = z := by
  classical
  have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨2, by decide, hz ▸ pow_orderOf_eq_one z⟩
  rw [hf.mem_zpowers_iff_mem_range_orderOf, hz]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have he : n = 0 ∨ n = 1 := by omega
    rcases he with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

private theorem square_preimage_card {P : Type*} [CommGroup P] [Finite P]
    (e : P ≃* Multiplicative (Fin 3 → ZMod 4)) (z : P) (hz : orderOf z = 2) :
    Nat.card ((zpowers z).comap (powMonoidHom 2 : P →* P)) = 16 := by
  let B := Multiplicative (Fin 3 → ZMod 4)
  have hc : ∀ z : B, z ^ 2 = 1 → z ≠ 1 →
      Fintype.card {q : B // q ^ 2 = 1 ∨ q ^ 2 = z} = 16 := by decide +kernel
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hez2 : e z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hez1 : e z ≠ 1 := by
    intro hh
    have hh' : z = 1 := e.injective (hh.trans e.map_one.symm)
    simp [hh'] at hz
  let f : ((zpowers z).comap (powMonoidHom 2 : P →* P)) ≃
      {q : B // q ^ 2 = 1 ∨ q ^ 2 = e z} := {
    toFun q := ⟨e q, by
      have hh := (zpowers_involution_cases z hz (q.val ^ 2)).mp q.property
      rcases hh with hh | hh
      · exact Or.inl (by rw [← map_pow, hh, map_one])
      · exact Or.inr (by rw [← map_pow, hh])⟩
    invFun q := ⟨e.symm q, by
      change (e.symm q) ^ 2 ∈ zpowers z
      apply (zpowers_involution_cases z hz ((e.symm q) ^ 2)).mpr
      rcases q.property with hh | hh
      · exact Or.inl (e.injective (by rw [map_pow, e.apply_symm_apply, hh, map_one]))
      · exact Or.inr (e.injective (by rw [map_pow, e.apply_symm_apply, hh]))⟩
    left_inv q := Subtype.ext (e.symm_apply_apply q)
    right_inv q := Subtype.ext (e.apply_symm_apply q) }
  rw [Nat.card_congr f, Nat.card_eq_fintype_card]
  exact hc (e z) hez2 hez1

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- A full-normalizer-core element belongs to the actual point core exactly
when its square belongs to the original distinguished involution line. -/
theorem TypeAt.mem_point_core_iff_square_mem (h : TypeAt z V) (q : G)
    (hq : q ∈ (normalizer (V : Set G)).pCoreIn 2) :
    q ∈ (involutionCentralizer z).pCoreIn 2 ↔ q ^ 2 ∈ zpowers z := by
  let M := normalizer (V : Set G)
  let P := M.pCoreIn 2
  let Q := (involutionCentralizer z).pCoreIn 2
  let e : P ≃* Multiplicative (Fin 3 → ZMod 4) :=
    ((pCore 2 M).equivMapOfInjective M.subtype M.subtype_injective).symm.trans
      ((MulEquiv.subgroupCongr h.normalizer_fitting.symm).trans
        (h.normalizer_core.some.trans (MulEquiv.funMultiplicative (Fin 3) (ZMod 4)).symm))
  let : IsMulCommutative P := ⟨⟨fun a b => e.injective
    ((e.map_mul a b).trans ((mul_comm (e a) (e b)).trans (e.map_mul b a).symm))⟩⟩
  let : CommGroup P := IsMulCommutative.instCommGroup
  have hzP : z ∈ P := by
    change z ∈ (pCore 2 (normalizer (V : Set G))).map (normalizer (V : Set G)).subtype
    rw [← h.seed_centralizer]
    let := h.elementary
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance) h.involution_mem_seed
  let zP : P := ⟨z, hzP⟩
  have hz : orderOf zP = 2 := by simpa only [← orderOf_coe] using h.involution
  let D := (zpowers zP).comap (powMonoidHom 2 : P →* P)
  have hD : Nat.card D = 16 := square_preimage_card e zP hz
  have hmem (a : G) : a ∈ D.map P.subtype ↔ a ∈ P ∧ a ^ 2 ∈ zpowers z := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.property, ?_⟩
      change (a : G) ^ 2 ∈ zpowers z
      rcases (zpowers_involution_cases zP hz (a ^ 2)).mp ha with hs | hs
      · rw [show (a : G) ^ 2 = 1 from congrArg Subtype.val hs]; exact (zpowers z).one_mem
      · rw [show (a : G) ^ 2 = z from congrArg Subtype.val hs]; exact mem_zpowers z
    · rintro ⟨ha, hs⟩
      refine ⟨⟨a, ha⟩, ?_, rfl⟩
      apply (zpowers_involution_cases zP hz _).mpr
      rcases (zpowers_involution_cases z h.involution _).mp hs with hs | hs
      · exact Or.inl (Subtype.ext hs)
      · exact Or.inr (Subtype.ext hs)
  have hQD : Q ⊓ P ≤ D.map P.subtype := by
    rintro a ⟨haQ, haP⟩
    exact (hmem a).mpr ⟨haP, h.centralizer_core_square_mem a haQ⟩
  have he : Q ⊓ P = D.map P.subtype := eq_of_le_of_card_ge hQD (by
    rw [card_map_of_injective P.subtype_injective, hD]
    exact h.local_cores_structure.1.ge)
  constructor
  · exact h.centralizer_core_square_mem q
  · intro hs
    exact (he.symm ▸ (hmem q).mpr ⟨hq, hs⟩).1

end CFSG.Quasithin.HigmanSims
