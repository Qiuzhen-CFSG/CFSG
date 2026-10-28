module
public import Theory.SpecificGroups.SL2.SylowBorelSeparation
/-!
# Borels above a two-group kernel

A surjection onto SL₂ in characteristic two identifies the normalizer of
any Sylow two-subgroup containing its kernel with a Borel preimage. The
upper-left diagonal entry gives a surjection from that normalizer onto the
field's units, with exactly the Sylow subgroup as kernel. Every complement
is therefore isomorphic to the multiplicative group of the field.

The proper-overgroup statement identifies the Borel selected by the original
minimal parabolic in Aschbacher–Smith 2.4.8, printed pp.529–530.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {A F : Type*} [Group A] [Field F]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one
def borelDiagonalProjection : rankOneBorel F →* Fˣ where
  toFun g := Units.mk0 (g.val.val 0 0) (by
    have hd : g.val.val 0 0 * g.val.val 1 1 = 1 := by
      simpa only [det_fin_two, (mem_rankOneBorel_iff _).mp g.property,
        mul_zero, sub_zero] using g.val.property
    exact left_ne_zero_of_mul_eq_one hd)
  map_one' := by ext; rfl
  map_mul' g h := by
    ext
    simp [mul_apply, Fin.sum_univ_two, (mem_rankOneBorel_iff _).mp h.property]

theorem borelDiagonalProjection_eq_one_iff (g : rankOneBorel F) :
    borelDiagonalProjection g = 1 ↔ g.val ∈ upperUnipotent F := by
  constructor
  · intro hg
    have h00 : g.val.val 0 0 = 1 := congrArg Units.val hg
    have h10 := (mem_rankOneBorel_iff _).mp g.property
    have h11 : g.val.val 1 1 = 1 := by
      simpa only [det_fin_two, h00, h10, one_mul, mul_zero, sub_zero] using g.val.property
    refine (mem_upperUnipotent F _).mpr ⟨g.val.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transvection_coe, h00, h10, h11]
  · intro hg
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F _).mp hg
    apply Units.ext
    change g.val.val 0 0 = 1
    rw [← ht]
    simp [transvection_coe]


theorem borelDiagonalProjection_surjective :
    Function.Surjective (borelDiagonalProjection (F := F)) := by
  intro a
  refine ⟨⟨diag2 a a.ne_zero, diag_mem_rankOneBorel (a : F) a.ne_zero⟩, ?_⟩
  apply Units.ext
  simp [borelDiagonalProjection, diag2_coe']

variable [Finite A] [Finite F] [CharP F 2]

theorem proper_overgroup_le_sylow_normalizer_of_two_kernel
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 A)
    (hk : q.ker ≤ (P : Subgroup A)) (B : Subgroup A)
    (hPB : (P : Subgroup A) ≤ B) (hB : B ≠ ⊤) :
    B ≤ normalizer (P : Set A) := by
  let R := P.mapSurjective hq
  have hBq : B.map q ≠ ⊤ := by
    intro he
    have hh := comap_map_eq_self (hk.trans hPB)
    rw [he,comap_top] at hh
    exact hB hh.symm
  have hn := proper_overgroup_le_sylow_normalizer R (B.map q) (map_mono hPB) hBq
  have hh : B ≤ (normalizer (R : Set SL(2,F))).comap q := by
    intro b hb
    exact hn (mem_map_of_mem q hb)
  change B ≤ (normalizer (((P : Subgroup A).map q) : Set SL(2,F))).comap q at hh
  rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hk] at hh
  simpa only [P.coe_coe] using hh

theorem sylow_normalizer_ne_top_of_surjective
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 A) :
    normalizer (P : Set A) ≠ ⊤ := by
  intro he
  have hn := (P : Subgroup A).le_normalizer_map q
  rw [P.coe_coe,he,map_top_of_surjective q hq] at hn
  exact sylow_normalizer_ne_top (P.mapSurjective hq) (top_unique hn)

theorem exists_sylowNormalizer_diagonal
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 A)
    (hk : q.ker ≤ (P : Subgroup A)) :
    ∃ f : normalizer (P : Set A) →* Fˣ, Function.Surjective f ∧
      ∀ x, f x = 1 ↔ (x : A) ∈ P := by
  let R := P.mapSurjective hq
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq SL(2,F) R (upperUnipotentSylow F 2)
  let q' := (MulAut.conj a).toMonoidHom.comp q
  have hq' : Function.Surjective q' := (MulAut.conj a).surjective.comp hq
  have hP : (P : Subgroup A).map q' = upperUnipotent F := by
    dsimp only [q']
    rw [← Subgroup.map_map]
    change ((a • R : Sylow 2 SL(2,F)) : Subgroup SL(2,F)) = _
    rw [ha]
    rfl
  have hk' : q'.ker ≤ (P : Subgroup A) := by
    intro x hx
    apply hk
    exact (MulAut.conj a).map_eq_one_iff.mp hx
  have hroot : (upperUnipotent F).comap q' = P := by
    rw [←hP, comap_map_eq_self hk']
  have hN : (rankOneBorel F).comap q' = normalizer (P : Set A) := by
    rw [rankOneBorel, comap_normalizer_eq_of_surjective _ hq', hroot, P.coe_coe]
  let f0 : normalizer (P : Set A) →* rankOneBorel F :=
    (q'.comp (normalizer (P : Set A)).subtype).codRestrict _
      (by
        intro x
        change (x : A) ∈ (rankOneBorel F).comap q'
        rw [hN]
        exact x.property)
  have hf0 : Function.Surjective f0 := by
    intro y
    obtain ⟨x,hx⟩ := hq' y
    have hm : x ∈ normalizer (P : Set A) := by
      rw [←hN]
      change q' x ∈ rankOneBorel F
      rw [hx]
      exact y.property
    exact ⟨⟨x,hm⟩,Subtype.ext hx⟩
  refine ⟨borelDiagonalProjection.comp f0, borelDiagonalProjection_surjective.comp hf0, ?_⟩
  intro x
  change borelDiagonalProjection (f0 x) = 1 ↔ _
  rw [borelDiagonalProjection_eq_one_iff]
  exact Iff.of_eq (congrArg (fun H : Subgroup A => (x : A) ∈ H) hroot)

theorem sylow_normalizer_complement_equiv_units
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 A)
    (hk : q.ker ≤ (P : Subgroup A)) (D : Subgroup A)
    (hDN : D ≤ normalizer (P : Set A)) (hd : Disjoint (P : Subgroup A) D)
    (hgen : (P : Subgroup A) ⊔ D = normalizer (P : Set A)) :
    Nonempty (D ≃* Fˣ) := by
  obtain ⟨f,hf,hker⟩ := exists_sylowNormalizer_diagonal q hq P hk
  let N := normalizer (P : Set A)
  let C := D.subgroupOf N
  let K := (P : Subgroup A).subgroupOf N
  let r := f.comp C.subtype
  have hK : K = f.ker := by
    ext x
    exact (hker x).symm
  have hsup : K ⊔ C = ⊤ := by
    have hPN : (P : Subgroup A) ≤ N := by simpa only [N, P.coe_coe] using (P : Subgroup A).le_normalizer
    dsimp only [K,C]
    rw [←subgroupOf_sup hPN hDN, hgen]
    exact subgroupOf_self _
  have hr : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hd) ((hker x.val).mp hx) x.property
  have hrs : Function.Surjective r := by
    apply MonoidHom.range_eq_top.mp
    have he := congrArg (Subgroup.map f) hsup
    rw [Subgroup.map_sup, hK, (Subgroup.map_eq_bot_iff _).mpr le_rfl, bot_sup_eq,
      map_top_of_surjective _ hf] at he
    simpa only [r, MonoidHom.range_comp, Subgroup.range_subtype] using he
  exact ⟨(subgroupOfEquivOfLe hDN).symm.trans (MulEquiv.ofBijective r ⟨hr,hrs⟩)⟩

end Matrix.SpecialLinearGroup
