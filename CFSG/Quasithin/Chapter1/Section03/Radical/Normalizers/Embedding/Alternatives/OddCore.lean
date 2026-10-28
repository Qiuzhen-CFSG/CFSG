module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.Quotients
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Solvable radicals in the odd-core alternatives

In A.3.12(21), a solvable subgroup normal in the supplement maps to a
solvable normal subgroup of the odd-core quotient, and hence lies in the
solvable radical. In (22), its image is normal and solvable in SL₂(5),
hence central; if it is two-perfect that image is trivial. The odd core
is nilpotent by the common conclusions of A.3.6, so both arguments use
a solvable kernel. No branch-exclusion premise is imposed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.6 and A.3.12(21)–(22), printed pp.43–48; proof of 1.3.8, p.513.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
/-- The actual SL₂ model is quasisimple in the source parameter range. -/
theorem slTwo_quasisimple {A : Type*} [Group A] {q : ℕ}
    (h : LocalModels.IsSL A 2 q) (hq : 4 ≤ q) : IsQuasisimple A := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := inferInstance
  have hsq : (x : F) ^ 2 ≠ 1 := by
    intro he
    have hbound := orderOf_le_of_pow_eq_one zero_lt_two (Units.ext he)
    rw [orderOf_eq_card_of_forall_mem_zpowers hx] at hbound
    have hc := Nat.card_eq_card_units_add_one F
    omega
  let : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F) :=
    { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero x) hsq⟩
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega) }
  exact IsQuasisimple.of_mulEquiv e.symm

/-- Central matrices in SL₂ have order dividing two. -/
theorem slTwo_center_isTwoGroup {A : Type*} [Group A] {q : ℕ}
    (h : LocalModels.IsSL A 2 q) : IsPGroup 2 (center A) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  refine IsPGroup.of_equiv (G := center (Matrix.SpecialLinearGroup (Fin 2) F))
    ?_ (centerCongr e).symm
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  obtain ⟨a, ha, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp g.property
  simp only [Fintype.card_fin] at ha
  rcases sq_eq_one_iff.mp ha with rfl | rfl
  · have hg : (g : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
      apply Subtype.ext
      simpa using he.symm
    simp [hg]
  · have hg : (g : Matrix.SpecialLinearGroup (Fin 2) F) = -1 := by
      apply Subtype.ext
      simpa [← Matrix.diagonal_neg] using he.symm
    simp [hg]

/-- A solvable normal subgroup of a quasisimple group is central. -/
theorem solvable_normal_le_center {A : Type*} [Group A] [IsQuasisimple A]
    (D : Subgroup A) [D.Normal] [Group.IsSolvable D] : D ≤ center A := by
  rcases IsQuasisimple.normal_le_center_or_eq_top D with h | h
  · exact h
  · let : Group.IsSolvable (⊤ : Subgroup A) := h ▸ inferInstance
    let : Group.IsSolvable A := Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom) topEquiv.surjective
    let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
    let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
    exact (Group.IsPerfect.not_isSolvable A inferInstance).elim

/-- A solvable normal two-perfect subgroup of SL₂(5) is trivial. -/
theorem solvable_twoPerfect_normal_eq_bot_of_slTwoFive
    {A : Type*} [Group A] (h : LocalModels.IsSL A 2 5)
    (D : Subgroup A) [D.Normal] [Group.IsSolvable D] (hD : IsPPerfect 2 D) : D = ⊥ := by
  let := slTwo_quasisimple h (by decide)
  have hp : IsPGroup 2 D := (slTwo_center_isTwoGroup h).to_le (solvable_normal_le_center D)
  have he := hD ⊥ inferInstance (hp.to_quotient ⊥)
  apply D.eq_bot_iff_forall.mpr
  intro x hx
  have hx' : (⟨x, hx⟩ : D) ∈ (⊥ : Subgroup D) := by rw [he]; trivial
  exact congrArg Subtype.val (mem_bot.mp hx')

/-- A normal solvable subgroup of a supplement lies in the radical when the kernel is solvable. -/
theorem normal_solvable_cover_le_radical {A H : Type*} [Group A] [Group H]
    [Finite A] [Finite H] (f : A →* H) [Group.IsSolvable f.ker]
    (B X : Subgroup A) (hXB : X ≤ B) (hX : (X.subgroupOf B).Normal)
    [Group.IsSolvable X] (hB : B.map f = ⊤) : X ≤ solvableRadical A := by
  have hfB : Function.Surjective (f.comp B.subtype) := by
    apply MonoidHom.range_eq_top.mp
    simpa only [MonoidHom.range_comp, range_subtype] using hB
  have he : (X.subgroupOf B).map (f.comp B.subtype) = X.map f := by
    rw [← map_map, map_subgroupOf_eq_of_le hXB]
  let : (X.map f).Normal := he ▸ hX.map _ hfB
  let : Group.IsSolvable (X.map f) := Group.isSolvable_of_surjective
    (f := f.subgroupMap X) (f.subgroupMap_surjective X)
  have hx := le_solvableRadical (X.map f) inferInstance inferInstance
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨b, hb⟩ := hfB y
    exact ⟨b, hb⟩
  rw [← comap_solvableRadical_eq_of_solvable_ker f hf]
  exact map_le_iff_le_comap.mp hx

/-- The marked solvable two-perfect subgroup dies in an SL₂(5) image. -/
theorem normal_solvable_twoPerfect_le_ker_of_slTwoFive_image
    {A H : Type*} [Group A] [Group H] (f : A →* H)
    (B X : Subgroup A) (hXB : X ≤ B) (hX : (X.subgroupOf B).Normal)
    [Group.IsSolvable X] (hXp : IsPPerfect 2 X)
    (hB : LocalModels.IsSL (B.map f) 2 5) : X ≤ f.ker := by
  let D := X.subgroupOf B
  let e := subgroupOfEquivOfLe hXB
  let : D.Normal := hX
  let : Group.IsSolvable D := Group.isSolvable_of_surjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hDp := hXp.of_surjective e.symm.toMonoidHom e.symm.surjective
  let g := f.subgroupMap B
  let : (D.map g).Normal := hX.map g (f.subgroupMap_surjective B)
  let : Group.IsSolvable (D.map g) := Group.isSolvable_of_surjective
    (f := g.subgroupMap D) (g.subgroupMap_surjective D)
  have hz := solvable_twoPerfect_normal_eq_bot_of_slTwoFive hB (D.map g)
    (hDp.of_surjective (g.subgroupMap D) (g.subgroupMap_surjective D))
  intro x hx
  have hm : g ⟨x, hXB hx⟩ ∈ D.map g := mem_map_of_mem g hx
  rw [hz, mem_bot] at hm
  exact congrArg Subtype.val hm

/-- A.3.6 identifies the odd core with the nilpotent Fitting subgroup. -/
theorem oddCore_solvable_of_A36Common {A : Type*} [Group A] [Finite A]
    (h : A36Common A) : Group.IsSolvable (pPrimeCore 2 A) := by
  rw [← h.1]
  infer_instance

/-- The supplement alternative puts the marked subgroup in the radical. -/
theorem radical_of_oddCore_cover {A : Type*} [Group A] [Finite A]
    (h : A36Common A) (B X : Subgroup A) (hXB : X ≤ B)
    (hX : (X.subgroupOf B).Normal) [Group.IsSolvable X]
    (hcover : B ⊔ pPrimeCore 2 A = ⊤) : X ≤ solvableRadical A := by
  let f := QuotientGroup.mk' (pPrimeCore 2 A)
  let : Group.IsSolvable (pPrimeCore 2 A) := oddCore_solvable_of_A36Common h
  let : Group.IsSolvable f.ker := by
    change Group.IsSolvable (QuotientGroup.mk' (pPrimeCore 2 A)).ker
    rw [QuotientGroup.ker_mk']
    infer_instance
  apply normal_solvable_cover_le_radical f B X hXB hX
  apply (comap_injective (QuotientGroup.mk'_surjective _))
  simpa only [comap_map_eq, f, QuotientGroup.ker_mk', comap_top] using hcover

/-- The SL₂(5) quotient-image alternative puts the marked subgroup in the radical. -/
theorem radical_of_slTwoFive_oddCore_image {A : Type*} [Group A] [Finite A]
    (h : A36Common A) (B X : Subgroup A) (hXB : X ≤ B)
    (hX : (X.subgroupOf B).Normal) [Group.IsSolvable X] (hXp : IsPPerfect 2 X)
    (himage : LocalModels.IsSL (B.map (QuotientGroup.mk' (pPrimeCore 2 A))) 2 5) :
    X ≤ solvableRadical A := by
  have hx := normal_solvable_twoPerfect_le_ker_of_slTwoFive_image
    (QuotientGroup.mk' (pPrimeCore 2 A)) B X hXB hX hXp himage
  rw [QuotientGroup.ker_mk'] at hx
  let : Group.IsSolvable (pPrimeCore 2 A) := oddCore_solvable_of_A36Common h
  exact hx.trans (le_solvableRadical _ inferInstance inferInstance)


variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
/-- Relative normality is preserved when both subgroups are viewed inside an overgroup. -/
theorem normal_restrict {X B K : Subgroup A} (hXB : X ≤ B) (hBK : B ≤ K)
    (hX : (X.subgroupOf B).Normal) :
    ((X.subgroupOf K).subgroupOf (B.subgroupOf K)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [← subgroupOf_normalizer_eq (hXB.trans hBK)]
  exact comap_mono ((normal_subgroupOf_iff_le_normalizer hXB).mp hX)

/-- The intrinsic supplement argument retains the given ambient embeddings. -/
theorem embedded_radical_of_cover {X B K : Subgroup A}
    (hcommon : A36Common K) (hXB : X ≤ B) (hBK : B ≤ K)
    (hX : (X.subgroupOf B).Normal) [Group.IsSolvable X]
    (hgen : B ⊔ (pPrimeCore 2 K).map K.subtype = K) :
    X ≤ (solvableRadical K).map K.subtype := by
  let e := subgroupOfEquivOfLe (hXB.trans hBK)
  let : Group.IsSolvable (X.subgroupOf K) := Group.isSolvable_of_surjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hg : B.subgroupOf K ⊔ pPrimeCore 2 K = ⊤ := by
    have he := congrArg (fun D : Subgroup A => D.subgroupOf K) hgen
    rwa [subgroupOf_sup hBK (map_subtype_le _),
      show ((pPrimeCore 2 K).map K.subtype).subgroupOf K = pPrimeCore 2 K from
        comap_map_eq_self_of_injective K.subtype_injective _, subgroupOf_self] at he
  have hx := radical_of_oddCore_cover hcommon (B.subgroupOf K) (X.subgroupOf K)
    (comap_mono hXB) (normal_restrict hXB hBK hX) hg
  have hm := map_mono (f := K.subtype) hx
  rwa [map_subgroupOf_eq_of_le (hXB.trans hBK)] at hm

/-- The intrinsic SL₂(5) image argument retains the given ambient embeddings. -/
theorem embedded_radical_of_slFive_image {X B K : Subgroup A}
    (hcommon : A36Common K) (hXB : X ≤ B) (hBK : B ≤ K)
    (hX : (X.subgroupOf B).Normal) [Group.IsSolvable X] (hXp : IsPPerfect 2 X)
    (himage : LocalModels.IsSL
      ((B.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 K))) 2 5) :
    X ≤ (solvableRadical K).map K.subtype := by
  let e := subgroupOfEquivOfLe (hXB.trans hBK)
  let : Group.IsSolvable (X.subgroupOf K) := Group.isSolvable_of_surjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hp := hXp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hx := radical_of_slTwoFive_oddCore_image hcommon (B.subgroupOf K) (X.subgroupOf K)
    (comap_mono hXB) (normal_restrict hXB hBK hX) hp himage
  have hm := map_mono (f := K.subtype) hx
  rwa [map_subgroupOf_eq_of_le (hXB.trans hBK)] at hm

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
