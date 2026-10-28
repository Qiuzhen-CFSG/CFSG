module
public import Theory.SpecificGroups.SL2.TorusMoverCentralizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Rigidity from a full odd torus and its Sylow subgroup

An automorphism of SL₂ in characteristic two fixing a full odd split torus
and its Sylow two-subgroup pointwise is trivial. Simultaneous torus and
Sylow coordinates reduce this to the diagonal inner automorphism theorem;
a single nontrivial root element kills the remaining diagonal action.
The second theorem carries the conclusion above a two-core.

Source: the quotient-action step of DGS (10.8), printed pp.160--161.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open BenderSuzuki.ZD.Linear
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "diag" => fun z : Fˣ => diag2 (z:F) (Units.ne_zero z)

/-- Pointwise fixation of the Sylow and its full odd torus determines the
whole automorphism. -/
theorem odd_torus_and_sylow_fixed_eq_one (hF : 2 < Nat.card F)
    (S : Sylow 2 SL(2,F)) (C : Subgroup SL(2,F))
    (hC : C ≤ normalizer (S : Set SL(2,F)))
    (ho : Odd (Nat.card C)) (hcard : Nat.card C = Nat.card Fˣ)
    (α : MulAut SL(2,F))
    (hfixS : ∀ s ∈ S, α s = s)
    (hfixC : ∀ c ∈ C, α c = c) : α = 1 := by
  obtain ⟨m,d,hm,hd⟩ := sylow_odd_subgroup_diagonal_coordinates S C hC ho
  have hdi : Function.Injective d := by
    intro x y hxy
    apply Subtype.ext
    apply (MulAut.conj m).injective
    change m * x * m⁻¹ = m * y * m⁻¹
    rw [hd x,hd y,hxy]
  have hds : Function.Surjective d := by
    let _ : Fintype C := Fintype.ofFinite C
    let _ : Fintype Fˣ := Fintype.ofFinite Fˣ
    exact ((Fintype.bijective_iff_injective_and_card d).mpr
      ⟨hdi,by simpa only [←Nat.card_eq_fintype_card] using hcard⟩).2
  let e := MulAut.conj m
  let β := MulAut.congr e α
  have hβ (x : SL(2,F)) : β (e x) = e (α x) := by
    change e (α (e.symm (e x))) = _
    rw [e.symm_apply_apply]
  have hS : (S : Subgroup SL(2,F)).map α.toMonoidHom = S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change α y ∈ S
      rw [hfixS y hy]
      exact hy
    · intro hx
      exact ⟨x,hx,hfixS x hx⟩
  have hβU : (upperUnipotent F).map β.toMonoidHom = upperUnipotent F := by
    rw [←hm,Subgroup.map_map]
    have he : β.toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := MonoidHom.ext hβ
    change (S : Subgroup SL(2,F)).map (β.toMonoidHom.comp e.toMonoidHom) = _
    rw [he,←Subgroup.map_map,hS]
  have hβD (z : Fˣ) : β (diag z) = diag z := by
    obtain ⟨x,rfl⟩ := hds z
    change β (diag2 (d x : F) _) = diag2 (d x : F) _
    rw [←hd x]
    change β (e x) = e x
    rw [hβ,hfixC x x.property]
  have hfixU (x : SL(2,F)) (hx : x ∈ upperUnipotent F) : β x = x := by
    rw [←hm] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    rw [show (MulAut.conj m).toMonoidHom y = e y from rfl,hβ,hfixS y hy]
  have hβ1 := sylow_torus_and_root_fixed_eq_one hF β hβU hβD
    (hfixU _ ((mem_upperUnipotent F _).mpr ⟨1,rfl⟩))
  apply (MulAut.congr e).injective
  simpa only [map_one] using hβ1

variable {A : Type*} [Group A] [Finite A]

/-- Fixation modulo the two-core of a Sylow, together with pointwise
fixation of its full odd torus, gives trivial action on the whole quotient. -/
theorem core_quotient_torus_sylow_fixed (hF : 2 < Nat.card F)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F))
    (T : Sylow 2 A) (C : Subgroup A)
    (hC : C ≤ normalizer (T : Set A))
    (ho : Odd (Nat.card C)) (hcard : Nat.card C = Nat.card Fˣ)
    (α : MulAut A)
    (hfixT : ∀ t ∈ T, QuotientGroup.mk' (pCore 2 A) (α t) =
      QuotientGroup.mk' (pCore 2 A) t)
    (hfixC : ∀ c ∈ C, α c = c) :
    quotientAut (pCore 2 A) α = 1 := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 A := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hker : q.ker ≤ (T : Subgroup A) := hk ▸ pCore_isPGroup.le_sylow_of_normal T
  let S := T.mapSurjective hq
  let D := C.map q
  let β := MulAut.congr e (quotientAut (pCore 2 A) α)
  have hβ (x : A) : β (q x) = q (α x) := by
    change e (quotientAut (pCore 2 A) α (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hDS : D ≤ normalizer (S : Set SL(2,F)) :=
    (map_mono hC).trans (le_normalizer_map q)
  have hDo : Odd (Nat.card D) := ho.of_dvd_nat (C.card_map_dvd q)
  have hd : Disjoint C q.ker := by
    obtain ⟨n,hn⟩ := (show IsPGroup 2 q.ker from hk ▸ pCore_isPGroup).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hn]; exact ho.coprime_two_right.pow_right n)
  have hqi : Function.Injective (q.subgroupMap C) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    apply Subtype.ext
    apply disjoint_def.mp hd x.property
    exact congrArg Subtype.val hx
  have hDc : Nat.card D = Nat.card Fˣ :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap C)
      ⟨hqi,q.subgroupMap_surjective C⟩).toEquiv).symm.trans hcard
  have hfixS : ∀ s ∈ S, β s = s := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hβ]
    exact congrArg e (hfixT t ht)
  have hfixD : ∀ d ∈ D, β d = d := by
    rintro _ ⟨c,hc,rfl⟩
    rw [hβ,hfixC c hc]
  have hβ1 := odd_torus_and_sylow_fixed_eq_one hF S D hDS hDo hDc β hfixS hfixD
  apply (MulAut.congr e).injective
  simpa only [map_one] using hβ1

end Matrix.SpecialLinearGroup
