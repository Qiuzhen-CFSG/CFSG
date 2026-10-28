module

public import Theory.GroupTheory.ExtraspecialSquare

/-! Subgroups containing the original extraspecial center are recovered from
  their actual square-form images. -/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.ExtraspecialSquare
variable {P : Type*} [Group P] [IsExtraspecial 2 P]

/-- Vanishing of the actual square form on the image forces exponent two. -/
theorem elementary_of_imageSpace_singular (A : Subgroup P)
    (h : ∀ v ∈ imageSpace P A, form P v=0) : IsElementaryAbelian 2 A := by
  have hs (x : A) : x^2=1 := by
    apply Subtype.ext
    exact (form_mk_eq_zero P x.val).mp (h _ ⟨x.val,x.property,rfl⟩)
  let : IsMulCommutative A := ⟨⟨fun x y =>
    (Commute.of_orderOf_dvd_two (fun a => orderOf_dvd_of_pow_eq_one (hs a)) x y).eq⟩⟩
  exact { exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }

/-- The zero square image is precisely containment in the actual center. -/
theorem imageSpace_eq_bot_iff (A : Subgroup P) : imageSpace P A=⊥ ↔ A≤center P := by
  constructor
  · intro he x hx
    have hh : Additive.ofMul (QuotientGroup.mk' (center P) x)∈imageSpace P A := ⟨x,hx,rfl⟩
    rw [he] at hh
    have hz : QuotientGroup.mk' (center P) x=1 := hh
    exact (QuotientGroup.eq_one_iff x).mp hz
  · intro hle
    apply eq_bot_iff.mpr
    rintro v ⟨x,hx,he⟩
    have hz : QuotientGroup.mk' (center P) x=1 := (QuotientGroup.eq_one_iff x).mpr (hle hx)
    change v=0
    exact congrArg Additive.ofMul (he.symm.trans hz)

/-- A subgroup containing the center and filling its quotient is the whole group. -/
theorem imageSpace_eq_top_iff (A : Subgroup P) (hZ : center P≤A) :
    imageSpace P A=⊤ ↔ A=⊤ := by
  constructor
  · intro he
    have hmap : A.map (QuotientGroup.mk' (center P))=⊤ := by
      ext x
      have hh := congrArg (fun S : Submodule (ZMod 2) (Space P) => Additive.ofMul x∈S) he
      exact eq_iff_iff.mp hh
    have hh := congrArg (Subgroup.comap (QuotientGroup.mk' (center P))) hmap
    simpa only [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hZ,comap_top] using hh
  · rintro rfl
    exact imageSpace_top P

/-- The square image keeps the automorphism marking of the original subgroup. -/
theorem linearAction_mem_imageSpace (A : Subgroup P) (a : MulAut P)
    (ha : ∀ x∈A, a x∈A) (v : Space P) (hv : v∈imageSpace P A) :
    linearAction P a v∈imageSpace P A := by
  obtain ⟨x,hx,he⟩ := hv
  have hv : v=Additive.ofMul (QuotientGroup.mk' (center P) x) := congrArg Additive.ofMul he.symm
  rw [hv,linearAction_apply,quotientAut_apply_mk]
  exact ⟨a x,ha x hx,rfl⟩

end Theory.GroupTheory.ExtraspecialSquare
