module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.QuotientFamily

/-!
# The literal local family in the chief-component argument

For `S = N_T(J)` and `H = JS`, the source family is
`Γ = {A ∩ H : A ∈ Ω}`. Intrinsically it is the image of Ω under subgroup comap
to H, not the subfamily of members contained in H. Conjugation in H preserves
this family. Mapping its weak closure back to G gives exactly the weak closure
of the ambient intersection family, and S normalizes it.

These definitions are shared by the two diagonal branches of E.1.11. The
transport proved here does not identify this family with ordinary restriction,
or identify its weak closure with the global weak closure.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, E.1.11, printed pp.213--214.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.ChiefOrbit
variable {G : Type*} [Group G]

/-- The source stabilizer `N_T(J)`, retained in the ambient group. -/
def stabilizer (T : Sylow 2 G) (J : Subgroup G) : Subgroup G :=
  (T : Subgroup G) ⊓ normalizer (J : Set G)

/-- The local product `JS`. -/
def localGroup (T : Sylow 2 G) (J : Subgroup G) : Subgroup G :=
  J ⊔ stabilizer T J

/-- The literal intersection family, intrinsic to the local group. -/
def intersectionFamily (H : Subgroup G) (Ω : Set (Subgroup G)) : Set (Subgroup H) :=
  (fun A : Subgroup G => A.subgroupOf H) '' Ω

theorem intersectionFamily_elementary (H : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    IsElementaryFamily (intersectionFamily H Ω) := by
  constructor
  · rintro _ ⟨A, hA, rfl⟩
    let _ := hΩ.1 A hA
    refine { toIsMulCommutative := Subgroup.subgroupOf_isMulCommutative H A
             exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change (x.val.val : G) ^ 2 = 1
    exact elemPow_eq_one_of_isElementaryAbelian (A := A) _ x.property
  · rintro g _ ⟨A, hA, rfl⟩
    refine ⟨A.map (MulAut.conj (g : G)).toMonoidHom, hΩ.2 _ _ hA, ?_⟩
    ext x
    constructor
    · rintro ⟨a, ha, he⟩
      refine ⟨g⁻¹ * x * g, ?_, ?_⟩
      · change ((g : G)⁻¹ * (x : G) * (g : G)) ∈ A
        change (g : G) * a * (g : G)⁻¹ = (x : G) at he
        rw [← he]
        simpa [MulAut.conj_apply, mul_assoc] using ha
      · simp [MulAut.conj_apply, mul_assoc]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, rfl⟩

theorem map_weakClosure_intersectionFamily (H S : Subgroup G) (hSH : S ≤ H)
    (Ω : Set (Subgroup G)) :
    (weakClosure (S.subgroupOf H) (intersectionFamily H Ω)).map H.subtype =
      weakClosure S ((fun A : Subgroup G => A ⊓ H) '' Ω) := by
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro B ⟨⟨A, hA, rfl⟩, hAS⟩
    apply map_le_iff_le_comap.mp
    rw [subgroupOf_map_subtype]
    apply le_sSup
    refine ⟨⟨A, hA, rfl⟩, ?_⟩
    have h := map_mono (f := H.subtype) hAS
    simpa only [subgroupOf_map_subtype, inf_eq_left.mpr hSH] using h
  · apply sSup_le
    rintro B ⟨⟨A, hA, rfl⟩, hAS⟩
    change A ⊓ H ≤ _
    rw [← subgroupOf_map_subtype A H]
    apply map_mono
    apply le_sSup
    refine ⟨⟨A, hA, rfl⟩, ?_⟩
    intro x hx
    exact hAS ⟨hx, x.property⟩

/-- The source `W₀`, mapped from the intrinsic local group to the ambient group. -/
def localWeakClosure (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) :
    Subgroup G :=
  (weakClosure ((stabilizer T J).subgroupOf (localGroup T J))
    (intersectionFamily (localGroup T J) Ω)).map (localGroup T J).subtype

variable [Finite G] in
/-- The source local E-family subgroup, mapped to the ambient group. -/
def localEFamily (n : ℕ) (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) :
    Subgroup G :=
  (eFamilySubgroup n ((stabilizer T J).subgroupOf (localGroup T J))
    (intersectionFamily (localGroup T J) Ω)).map (localGroup T J).subtype

theorem localWeakClosure_eq (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) :
    localWeakClosure T J Ω = weakClosure (stabilizer T J)
      ((fun A : Subgroup G => A ⊓ localGroup T J) '' Ω) :=
  map_weakClosure_intersectionFamily _ _ le_sup_right Ω

theorem localWeakClosure_le (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) :
    localWeakClosure T J Ω ≤ stabilizer T J := by
  rw [localWeakClosure_eq]
  exact weakClosure_le _ _

variable [Finite G] in
theorem stabilizer_le_localWeakClosure_normalizer (T : Sylow 2 G) (J : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsElementaryFamily Ω) :
    stabilizer T J ≤ normalizer (localWeakClosure T J Ω : Set G) := by
  let H := localGroup T J
  let S := (stabilizer T J).subgroupOf H
  let Γ := intersectionFamily H Ω
  have hSW : S ≤ normalizer (weakClosure S Γ : Set H) :=
    S.le_normalizer.trans (SubgroupFamily.normalizer_le_span_normalizer
      (intersectionFamily_elementary H hΩ).conjugationInvariant _)
  have h := (map_mono (f := H.subtype) hSW).trans (le_normalizer_map H.subtype)
  rw [show S.map H.subtype = stabilizer T J from
    map_subgroupOf_eq_of_le (show stabilizer T J ≤ H from le_sup_right)] at h
  exact h

variable [Finite G] in
/-- The subgroup whose equality with the whole group is the generation target. -/
def generationTarget (n : ℕ) (T : Sylow 2 G) (Ω : Set (Subgroup G)) : Subgroup G :=
  eFamilySubgroup n (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)

/-- The relative normalizer `N_J(W₀)`, retained in the ambient group. -/
def localNormalizer (T : Sylow 2 G) (J : Subgroup G) (Ω : Set (Subgroup G)) : Subgroup G :=
  J ⊓ normalizer (localWeakClosure T J Ω : Set G)

end CFSG.Quasithin.ChapterE.ChiefOrbit
