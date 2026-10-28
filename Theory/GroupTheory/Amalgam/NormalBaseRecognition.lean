module

public import Theory.GroupTheory.NormalSupplementGluing
public import Theory.GroupTheory.Amalgam.RankTwo
public import Theory.GroupTheory.Amalgam.NormalBaseAction

/-!
# Reconstructing endpoints from a normal base and the marked overlap

An isomorphism on a normal local subgroup and a homomorphism on a supplement
extend to the endpoint when they agree on the intersection and preserve
conjugation. The inverse image of the model normal subgroup detects exactly
that intersection, so the extension is injective. Its image is the join of
the two prescribed images. Applying the existing normal-supplement gluing
theorem on both sides yields an isomorphism of inclusion amalgams with the
original overlap map and both normal-base restrictions retained.

This is the reconstruction step for the normal two-perfect base in
Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.8) and §3,
used by the M₁₂ extension alternatives of Aschbacher--Smith F.1.12.
-/

public section
noncomputable section
open Subgroup

namespace Theory.GroupTheory.RankTwoAmalgam.NormalBaseRecognition
variable {G H : Type*} [Group G] [Group H]

/-- Restrict the target of the existing normal-supplement gluing theorem to
the join of the two specified images. -/
theorem exists_endpoint_equiv (N T : Subgroup G) [N.Normal]
    (R : Subgroup H) (e : N ≃* R) (v : T →* H)
    (hgen : N ⊔ T = ⊤)
    (hinter : ∀ t : T, v t ∈ R ↔ (t : G) ∈ N)
    (hagree : ∀ (t : T) (ht : (t : G) ∈ N), (e ⟨t, ht⟩ : H) = v t)
    (hconj : ∀ (t : T) (n : N),
      (e (MulAut.conjNormal (t : G) n) : H) = v t * e n * (v t)⁻¹) :
    ∃ E : G ≃* (R ⊔ v.range : Subgroup H),
      (∀ n : N, (E n : H) = e n) ∧ ∀ t : T, (E t : H) = v t := by
  let K : Subgroup H := R ⊔ v.range
  let R' : Subgroup K := R.subgroupOf K
  let e' : N ≃* R' := e.trans (subgroupOfEquivOfLe (show R ≤ K from le_sup_left)).symm
  let v' : T →* K := v.codRestrict K (fun t =>
    (show v.range ≤ K from le_sup_right) ⟨t, rfl⟩)
  have hv : K.subtype.comp v' = v := by ext t; rfl
  have htarget : R' ⊔ v'.range = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, ← MonoidHom.range_comp, hv,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    change (R.subgroupOf K).map K.subtype ⊔ v.range = K
    rw [map_subgroupOf_eq_of_le (show R ≤ K from le_sup_left)]
  obtain ⟨E, hE, hT⟩ := NormalSupplementGluing.exists_equiv N T R' e' v' hgen htarget
    hinter (fun t ht => Subtype.ext (hagree t ht))
    (fun t n => Subtype.ext (hconj t n))
  refine ⟨E, ?_, ?_⟩
  · intro n
    exact congrArg Subtype.val (hE n)
  · intro t
    exact congrArg Subtype.val (hT t)

private theorem restrict_overlap_range (A T : Subgroup G) (hTA : T ≤ A) (ρ : T →* H) :
    (ρ.comp (subgroupOfEquivOfLe hTA).toMonoidHom).range = ρ.range := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨subgroupOfEquivOfLe hTA t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(subgroupOfEquivOfLe hTA).symm t,
      congrArg ρ ((subgroupOfEquivOfLe hTA).apply_symm_apply t)⟩

/-- A normal-base endpoint identification extends across the literal common
overlap; the resulting endpoint has precisely the generated target image. -/
theorem exists_local_equiv (N A T : Subgroup G) [N.Normal]
    (hTA : T ≤ A) (R : Subgroup H) (e : N.subgroupOf A ≃* R) (ρ : T →* H)
    (hgen : N.subgroupOf A ⊔ T.subgroupOf A = ⊤)
    (hinter : ∀ t : T, ρ t ∈ R ↔ (t : G) ∈ N)
    (hagree : ∀ (t : T) (ht : (t : G) ∈ N),
      (e ⟨⟨t, hTA t.property⟩, ht⟩ : H) = ρ t)
    (hconj : ∀ (t : T) (n : N.subgroupOf A),
      (e (MulAut.conjNormal (⟨t, hTA t.property⟩ : A) n) : H) =
        ρ t * e n * (ρ t)⁻¹) :
    ∃ E : A ≃* (R ⊔ ρ.range : Subgroup H),
      (∀ n : N.subgroupOf A, (E n : H) = e n) ∧
      ∀ t : T, (E (Subgroup.inclusion hTA t) : H) = ρ t := by
  let v : T.subgroupOf A →* H := ρ.comp (subgroupOfEquivOfLe hTA).toMonoidHom
  obtain ⟨E, hE, hT⟩ := exists_endpoint_equiv (N.subgroupOf A) (T.subgroupOf A) R e v
    hgen (fun t => hinter (subgroupOfEquivOfLe hTA t))
    (fun t ht => hagree (subgroupOfEquivOfLe hTA t) ht)
    (fun t n => hconj (subgroupOfEquivOfLe hTA t) n)
  have hv : v.range = ρ.range := restrict_overlap_range A T hTA ρ
  let E' : A ≃* (R ⊔ ρ.range : Subgroup H) :=
    E.trans (MulEquiv.subgroupCongr (congrArg (R ⊔ ·) hv))
  refine ⟨E', hE, ?_⟩
  intro t
  exact hT ((subgroupOfEquivOfLe hTA).symm t)

/-- Interchanging the ambient and subgroup roles preserves the literal element. -/
@[expose] def subgroupOfSwap (N A : Subgroup G) : N.subgroupOf A ≃* A.subgroupOf N where
  toFun x := ⟨⟨x.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A normal supplement restricts to every subgroup containing the supplement. -/
theorem local_sup_eq_top (N A T : Subgroup G) [N.Normal]
    (hTA : T ≤ A) (hgen : N ⊔ T = ⊤) :
    N.subgroupOf A ⊔ T.subgroupOf A = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨n, hn, t, ht, he⟩ := Subgroup.mem_sup_of_normal_left.mp
    (show (a : G) ∈ N ⊔ T by rw [hgen]; trivial)
  have hnA : n ∈ A := by
    have hnt : n = (a : G) * t⁻¹ := (eq_mul_inv_iff_mul_eq).mpr he
    rw [hnt]
    exact A.mul_mem a.property (A.inv_mem (hTA ht))
  have ha : (⟨n, hnA⟩ : A) * ⟨t, hTA ht⟩ = a := Subtype.ext he
  rw [← ha]
  exact (N.subgroupOf A ⊔ T.subgroupOf A).mul_mem
    (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right ht)

/-- Reconstruct both original endpoints from a marked normal base and a
faithful overlap map, retaining the overlap and both normal-base maps. -/
theorem exists_iso (N A B : Subgroup G) [N.Normal]
    (R₀ R₁ : Subgroup H)
    (e₀ : A.subgroupOf N ≃* R₀) (e₁ : B.subgroupOf N ≃* R₁)
    (ρ : (A ⊓ B : Subgroup G) →* H) (hρ : Function.Injective ρ)
    (hgen : N ⊔ (A ⊓ B) = ⊤)
    (hinter₀ : ∀ t : (A ⊓ B : Subgroup G), ρ t ∈ R₀ ↔ (t : G) ∈ N)
    (hinter₁ : ∀ t : (A ⊓ B : Subgroup G), ρ t ∈ R₁ ↔ (t : G) ∈ N)
    (hagree₀ : ∀ s : (A.subgroupOf N ⊓ B.subgroupOf N : Subgroup N),
      ρ ⟨s.val.val, s.property⟩ = (e₀ (Subgroup.inclusion inf_le_left s) : H))
    (hagree₁ : ∀ s : (A.subgroupOf N ⊓ B.subgroupOf N : Subgroup N),
      ρ ⟨s.val.val, s.property⟩ = (e₁ (Subgroup.inclusion inf_le_right s) : H))
    (hconj₀ : ∀ (t : (A ⊓ B : Subgroup G)) (n : A.subgroupOf N),
      (e₀ ((normalOverlapAction N A B t).left n) : H) = ρ t * e₀ n * (ρ t)⁻¹)
    (hconj₁ : ∀ (t : (A ⊓ B : Subgroup G)) (n : B.subgroupOf N),
      (e₁ ((normalOverlapAction N A B t).right n) : H) = ρ t * e₁ n * (ρ t)⁻¹) :
    ∃ E : Iso (ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right)
      (ofSubgroups (R₀ ⊔ ρ.range) ρ.range (R₁ ⊔ ρ.range) le_sup_right le_sup_right),
      E.middle = MonoidHom.ofInjective hρ ∧
      (∀ n : A.subgroupOf N, (E.left ⟨n.val.val, n.property⟩ : H) = e₀ n) ∧
      (∀ n : B.subgroupOf N, (E.right ⟨n.val.val, n.property⟩ : H) = e₁ n) := by
  let f₀ := (subgroupOfSwap N A).trans e₀
  let f₁ := (subgroupOfSwap N B).trans e₁
  obtain ⟨E₀, hE₀, hT₀⟩ := exists_local_equiv N A (A ⊓ B) inf_le_left R₀ f₀ ρ
    (local_sup_eq_top N A (A ⊓ B) inf_le_left hgen) hinter₀
    (fun t ht => (hagree₀ ⟨⟨t, ht⟩, t.property⟩).symm)
    (fun t n => hconj₀ t (subgroupOfSwap N A n))
  obtain ⟨E₁, hE₁, hT₁⟩ := exists_local_equiv N B (A ⊓ B) inf_le_right R₁ f₁ ρ
    (local_sup_eq_top N B (A ⊓ B) inf_le_right hgen) hinter₁
    (fun t ht => (hagree₁ ⟨⟨t, ht⟩, t.property⟩).symm)
    (fun t n => hconj₁ t (subgroupOfSwap N B n))
  let E : Iso (ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right)
      (ofSubgroups (R₀ ⊔ ρ.range) ρ.range (R₁ ⊔ ρ.range) le_sup_right le_sup_right) :=
    { left := E₀
      middle := MonoidHom.ofInjective hρ
      right := E₁
      left_commutes := fun t => Subtype.ext (hT₀ t)
      right_commutes := fun t => Subtype.ext (hT₁ t) }
  exact ⟨E, rfl, fun n => hE₀ ((subgroupOfSwap N A).symm n),
    fun n => hE₁ ((subgroupOfSwap N B).symm n)⟩

end Theory.GroupTheory.RankTwoAmalgam.NormalBaseRecognition
