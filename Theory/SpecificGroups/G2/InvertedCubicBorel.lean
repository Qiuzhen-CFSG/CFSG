module
public import Theory.SpecificGroups.G2.SolvableSylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelAction
public import Theory.FieldTheory.BinaryTorusInvolution
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Inverted cubic obstructions in lifted even G₂ Borels

In a two-kernel cover of G₂(q), for even q > 2, a solvable subgroup
normalized by a Sylow two-subgroup lies in its normalizer. We construct
the actual normalizer map to the two-parameter split torus, with the
original Sylow as its kernel and a compatible action for every specified
automorphism preserving that Sylow.

The proved inner–field description makes the quotient action apply the
same field automorphism to both coordinates. A nontrivial field action
has at least two displacements, so the full torus displacement has at
least four elements. Thus displacement of size at most three forces
trivial action. The original 14.7.41 application supplies this bound
from its actual centralizing supplement and inverted cubic.

Source: Aschbacher–Smith 14.7.41(2), printed p.1061, refs/quasithin.pdf.
The octonion and torus formulas are from the attributed ATLAS development;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup
namespace Atlas.G2.InvertedCubicBorel
open EvenBorelTorus
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem field_eq_one_of_small_displacement (σ : F ≃+* F)
    (hc : Nat.card (((Units.mapEquiv σ.toMulEquiv).prodCongr
      (Units.mapEquiv σ.toMulEquiv)).toMonoidHom *
      (MonoidHom.id (Fˣ × Fˣ))⁻¹).range ≤ 3) : σ = 1 := by
  let d := FiniteField.BinaryTorusInvolution.displacement σ
  let τ := (Units.mapEquiv σ.toMulEquiv).prodCongr (Units.mapEquiv σ.toMulEquiv)
  let δ : (Fˣ × Fˣ) →* (Fˣ × Fˣ) := τ.toMonoidHom * (MonoidHom.id _)⁻¹
  have hr : δ.range = d.range.prod d.range := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y.1,rfl⟩,⟨y.2,rfl⟩⟩
    · rintro ⟨⟨y,hy⟩,⟨z,hz⟩⟩
      exact ⟨(y,z),Prod.ext hy hz⟩
  change Nat.card δ.range ≤ 3 at hc
  rw [hr,Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv,Nat.card_prod] at hc
  by_contra hσ
  have hne : d.range ≠ ⊥ := by
    intro hh
    apply hσ
    apply RingEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · let v := Units.mk0 x hx
      have hv : d v ∈ d.range := ⟨v,rfl⟩
      rw [hh,mem_bot] at hv
      have he : Units.map σ.toMonoidHom v = v := mul_inv_eq_one.mp hv
      exact congrArg Units.val he
  have ht : 1 < Nat.card d.range := (one_lt_card_iff_ne_bot _).mpr hne
  nlinarith

/-- Lift solvable Sylow-normalized subgroups through an arbitrary two-kernel. -/
theorem solvable_sylow_normalized_le_normalizer
    (hF : 2 < Nat.card F) (q : G →* Model F) (hq : Function.Surjective q)
    (P : Sylow 2 G) (hk : q.ker ≤ (P : Subgroup G))
    (A : Subgroup G) [Group.IsSolvable A]
    (hnorm : (P : Subgroup G) ≤ normalizer (A : Set G)) :
    A ≤ normalizer (P : Set G) := by
  let := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (A ⊔ (P : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes A P hnorm
  let H := (A ⊔ (P : Subgroup G)).map q
  have hs : Group.IsSolvable H :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  have hN := solvable_sylow_overgroup_normalizes hF (P.mapSurjective hq) H
    (map_mono le_sup_right) hs
  have hc := (map_le_iff_le_comap).mp hN
  change A ⊔ (P : Subgroup G) ≤
    (normalizer ((P : Subgroup G).map q : Set (Model F))).comap q at hc
  rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hk] at hc
  exact le_sup_left.trans hc

/-- The literal normalizer quotient and its original compatible actor. -/
theorem exists_normalizer_torus_action
    (hF : 2 < Nat.card F)
    (q : G →* Model F) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G)) (α : MulAut G) (β : MulAut (Model F))
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = P) :
    ∃ f : normalizer (P : Set G) →* (Fˣ × Fˣ), ∃ τ : MulAut (Fˣ × Fˣ),
      Function.Surjective f ∧
      (∀ x, f x = 1 ↔ (x : G) ∈ P) ∧
      (∀ x y : normalizer (P : Set G), α x = y → f y = τ (f x)) ∧
      (Nat.card (τ.toMonoidHom * (MonoidHom.id _)⁻¹).range ≤ 3 → τ = 1) := by
  let Q := P.mapSurjective hq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) Q (LieParabolicSetup.sylow (F := F))
  let e := MulAut.conj g
  let q' := e.toMonoidHom.comp q
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hU : (P : Subgroup G).map q' = unipotent := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  let N := normalizer (P : Set G)
  have hN : N.map q' = borel := by
    rw [P.normalizer_map_surjective q' hq']
    rw [hU,SylowNormalizer.normalizer_unipotent]
  let f₀ : N →* borel (K := F) := (q'.comp N.subtype).codRestrict borel
    (fun x => hN.le (mem_map_of_mem q' x.property))
  have hf₀ : Function.Surjective f₀ := by
    intro y
    obtain ⟨x,hx,heq⟩ := hN.ge y.property
    exact ⟨⟨x,hx⟩,Subtype.ext heq⟩
  let f := projection.comp f₀
  let β' := MulAut.congr e β
  have he' (x : G) : q' (α x) = β' (q' x) := by
    change e (q (α x)) = e (β (e.symm (e (q x))))
    rw [he,e.symm_apply_apply]
  have hstab : unipotent.map β'.toMonoidHom = unipotent := by
    have heq : β'.toMonoidHom.comp q' = q'.comp α.toMonoidHom :=
      MonoidHom.ext (fun x => (he' x).symm)
    rw [←hU,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  obtain ⟨z,hz⟩ := LieAutomorphismExtensions.semilinearAction_surjective hF β'
  have hzs : unipotent.map (LieAutomorphismExtensions.semilinearAction z).toMonoidHom =
      unipotent := by rw [hz]; exact hstab
  let τ := (Units.mapEquiv z.right.toMulEquiv).prodCongr (Units.mapEquiv z.right.toMulEquiv)
  refine ⟨f,τ,projection_surjective.comp hf₀,?_,?_,?_⟩
  · intro x
    change f₀ x ∈ (projection (F := F)).ker ↔ _
    rw [projection_ker]
    change q' x ∈ unipotent ↔ _
    rw [←hU]
    change x.val ∈ ((P : Subgroup G).map q').comap q' ↔ _
    rw [comap_map_eq_self (show q'.ker ≤ (P : Subgroup G) from fun x hx =>
      hk (e.map_eq_one_iff.mp hx))]
    rfl
  · intro x y hxy
    have hh := projection_semilinear z hzs (f₀ x)
    change projection (f₀ y) = τ (projection (f₀ x))
    change projection _ = τ (projection (f₀ x)) at hh
    rw [←hh]
    congr 1
    apply Subtype.ext
    change q' y = LieAutomorphismExtensions.semilinearAction z (q' x)
    rw [hz,←hxy,he']
  · intro hc
    have hσ := field_eq_one_of_small_displacement z.right hc
    apply MulEquiv.ext
    intro x
    change (Units.map z.right.toMonoidHom x.1,Units.map z.right.toMonoidHom x.2) = x
    rw [hσ]
    rfl

end Atlas.G2.InvertedCubicBorel
