module

public import Theory.Representation.SpecialLinearRestriction
public import Theory.GroupTheory.PerfectCentralCover
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy

/-!
# Small representations of alternating central covers over F₁₆

Every two-dimensional representation of a perfect central cover of A₆, A₇,
or A₈ is trivial. Every three-dimensional representation of such a cover
of A₇ or A₈ is trivial. The actual surjective central map is retained, so
exceptional cubic covers are included. No exclusion is asserted for A₅ in
degree two or for the genuine triple cover of A₆ in degree three.

Perfectness puts the image in the special linear group. In degree two,
9 divides the alternating quotient's order but not |SL₂(16)| = 4080.
In degree three, involution centralizers in PSL₃(16) have order 20480,
so PSL₃(16) has no element of order six. Both A₇ and A₈ have such elements.
Every nontrivial image of a perfect central cover still maps onto its simple
quotient; taking powers lifts element orders to the finite image. A trivial
projective image is central, hence trivial by perfectness. Neither argument
requires a degree table, irreducibility, or a bound on the covering kernel.

Source: the small-overgroup inspection in Aschbacher–Smith, combined manuscript
(1 March 2004), proof of Proposition 8.2.8(1), printed p.719 (PDF p.736).
The matrix involution centralizers are the concrete ones constructed in
`Theory.SpecificGroups.PSL3.EvenInnerCentralizers`.
-/

public section
namespace Representation.AlternatingCentralCoverSmallSixteen

open Subgroup
open scoped MatrixGroups
section CoverImages
variable {L S H : Type*} [Group L] [Group S] [Group H] [IsSimpleGroup S]
private theorem ker_le_cover_ker (c : PerfectCentralCovering.Cover L S) (f : L →* H) (hf : f ≠ 1) :
    f.ker ≤ c.toMonoidHom.ker := by
  let := c.isPerfect
  have hn : (f.ker.map c.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ c.surjective
  rcases hn.eq_bot_or_eq_top with hb | ht
  · intro x hx
    have hm := mem_map_of_mem c.toMonoidHom hx
    rwa [hb, mem_bot] at hm
  · have he := congrArg (Subgroup.comap c.toMonoidHom) ht
    have hs : f.ker ⊔ c.toMonoidHom.ker = ⊤ := by
      simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using he
    have hab : IsMulCommutative c.toMonoidHom.ker :=
      ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (c.ker_le_center y.property) x)⟩⟩
    have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hs hab
    have hk : f.ker = ⊤ := top_unique (by simpa using hc)
    exact (hf (MonoidHom.ker_eq_top_iff.mp hk)).elim

private theorem exists_cover_image_surjection (c : PerfectCentralCovering.Cover L S) (f : L →* H)
    (hf : f ≠ 1) : ∃ q : f.range →* S, Function.Surjective q := by
  let q := f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective
    ⟨c.toMonoidHom, by simpa using ker_le_cover_ker c f hf⟩
  refine ⟨q, ?_⟩
  intro s
  obtain ⟨l, rfl⟩ := c.surjective s
  exact ⟨f.rangeRestrict l, by simp [q]⟩

private theorem card_dvd_of_nontrivial_cover_image [Finite H] (c : PerfectCentralCovering.Cover L S) (f : L →* H)
    (hf : f ≠ 1) : Nat.card S ∣ Nat.card H := by
  obtain ⟨q, hq⟩ := exists_cover_image_surjection c f hf
  exact (Subgroup.card_dvd_of_surjective q hq).trans (Subgroup.card_subgroup_dvd_card f.range)

private theorem exists_image_element_of_order [Finite H] (c : PerfectCentralCovering.Cover L S) (f : L →* H)
    (hf : f ≠ 1) (s : S) : ∃ h : H, orderOf h = orderOf s := by
  obtain ⟨q, hq⟩ := exists_cover_image_surjection c f hf
  obtain ⟨l, hl⟩ := hq s
  have hd : orderOf s ∣ orderOf l := hl ▸ orderOf_map_dvd q l
  refine ⟨(l : H) ^ (orderOf l / orderOf s), ?_⟩
  rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]
  exact orderOf_pow_orderOf_div (ne_of_gt (orderOf_pos l)) hd
end CoverImages

section SmallLinearGroups
variable {F : Type*} [Field F] [Finite F]

private theorem card_det_kernel_two (hF : Nat.card F = 16) :
    Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker = 4080 := by
  let := Fintype.ofFinite F
  let d := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  have hr : Nat.card d.range = 15 := by
    rw [MonoidHom.range_eq_top_of_surjective _ Matrix.GeneralLinearGroup.det_surjective]
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv, Nat.card_units, hF]
  have hF' : Fintype.card F = 16 := by rwa [← Nat.card_eq_fintype_card]
  have hc := d.ker.index_mul_card
  rw [Subgroup.index_ker, hr, Matrix.card_GL_field] at hc
  norm_num [Fin.prod_univ_two, hF'] at hc
  change Nat.card d.ker = 4080
  change 15 * Nat.card d.ker = 61200 at hc
  omega

private theorem not_order_six_projective_three (hF : Nat.card F = 16) (g : PSL(3,F)) (hg : orderOf g = 6) : False := by
  have ht : orderOf (g ^ 3) = 2 := by rw [orderOf_pow, hg]; decide
  have htne : g ^ 3 ≠ 1 := by intro h; simp [h] at ht
  have ht2 : (g ^ 3) ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one _
  let e := Matrix.PSL3.EvenInnerCentralizers.involutionCentralizerEquiv F
    (n := 4) (by decide) hF (g ^ 3) htne ht2
  have hc : Nat.card (Subgroup.centralizer ({g ^ 3} : Set PSL(3,F))) = 20480 := by
    rw [Nat.card_congr e.toEquiv,
      Matrix.PSL3.EvenInnerCentralizers.MarkedInvariants.centralizer_card F
        (n := 4) hF (by decide) (by decide)]
    norm_num
  let a : Subgroup.centralizer ({g ^ 3} : Set PSL(3,F)) :=
    ⟨g, by rw [Subgroup.mem_centralizer_singleton_iff]; exact (Commute.self_pow g 3).eq⟩
  have hd := orderOf_dvd_natCard a
  rw [Subgroup.orderOf_mk, hg, hc] at hd
  norm_num at hd
end SmallLinearGroups


section Representations
open Matrix
variable {L F V : Type*} [Group L] [Field F] [Finite F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private noncomputable def specialLinearAction [Group.IsPerfect L] (ρ : Representation F L V) {d : ℕ}
    (b : Module.Basis (Fin d) F V) : L →* SL(d,F) where
  toFun g := ⟨LinearMap.toMatrix b b (ρ g), by
    rw [LinearMap.det_toMatrix, Representation.det_eq_one_of_perfect]⟩
  map_one' := by apply Subtype.ext; simp only [map_one, LinearMap.toMatrix_one]; rfl
  map_mul' g h := by apply Subtype.ext; simp only [map_mul, LinearMap.toMatrix_mul]; rfl

omit [Finite F] [FiniteDimensional F V] in
private theorem representation_eq_one_of_specialLinearAction [Group.IsPerfect L] (ρ : Representation F L V) {d : ℕ}
    (b : Module.Basis (Fin d) F V) (h : specialLinearAction ρ b = 1) : ρ = 1 := by
  apply MonoidHom.ext
  intro g
  apply (LinearMap.toMatrix b b).injective
  have he := congrArg Subtype.val (DFunLike.congr_fun h g)
  change LinearMap.toMatrix b b (ρ g) = (1 : Matrix (Fin d) (Fin d) F) at he
  change LinearMap.toMatrix b b (ρ g) = LinearMap.toMatrix b b 1
  rw [LinearMap.toMatrix_one]
  exact he

/-- A perfect central cover of A₆, A₇ or A₈ acts trivially on every F₁₆-plane. -/
theorem representation_eq_one_of_finrank_two (m : ℕ) (hm : m = 6 ∨ m = 7 ∨ m = 8)
    (c : PerfectCentralCovering.Cover L (alternatingGroup (Fin m)))
    (ρ : Representation F L V) (hF : Nat.card F = 16) (hd : Module.finrank F V = 2) :
    ρ = 1 := by
  let := c.isPerfect
  let : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rcases hm with rfl | rfl | rfl <;> simp)
  let b := Module.finBasisOfFinrankEq F V hd
  let f := specialLinearAction ρ b
  apply representation_eq_one_of_specialLinearAction ρ b
  by_contra hn
  let g := Matrix.SpecialLinearGroup.toGL.comp f
  let d := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)
  let g' : L →* d.ker := g.codRestrict d.ker (fun x => Matrix.SpecialLinearGroup.coeToGL_det (f x))
  have hgne : g' ≠ 1 := by
    intro he
    apply hn
    apply MonoidHom.ext
    intro x
    apply Matrix.SpecialLinearGroup.toGL_injective
    have hh := congrArg Subtype.val (DFunLike.congr_fun he x)
    change Matrix.SpecialLinearGroup.toGL (f x) = 1 at hh
    change Matrix.SpecialLinearGroup.toGL (f x) = Matrix.SpecialLinearGroup.toGL 1
    rw [map_one]
    exact hh
  have hc := card_dvd_of_nontrivial_cover_image c g' hgne
  rw [card_det_kernel_two hF] at hc
  have h9 : 9 ∣ Nat.card (alternatingGroup (Fin m)) := by
    rcases hm with rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup, Nat.card_fin] <;> norm_num
  have := h9.trans hc
  norm_num at this

private def sixSeven : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * (Equiv.swap 4 5 * Equiv.swap 5 6), by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩


private def sixEight : alternatingGroup (Fin 8) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3 * (Equiv.swap 4 5 * Equiv.swap 5 6), by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩
private theorem alternating_has_order_six (m : ℕ) (hm : m = 7 ∨ m = 8) :
    ∃ s : alternatingGroup (Fin m), orderOf s = 6 := by
  rcases hm with rfl | rfl
  · refine ⟨sixSeven, (orderOf_eq_iff (by decide : 0 < 6)).mpr ?_⟩
    decide +kernel
  · refine ⟨sixEight, (orderOf_eq_iff (by decide : 0 < 6)).mpr ?_⟩
    decide +kernel

/-- A perfect central cover of A₇ or A₈ acts trivially on every F₁₆ three-space. -/
theorem representation_eq_one_of_finrank_three (m : ℕ) (hm : m = 7 ∨ m = 8)
    (c : PerfectCentralCovering.Cover L (alternatingGroup (Fin m)))
    (ρ : Representation F L V) (hF : Nat.card F = 16) (hd : Module.finrank F V = 3) :
    ρ = 1 := by
  let := c.isPerfect
  let : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rcases hm with rfl | rfl <;> simp)
  let b := Module.finBasisOfFinrankEq F V hd
  let f := specialLinearAction ρ b
  let g := (Matrix.PSL3.projection F).comp f
  have hg : g = 1 := by
    by_contra hn
    obtain ⟨s, hs⟩ := alternating_has_order_six m hm
    obtain ⟨x, hx⟩ := exists_image_element_of_order c g hn s
    exact not_order_six_projective_three hF x (hx.trans hs)
  have hfcentral (l : L) : f l ∈ Subgroup.center SL(3,F) := by
    rw [← Matrix.PSL3.projection_ker, MonoidHom.mem_ker]
    exact DFunLike.congr_fun hg l
  let fc : L →* Subgroup.center SL(3,F) := f.codRestrict _ hfcentral
  have hfc : fc = 1 := by
    apply MonoidHom.ext
    intro l
    let : Group.IsPerfect fc.range := Group.IsPerfect.range fc
    exact congrArg Subtype.val (Subsingleton.elim (fc.rangeRestrict l) 1)
  apply representation_eq_one_of_specialLinearAction ρ b
  apply MonoidHom.ext
  intro l
  exact congrArg Subtype.val (DFunLike.congr_fun hfc l)


/-- The same exclusions for homomorphisms to linear automorphisms, with the
original vector space and covering map retained. -/
theorem linearAction_eq_one (m : ℕ)
    (c : PerfectCentralCovering.Cover L (alternatingGroup (Fin m)))
    (α : L →* (V ≃ₗ[F] V)) (hF : Nat.card F = 16)
    (hd : ((m = 6 ∨ m = 7 ∨ m = 8) ∧ Module.finrank F V = 2) ∨
      ((m = 7 ∨ m = 8) ∧ Module.finrank F V = 3)) : α = 1 := by
  let ρ : Representation F L V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp α
  have hρ : ρ = 1 := by
    rcases hd with ⟨hm, hd⟩ | ⟨hm, hd⟩
    · exact representation_eq_one_of_finrank_two m hm c ρ hF hd
    · exact representation_eq_one_of_finrank_three m hm c ρ hF hd
  apply MonoidHom.ext
  intro l
  apply LinearEquiv.ext
  intro v
  exact DFunLike.congr_fun (DFunLike.congr_fun hρ l) v

end Representations

end Representation.AlternatingCentralCoverSmallSixteen
