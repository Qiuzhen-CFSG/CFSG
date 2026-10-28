module
public import Theory.Representation.RankOneSymplectic.Basic

/-!
# Normal rank-one generated subgroups in symplectic four-space

The restriction to a nontrivial normal subgroup has no fixed vectors. Choose
an irreducible constituent. Rank-one generation makes it nondegenerate and
makes each distinct ambient conjugate orthogonal to it. In dimension four,
a proper such constituent and its orthogonal complement both have dimension
two; every ambient operator preserves or exchanges them.

This proves the normal-closure irreducibility reduction of Aschbacher--Smith
G.4.6--7, printed pp.339--340, over the original coefficient field. The later
identification of the irreducible subgroup is a separate recognition theorem.
-/

public noncomputable section
open Subgroup Module
namespace Representation.RankOneSymplectic
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

/-- A nontrivial normal subgroup of a faithful irreducible action has no
fixed vector. -/
theorem normal_invariants_eq_bot (ρ : Representation F G V)
    [ρ.IsIrreducible] (hf : Function.Injective ρ)
    (N : Subgroup G) [N.Normal] (hn : N≠⊥) : invariants (ρ.comp N.subtype)=⊥ := by
  by_contra hne
  have hk := le_ker_of_normal_invariants_ne_bot ρ N hne
  apply hn
  apply bot_unique
  intro g hg
  change g=1
  exact hf ((hk hg).trans ρ.map_one.symm)

/-- Isometries carry orthogonal complements to the literal orthogonal
complement of the image. -/
theorem map_orthogonal (ρ : Representation F G V)
    (B : LinearMap.BilinForm F V) (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y)
    (U : Submodule F V) (g : G) :
    (B.orthogonal U).map (ρ g)=B.orthogonal (U.map (ρ g)) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩ z ⟨w,hw,rfl⟩
    exact (hp g w y).trans (hy w hw)
  · intro hx
    refine ⟨ρ g⁻¹ x,?_,ρ.self_inv_apply g x⟩
    intro u hu
    have h := hx (ρ g u) ⟨u,hu,rfl⟩
    have he := hp g u (ρ g⁻¹ x)
    rw [ρ.self_inv_apply] at he
    exact he.symm.trans h

variable [FiniteDimensional F V]

/-- A normal rank-one generated subgroup in an irreducible symplectic
four-space is irreducible or gives an orthogonal two-plane system. -/
theorem normal_four_dichotomy (ρ : Representation F G V) [ρ.IsIrreducible]
    (hf : Function.Injective ρ) (B : LinearMap.BilinForm F V)
    (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y) (hdim : finrank F V=4)
    (N : Subgroup G) [N.Normal] (hn : N≠⊥)
    (D : Set N) (hgen : closure D=⊤)
    (hrank : ∀ d∈D, finrank F (LinearMap.range (ρ d-LinearMap.id))=1) :
    Representation.IsIrreducible (ρ.comp N.subtype) ∨
      ∃ U : Submodule F V,
        IsCompl U (B.orthogonal U) ∧ finrank F U=2 ∧
        finrank F (B.orthogonal U)=2 ∧
        (∀ g,
          (U.map (ρ g)=U ∧ (B.orthogonal U).map (ρ g)=B.orthogonal U) ∨
          (U.map (ρ g)=B.orthogonal U ∧ (B.orthogonal U).map (ρ g)=U)) := by
  let σ : Representation F N V := ρ.comp N.subtype
  by_cases hi : σ.IsIrreducible
  · exact Or.inl hi
  right
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨J,hJ⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
  let : J.toRepresentation.IsIrreducible := hJ
  have ha : IsAtom J := (Subrepresentation.irreducible_iff_isAtom J).mp hJ
  have hfix : invariants σ=⊥ := normal_invariants_eq_bot ρ hf N hn
  have hnd := constituent_nondegenerate σ B halt hB (fun n => hp n) D hgen hrank hfix J
  have hc := B.isCompl_orthogonal_of_restrict_nondegenerate halt.isRefl hnd
  have hne : J.toSubmodule≠⊥ := fun h => ha.ne_bot (Subrepresentation.toSubmodule_injective h)
  have hnt : J.toSubmodule≠⊤ := by
    intro h
    have he : J=⊤ := Subrepresentation.toSubmodule_injective h
    have ht : IsAtom (⊤ : Subrepresentation σ) := he ▸ ha
    exact hi ((isSimpleOrder_iff_isAtom_top).mpr ht)
  have hpos : 0<finrank F J.toSubmodule := by
    have : Nontrivial J.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne
    exact Module.finrank_pos
  have hlt : finrank F J.toSubmodule<4 := by
    have h := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hnt)
    simpa only [finrank_top,hdim] using h
  have heven := AlternatingForm.even_finrank (B.restrict J.toSubmodule)
    (fun x => halt x.val) hnd
  have hjdim : finrank F J.toSubmodule=2 := by
    obtain ⟨r,hr⟩ := heven
    omega
  have hperp : finrank F (B.orthogonal J.toSubmodule)=2 := by
    rw [B.finrank_orthogonal hB,hdim,hjdim]
  refine ⟨J.toSubmodule,hc,hjdim,hperp,fun g => ?_⟩
  let K := conjugateSubrepresentationOrderIso ρ N g J
  have hKa : IsAtom K := ((conjugateSubrepresentationOrderIso ρ N g).isAtom_iff J).mpr ha
  have hK : K.toSubmodule=J.toSubmodule.map (ρ g) :=
    conjugateSubrepresentationOrderIso_toSubmodule ρ N g J
  have hmap : J.toSubmodule.map (ρ g)=J.toSubmodule ∨
      J.toSubmodule.map (ρ g)=B.orthogonal J.toSubmodule := by
    by_cases he : K=J
    · exact Or.inl (hK.symm.trans (congrArg Subrepresentation.toSubmodule he))
    right
    have hd : Disjoint J.toSubmodule K.toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule (ha.disjoint_of_ne hKa (Ne.symm he)).eq_bot
    have ho := disjoint_orthogonal σ B (fun n => hp n) D hgen hrank hfix J K hd
    have hle : K.toSubmodule≤B.orthogonal J.toSubmodule := fun v hv u hu => ho u hu v hv
    have hkd : finrank F K.toSubmodule=2 := by
      rw [hK]
      exact (Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective J.toSubmodule).finrank_eq.symm.trans hjdim
    exact hK.symm.trans (Submodule.eq_of_le_of_finrank_eq hle (hkd.trans hperp.symm))
  rcases hmap with he | he
  · exact Or.inl ⟨he,by rw [map_orthogonal ρ B hp,he]⟩
  · exact Or.inr ⟨he,by rw [map_orthogonal ρ B hp,he,B.orthogonal_orthogonal hB halt.isRefl]⟩

end Representation.RankOneSymplectic
