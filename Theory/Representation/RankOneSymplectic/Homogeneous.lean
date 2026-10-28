module
public import Theory.Representation.RankOneSymplectic.Homogeneous.Lines

/-!
# Homogeneous normal restriction for symplectic rank-one generators

In an irreducible symplectic module of dimension greater than two generated
by involutory rank-one isometries, every normal-subgroup restriction is isotypic.
If a proper isotypic component moves, displacement injectivity makes it a line.
Its unique dual line partner then makes their two-dimensional sum invariant
under every generator, contradicting ambient irreducibility.

This proves the homogeneous-restriction consequence of the primitive standing
reduction after Aschbacher--Smith G.4.6, printed pp.339--340, directly over the
original coefficient field. It is used in the G.4.9 normal-subgroup analysis.
-/

public noncomputable section
open Subgroup Module
open scoped MonoidAlgebra
namespace Representation.RankOneSymplectic.Homogeneous
open CubicClifford.Inertia
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

omit [FiniteDimensional F V] in
theorem conjugate_component_self (ρ : Representation F G V) (N : Subgroup G) [N.Normal]
    (A : Subrepresentation (ρ.comp N.subtype)) (hc : component (ρ.comp N.subtype) A=A)
    (g : G) : component (ρ.comp N.subtype) (conjugateSubrepresentationOrderIso ρ N g A)=
      conjugateSubrepresentationOrderIso ρ N g A := by
  rw [←conjugate_component,hc]

omit [FiniteDimensional F V] in
theorem conjugate_irreducible (ρ : Representation F G V) (N : Subgroup G) [N.Normal]
    (A : Subrepresentation (ρ.comp N.subtype)) (hA : A.toRepresentation.IsIrreducible)
    (g : G) : (conjugateSubrepresentationOrderIso ρ N g A).toRepresentation.IsIrreducible :=
  (Subrepresentation.irreducible_iff_isAtom _).mpr
    (((conjugateSubrepresentationOrderIso ρ N g).isAtom_iff A).mpr
      ((Subrepresentation.irreducible_iff_isAtom A).mp hA))

theorem line_image_eq_or_paired (ρ : Representation F G V) (N : Subgroup G) [N.Normal]
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y)
    (A C : Subrepresentation (ρ.comp N.subtype)) [A.toRepresentation.IsIrreducible]
    [C.toRepresentation.IsIrreducible]
    (hA : finrank F A.toSubmodule=1) (hC : finrank F C.toSubmodule=1)
    (hcA : component (ρ.comp N.subtype) A=A) (hcC : component (ρ.comp N.subtype) C=C)
    (hpair : pairing (ρ.comp N.subtype) B (fun n => hp n) C A≠0)
    (d : G) (hd : d*d=1) (hr : finrank F (LinearMap.range (ρ d-LinearMap.id))=1) :
    conjugateSubrepresentationOrderIso ρ N d A=A ∨
      conjugateSubrepresentationOrderIso ρ N d A=C := by
  by_cases he : conjugateSubrepresentationOrderIso ρ N d A=A
  · exact Or.inl he
  right
  let : (conjugateSubrepresentationOrderIso ρ N d A).toRepresentation.IsIrreducible :=
    conjugate_irreducible ρ N A inferInstance d
  exact unique_paired_line_component (ρ.comp N.subtype) B (fun n => hp n) A _ C
    hA ((conjugate_finrank ρ N A d).trans hA) hC
    (conjugate_component_self ρ N A hcA d) hcC
    (moved_line_pairing_ne_zero ρ N B halt hB hp A hA d hd hr he) hpair

theorem no_line_component (ρ : Representation F G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal]
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y) (hdim : 2<finrank F V)
    (D : Set G) (hgen : closure D=⊤)
    (hsq : ∀ d∈D, d*d=1)
    (hrank : ∀ d∈D, finrank F (LinearMap.range (ρ d-LinearMap.id))=1)
    (A : Subrepresentation (ρ.comp N.subtype)) [A.toRepresentation.IsIrreducible]
    (hA : finrank F A.toSubmodule=1)
    (hcA : component (ρ.comp N.subtype) A=A) : False := by
  have ha := (Subrepresentation.irreducible_iff_isAtom A).mp inferInstance
  have ht : A≠⊤ := by
    intro h
    have hh : finrank F A.toSubmodule=finrank F V := by rw [h]; exact finrank_top F V
    omega
  obtain ⟨t,htD,htA⟩ := exists_moving_generator ρ N D hgen A ha.ne_bot ht
  let C := conjugateSubrepresentationOrderIso ρ N t A
  let : C.toRepresentation.IsIrreducible := conjugate_irreducible ρ N A inferInstance t
  have hC : finrank F C.toSubmodule=1 := (conjugate_finrank ρ N A t).trans hA
  have hcC : component (ρ.comp N.subtype) C=C := conjugate_component_self ρ N A hcA t
  have htt : conjugateSubrepresentationOrderIso ρ N t C=A := by
    change conjugateSubrepresentationOrderIso ρ N t
      (conjugateSubrepresentationOrderIso ρ N t A)=A
    rw [←conjugateSubrepresentationOrderIso_mul,hsq t htD,conjugateSubrepresentationOrderIso_one]
  have hCA : pairing (ρ.comp N.subtype) B (fun n => hp n) C A≠0 :=
    moved_line_pairing_ne_zero ρ N B halt hB hp A hA t (hsq t htD) (hrank t htD) htA
  have hAC : pairing (ρ.comp N.subtype) B (fun n => hp n) A C≠0 := by
    have hm : conjugateSubrepresentationOrderIso ρ N t C≠C := fun h => htA (h.symm.trans htt)
    have h := moved_line_pairing_ne_zero ρ N B halt hB hp C hC t (hsq t htD) (hrank t htD) hm
    rwa [htt] at h
  have hstable (d : G) (hd : d∈D) :
      conjugateSubrepresentationOrderIso ρ N d (A⊔C)=A⊔C := by
    let c := conjugateSubrepresentationOrderIso ρ N d
    have h1 := line_image_eq_or_paired ρ N B halt hB hp A C hA hC hcA hcC hCA d (hsq d hd) (hrank d hd)
    have h2 := line_image_eq_or_paired ρ N B halt hB hp C A hC hA hcC hcA hAC d (hsq d hd) (hrank d hd)
    have h1' : c A≤A⊔C := by
      rcases h1 with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    have h2' : c C≤A⊔C := by
      rcases h2 with h | h
      · rw [h]; exact le_sup_right
      · rw [h]; exact le_sup_left
    have hle : c (A⊔C)≤A⊔C := by
      rw [c.map_sup]
      exact sup_le h1' h2'
    apply le_antisymm hle
    have hcc : c (c (A⊔C))=A⊔C := by
      change conjugateSubrepresentationOrderIso ρ N d
        (conjugateSubrepresentationOrderIso ρ N d (A⊔C))=A⊔C
      rw [←conjugateSubrepresentationOrderIso_mul,hsq d hd,conjugateSubrepresentationOrderIso_one]
    exact hcc.symm.le.trans (c.monotone hle)
  have hn : A⊔C≠⊥ := fun h => ha.ne_bot (le_bot_iff.mp (le_sup_left.trans_eq h))
  have htop := eq_top_of_stable ρ N (A⊔C) hn (fun g =>
    stable_of_generators ρ N D (A⊔C) hstable (hgen ▸ mem_top g))
  have htop' : A.toSubmodule⊔C.toSubmodule=⊤ := by
    rw [←Subrepresentation.toSubmodule_sup]
    exact congrArg Subrepresentation.toSubmodule htop
  have hle := Submodule.finrank_add_le_finrank_add_finrank A.toSubmodule C.toSubmodule
  rw [htop',finrank_top,hA,hC] at hle
  omega

/-- Every occurring normal simple type spans the whole ambient module. -/
theorem component_eq_top (ρ : Representation F G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal]
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y) (hdim : 2<finrank F V)
    (D : Set G) (hgen : closure D=⊤)
    (hsq : ∀ d∈D, d*d=1)
    (hrank : ∀ d∈D, finrank F (LinearMap.range (ρ d-LinearMap.id))=1)
    (A : Subrepresentation (ρ.comp N.subtype)) [A.toRepresentation.IsIrreducible] :
    component (ρ.comp N.subtype) A=⊤ := by
  by_contra ht
  let C := component (ρ.comp N.subtype) A
  have ha := (Subrepresentation.irreducible_iff_isAtom A).mp inferInstance
  have hn : C≠⊥ := fun h => ha.ne_bot (le_bot_iff.mp ((le_component _ A).trans_eq h))
  obtain ⟨d,hd,hmove⟩ := exists_moving_generator ρ N D hgen C hn ht
  have hle := moved_component_finrank_le_one ρ N A inferInstance d (hrank d hd) hmove
  change finrank F C.toSubmodule≤1 at hle
  have hCn : C.toSubmodule≠⊥ := fun h => hn (Subrepresentation.toSubmodule_injective h)
  have hpos : 0<finrank F C.toSubmodule := by
    let : Nontrivial C.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hCn
    exact Module.finrank_pos
  have hdimC : finrank F C.toSubmodule=1 := by omega
  have hAn : A.toSubmodule≠⊥ := fun h => ha.ne_bot (Subrepresentation.toSubmodule_injective h)
  have hAC : A.toSubmodule=C.toSubmodule :=
    ((Submodule.isAtom_iff_finrank_eq_one.mpr hdimC).le_iff_eq hAn).mp (le_component _ A)
  have hCA : C=A := Subrepresentation.toSubmodule_injective hAC.symm
  have hdimA : finrank F A.toSubmodule=1 := hAC.symm ▸ hdimC
  exact no_line_component ρ N B halt hB hp hdim D hgen hsq hrank A hdimA hCA

/-- Homogeneity for the literal restriction and any selected simple constituent. -/
theorem normal_restriction_isotypic (ρ : Representation F G V) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal]
    (B : LinearMap.BilinForm F V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (hp : ∀ g x y, B (ρ g x) (ρ g y)=B x y) (hdim : 2<finrank F V)
    (D : Set G) (hgen : closure D=⊤)
    (hsq : ∀ d∈D, d*d=1)
    (hrank : ∀ d∈D, finrank F (LinearMap.range (ρ d-LinearMap.id))=1)
    (A : Subrepresentation (ρ.comp N.subtype)) [A.toRepresentation.IsIrreducible] :
    IsIsotypicOfType F[N] (Representation.asModule (ρ.comp N.subtype)) A.asSubmodule := by
  let : IsSimpleModule F[N] A.asSubmodule := isSimpleModule_iff_isAtom.mpr
    ((Subrepresentation.subrepresentationSubmoduleOrderIso.isAtom_iff A).mpr
      ((Subrepresentation.irreducible_iff_isAtom A).mp inferInstance))
  apply IsIsotypicOfType.of_isotypicComponent_eq_top
  rw [←component_asSubmodule,component_eq_top ρ N B halt hB hp hdim D hgen hsq hrank A]
  rfl

end Representation.RankOneSymplectic.Homogeneous
