module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.FieldResidual
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldModels
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# Transporting the local Sylow three-subgroup to the field centralizer

Conjugation carrying w to f embeds the supplied Sylow three-subgroup of
C_I(w) in C_G(f). Its actual equivalence, extraspecial structure, order and
exponent are retained. This is the subgroup B used to exclude components
of three-rank one; it is not asserted to centralize a conjugate four-group.

The last theorem combines this construction with the proved ordinary-layer
inclusion for the field residual. Component selection remains a separate
argument, as do the earlier local model and balance inputs.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137, the paragraph beginning “Suppose that there is a
component”.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion

/-- The transported subgroup, including its pointwise conjugation formula. -/
theorem extraspecial_subgroup_of_fusion {G : Type*} [Group G] (I : Subgroup G) {w f : G}
    (hfusion : IsConj w f) (P : Sylow 3 (I ⊓ centralizer ({w} : Set G) : Subgroup G))
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (he : ∀ x : P, x ^ 3 = 1) :
    ∃ (g : G) (B : Subgroup G), (MulAut.conj g) w = f ∧
      B ≤ centralizer ({f} : Set G) ∧ IsExtraspecial 3 B ∧
      Nat.card B = 27 ∧ (∀ b : B, b ^ 3 = 1) ∧
      ∃ e : P ≃* B, ∀ x : P, (e x : G) =
        (MulAut.conj g) (((x : (I ⊓ centralizer ({w} : Set G) : Subgroup G)) : G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
  change (MulAut.conj g) w = f at hg
  let C := I ⊓ centralizer ({w} : Set G)
  let φ : C →* G := (MulAut.conj g).toMonoidHom.comp C.subtype
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp C.subtype_injective
  let B := (P : Subgroup C).map φ
  let e : P ≃* B := (P : Subgroup C).equivMapOfInjective φ hφ
  refine ⟨g, B, hg, ?_, IsExtraspecial.of_mulEquiv e inferInstance,
    (Nat.card_congr e.toEquiv).symm.trans hc, ?_, e, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp x.property.2)
    simpa only [map_mul, hg, φ, MonoidHom.comp_apply, subtype_apply, MulEquiv.coe_toMonoidHom] using h
  · intro b
    obtain ⟨x, rfl⟩ := e.surjective b
    rw [← map_pow, he, map_one]
  · intro x
    rfl

/-- Restrict the transported subgroup to the actual field centralizer. -/
theorem extraspecial_subgroup_in_fieldCentralizer {G : Type*} [Group G]
    (I : Subgroup G) {w f : G} (hfusion : IsConj w f)
    (P : Sylow 3 (I ⊓ centralizer ({w} : Set G) : Subgroup G))
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (he : ∀ x : P, x ^ 3 = 1) :
    ∃ B : Subgroup (centralizer ({f} : Set G)), IsExtraspecial 3 B ∧
      Nat.card B = 27 ∧ (∀ b : B, b ^ 3 = 1) := by
  obtain ⟨g, B, hg, hB, hs, hcB, heB, e, he⟩ :=
    extraspecial_subgroup_of_fusion I hfusion P hc he
  let eB := (subgroupOfEquivOfLe hB).symm
  refine ⟨B.subgroupOf (centralizer ({f} : Set G)),
    IsExtraspecial.of_mulEquiv eB hs,
    (Nat.card_congr eB.toEquiv).symm.trans hcB, ?_⟩
  intro b
  obtain ⟨b, rfl⟩ := eB.surjective b
  rw [← map_pow, heB, map_one]

/-- The supplied residual model identifies the subgroup embedded in C_G(f). -/
noncomputable def fieldResidualEquivModel {G : Type*} [Group G]
    (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    fieldResidual L f ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
  ((pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G)).equivMapOfInjective
    (inclusion inf_le_right) (inclusion_injective inf_le_right)).symm.trans e

/-- Fusion supplies both inputs for the subsequent component analysis. -/
theorem field_local_subgroups_of_fusion {G : Type*} [Group G] [Finite G]
    (V I L : Subgroup G) [IsKleinFour V]
    (hV : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup V)
    (hI : I = normalizer (V : Set G)) {w f : G}
    (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    (eO : pPrimeCore 2 (I ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine)
    (eF : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hbalance : fieldResidual L f ≤
      oddExtendedTwoComponentLayer (centralizer ({f} : Set G)))
    (P : Sylow 3 (I ⊓ centralizer ({w} : Set G) : Subgroup G))
    [IsExtraspecial 3 P] (hc : Nat.card P = 27) (he : ∀ x : P, x ^ 3 = 1) :
    fieldResidual L f ≤ componentLayer (centralizer ({f} : Set G)) ∧
      ∃ B : Subgroup (centralizer ({f} : Set G)), IsExtraspecial 3 B ∧
        Nat.card B = 27 ∧ (∀ b : B, b ^ 3 = 1) :=
  ⟨fieldResidual_le_layer_of_fusion V I L hV hI hw hfusion eO eF hbalance,
    extraspecial_subgroup_in_fieldCentralizer I hfusion P hc he⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
