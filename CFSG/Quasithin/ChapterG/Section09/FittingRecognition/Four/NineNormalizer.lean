module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NineNormalizer.Concrete
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NormalizerModel
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.Reduction
import Mathlib.Tactic

/-!
# The full order-nine normalizer in binary degree four

A subgroup of order nine in GL₄(2) is Sylow, since |GL₄(2)| = 20160.
Sylow conjugacy therefore places it in the product of the two explicit cubic
plane groups of `NineNormalizer.Concrete`. This proves elementary abelianness,
excludes the cyclic order-nine possibility, and identifies the two irreducible
planes with their actual actions.

Conjugation transports the full normalizer, its action, and its marked
three-subgroup to `BinaryFourPlus.q.isometrySubgroup`. The published isometry
`splitOrthogonalEquiv` then gives the prescribed full hyperbolic orthogonal
carrier. The three-core applications use `OrthogonalNormalizerModel.realization`
and discharge the order-nine premise at actor rank two with `Four.Reduction`.

Source: Aschbacher--Smith, G.9.4, printed pp.354--355 / PDF pp.365--366.
This module proves the order-nine branch; final degree-four assembly is in Four.
-/

public section

open BinaryFourPlus
open LinearMap.GeneralLinearGroup
open CFSG.Quasithin.ChapterG.Section09.FittingRecognition
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NineNormalizer
universe u v
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

abbrev L := BinaryFourPlus.V ≃ₗ[ZMod 2] BinaryFourPlus.V

def unitCoordinates (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V) :
    (Module.End (ZMod 2) W)ˣ ≃* L :=
  (congrLinearEquiv e).trans (generalLinearEquiv (ZMod 2) BinaryFourPlus.V)

theorem unitCoordinates_apply (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (g : (Module.End (ZMod 2) W)ˣ) (v : BinaryFourPlus.V) :
    unitCoordinates e g v = e (g.val (e.symm v)) := by rfl

theorem unitCoordinates_trans (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V) (g : L) :
    unitCoordinates (e.trans g) = (unitCoordinates e).trans (MulAut.conj g) := by
  ext x v <;> rfl

theorem finrank_binary : Module.finrank (ZMod 2) BinaryFourPlus.V = 4 := by
  simp [BinaryFourPlus.V, Plane, Module.finrank_prod]

theorem card_linear : Nat.card L = 20160 := by
  let b := Module.finBasis (ZMod 2) BinaryFourPlus.V
  calc
    Nat.card L = Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) BinaryFourPlus.V) :=
      (Nat.card_congr (generalLinearEquiv (ZMod 2) BinaryFourPlus.V).toEquiv).symm
    _ = Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank (ZMod 2) BinaryFourPlus.V)) (ZMod 2)) :=
      (Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b).toEquiv).symm
    _ = 20160 := by
      rw [finrank_binary, Matrix.card_GL_field]
      norm_num [Fin.prod_univ_succ]

def sylowOfNine (P : Subgroup L) (hc : Nat.card P = 9) : Sylow 3 L := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hi : P.index = 2240 := by
    have h := P.card_mul_index
    rw [hc, card_linear] at h
    omega
  exact (IsPGroup.of_card (p := 3) (n := 2) hc).toSylow (by rw [hi]; decide)

theorem exists_conjugate_nine (P : Subgroup L) (hc : Nat.card P = 9) :
    ∃ g : L, P.map (MulAut.conj g).toMonoidHom = nine := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L (sylowOfNine P hc) (sylowOfNine nine card_nine)
  exact ⟨g, congrArg (fun S : Sylow 3 L => (S : Subgroup L)) hg⟩

/-- Sylow conjugacy supplies actual coordinates for every order-nine linear subgroup. -/
theorem exists_coordinates [FiniteDimensional (ZMod 2) W]
    (hd : Module.finrank (ZMod 2) W = 4)
    (P : Subgroup (Module.End (ZMod 2) W)ˣ) (hc : Nat.card P = 9) :
    ∃ e : W ≃ₗ[ZMod 2] BinaryFourPlus.V,
      P.map (unitCoordinates e).toMonoidHom = nine := by
  let e := LinearEquiv.ofFinrankEq W BinaryFourPlus.V (hd.trans finrank_binary.symm)
  have hcard : Nat.card (P.map (unitCoordinates e).toMonoidHom) = 9 :=
    (Nat.card_congr ((unitCoordinates e).subgroupMap P).toEquiv).symm.trans hc
  obtain ⟨g, hg⟩ := exists_conjugate_nine _ hcard
  refine ⟨e.trans g, ?_⟩
  rw [unitCoordinates_trans]
  exact (Subgroup.map_map _ _ _).symm.trans hg


/-- Transport the literal full linear normalizer along the chosen coordinates. -/
def normalizerEquiv (P : Subgroup (Module.End (ZMod 2) W)ˣ)
    (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (he : P.map (unitCoordinates e).toMonoidHom = nine) :
    Subgroup.normalizer (P : Set ((Module.End (ZMod 2) W)ˣ)) ≃* q.isometrySubgroup :=
  ((unitCoordinates e).subgroupMap (Subgroup.normalizer (P : Set ((Module.End (ZMod 2) W)ˣ)))).trans
    (MulEquiv.subgroupCongr ((Subgroup.map_equiv_normalizer_eq P (unitCoordinates e)).trans
      (by rw [he, normalizer_nine])))

theorem normalizerEquiv_apply (P : Subgroup (Module.End (ZMod 2) W)ˣ)
    (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (he : P.map (unitCoordinates e).toMonoidHom = nine)
    (g : Subgroup.normalizer (P : Set ((Module.End (ZMod 2) W)ˣ))) :
    (normalizerEquiv P e he g).val = unitCoordinates e g.val := by rfl

theorem normalizerEquiv_core (P : Subgroup (Module.End (ZMod 2) W)ˣ)
    (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (he : P.map (unitCoordinates e).toMonoidHom = nine) :
    (P.subgroupOf (Subgroup.normalizer (P : Set ((Module.End (ZMod 2) W)ˣ)))).map
      (normalizerEquiv P e he).toMonoidHom = pCore 3 q.isometrySubgroup := by
  rw [← nine_is_core]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    change unitCoordinates e x.val ∈ nine
    rw [← he]
    exact ⟨x.val, hx, rfl⟩
  · intro hg
    change g.val ∈ nine at hg
    rw [← he] at hg
    obtain ⟨x, hx, hxe⟩ := hg
    exact ⟨⟨x, P.le_normalizer hx⟩, hx, Subtype.ext hxe⟩

variable {G : Type u} [Group G]

/-- Pass from the two-plane model to the prescribed full hyperbolic carrier. -/
def modelOfCoordinates (ρ : Representation (ZMod 2) G W) (B : Subgroup G)
    (e : W ≃ₗ[ZMod 2] BinaryFourPlus.V)
    (he : (linearImage ρ B).map (unitCoordinates e).toMonoidHom = nine) :
    OrthogonalNormalizerModel ρ B where
  groupEquiv := (normalizerEquiv (linearImage ρ B) e he).trans splitOrthogonalEquiv.symm
  coordinates := e.trans splitCoordinates.symm
  intertwines g v := by
    apply splitCoordinates.injective
    have h := splitOrthogonalEquiv_intertwines
      (splitOrthogonalEquiv.symm (normalizerEquiv (linearImage ρ B) e he g))
      (splitCoordinates.symm (e v))
    simpa only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      MulEquiv.trans_apply, MulEquiv.apply_symm_apply, normalizerEquiv_apply,
      unitCoordinates_apply, LinearEquiv.symm_apply_apply] using h
  core_eq := by
    change (linearImage ρ B |>.subgroupOf (linearNormalizer ρ B)).map
      (splitOrthogonalEquiv.symm.toMonoidHom.comp
        (normalizerEquiv (linearImage ρ B) e he).toMonoidHom) = _
    rw [← Subgroup.map_map, normalizerEquiv_core, pCore_map_iso]

/-- The full normalizer of a faithful order-nine subgroup in binary degree four,
with its actual natural action and marked three-core. -/
theorem orthogonalNormalizerModel [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hfaithful : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4) (B : Subgroup G) (hc : Nat.card B = 9) :
    Nonempty (OrthogonalNormalizerModel ρ B) := by
  have hi : Function.Injective ρ.asGroupHom := fun x y h => hfaithful (congrArg Units.val h)
  have hc' : Nat.card (linearImage ρ B) = 9 :=
    (Subgroup.card_map_of_injective hi).trans hc
  obtain ⟨e, he⟩ := exists_coordinates hd (linearImage ρ B) hc'
  exact ⟨modelOfCoordinates ρ B e he⟩

/-- A faithful order-nine subgroup acts as the independent cubic rotations
on two binary planes. `plane_irreducible` proves irreducibility on each plane. -/
theorem exists_split_action [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hfaithful : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4) (B : Subgroup G) (hc : Nat.card B = 9) :
    ∃ e : W ≃ₗ[ZMod 2] BinaryFourPlus.V, ∃ f : B ≃* E9,
      (∀ (b : B) v, e (ρ (b : G) v) = nineHom (f b) (e v)) ∧
      (∀ U : Submodule (ZMod 2) Plane,
        (∀ (b : B) v, v ∈ U → planeHom (f b).1 v ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      (∀ U : Submodule (ZMod 2) Plane,
        (∀ (b : B) v, v ∈ U → planeHom (f b).2 v ∈ U) → U = ⊥ ∨ U = ⊤) := by
  have hi : Function.Injective ρ.asGroupHom := fun x y h => hfaithful (congrArg Units.val h)
  have hc' : Nat.card (linearImage ρ B) = 9 :=
    (Subgroup.card_map_of_injective hi).trans hc
  obtain ⟨e, he⟩ := exists_coordinates hd (linearImage ρ B) hc'
  let j := (B.equivMapOfInjective ρ.asGroupHom hi).trans
    (((unitCoordinates e).subgroupMap (linearImage ρ B)).trans (MulEquiv.subgroupCongr he))
  let f : B ≃* E9 := j.trans (MonoidHom.ofInjective nineHom_injective).symm
  refine ⟨e, f, ?_, ?_, ?_⟩
  · intro b v
    have hf : nineHom (f b) = unitCoordinates e (ρ.asGroupHom (b : G)) :=
      congrArg Subtype.val ((MonoidHom.ofInjective nineHom_injective).apply_symm_apply (j b))
    rw [hf, unitCoordinates_apply, LinearEquiv.symm_apply_apply]
    rfl
  · intro U hU
    apply plane_irreducible U
    intro c v hv
    obtain ⟨b, hb⟩ := f.surjective (c, 1)
    simpa only [hb] using hU b v hv
  · intro U hU
    apply plane_irreducible U
    intro c v hv
    obtain ⟨b, hb⟩ := f.surjective (1, c)
    simpa only [hb] using hU b v hv

/-- A faithful order-nine subgroup in binary degree four is elementary abelian. -/
theorem elementary_of_card_nine [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hfaithful : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4) (B : Subgroup G) (hc : Nat.card B = 9) :
    IsElementaryAbelian 3 B := by
  obtain ⟨_, f, _⟩ := exists_split_action ρ hfaithful hd B hc
  exact IsElementaryAbelian.of_surjective f.symm.toMonoidHom f.symm.surjective

/-- Explicitly exclude the cyclic order-nine possibility. -/
theorem not_cyclic_of_card_nine [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hfaithful : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4) (B : Subgroup G) (hc : Nat.card B = 9) :
    ¬ IsCyclic B := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Finite B := Nat.finite_of_card_ne_zero (hc.trans_ne (by decide))
  let : IsElementaryAbelian 3 B := elementary_of_card_nine ρ hfaithful hd B hc
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 3) hc

/-- Apply the order-nine full normalizer to the literal three-core of the
original group. This supplies the orthogonal alternative in G.9.4(3--4). -/
theorem core_realization [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hfaithful : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) W = 4) (hc : Nat.card (pCore 3 G) = 9) :
    ∃ H : Subgroup OrthogonalFour, pCore 3 OrthogonalFour ≤ H ∧
      OrthogonalRealization ρ H := by
  obtain ⟨d⟩ := orthogonalNormalizerModel ρ hfaithful hd (pCore 3 G) hc
  exact d.realization hfaithful

/-- At actor rank two the parent's core-order reduction discharges the
order-nine hypothesis, giving the marked orthogonal realization directly. -/
theorem core_realization_of_rank_two [Finite G] [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) G W} {A : Subgroup G}
    (h : Setup ρ A 2) (data : ThreeCoreData ρ A 2)
    (hd : Module.finrank (ZMod 2) W = 4) :
    ∃ H : Subgroup OrthogonalFour, pCore 3 OrthogonalFour ≤ H ∧
      OrthogonalRealization ρ H :=
  core_realization ρ h.faithful hd (threeCore_card_nine_of_rank_two h data hd)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NineNormalizer
