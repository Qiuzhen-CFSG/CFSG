module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.RankOne.Geometry
public import Theory.Representation.AffineNine.Model
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# The actual elementary-nine conjugation action

An elementary group of order nine is identified with the ternary plane.
Transporting its automorphisms along these coordinates gives a matrix action
which retains conjugation in the original group, point by point. No assertion
that its image contains SL₂(3) is built into this construction.

For the selected source actor Uγ*, placement in a conjugate of O₂(L₁T)
and the proved parabolic-core centralizer identity give faithful action on
the original P*. In the elementary case the source Frattini interval is
exactly the ordinary irreducibility interval. These are inputs to the
remaining image recognition and character-space argument, not an exclusion
of the elementary-nine branch by themselves.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951 (PDF p.968).
-/

public section

open Subgroup
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

open Representation.AffineNine

variable {K : Type*} [Group K]

/-- Coordinates on the original normal subgroup, with its actual ambient
conjugation action. This record asserts no largeness of the matrix image. -/
structure ConjugationCoordinates (P : Subgroup K) where
  coordinate : P ≃* Translation
  action : K →* LinearGroup
  conjugates : ∀ (k : K) (p : P),
    k * (p : K) * k⁻¹ =
      (coordinate.symm (naturalAction (action k) (coordinate p)) : P)

private def automorphismAdd (a : MulAut Translation) : Plane ≃+ Plane where
  toFun v := (a (Multiplicative.ofAdd v)).toAdd
  invFun v := (a.symm (Multiplicative.ofAdd v)).toAdd
  left_inv v := a.left_inv v
  right_inv v := a.right_inv v
  map_add' v w := a.map_mul v w

private def automorphismLinear : MulAut Translation ≃* (Plane ≃ₗ[ZMod 3] Plane) where
  toFun a := { automorphismAdd a with map_smul' := ZMod.map_smul (automorphismAdd a) }
  invFun a := a.toAddEquiv.toMultiplicative
  left_inv a := by ext; rfl
  right_inv a := by ext; rfl
  map_mul' a b := by ext; rfl

private def naturalActionEquiv : LinearGroup ≃* MulAut Translation :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) Plane).trans
      automorphismLinear.symm)

/-- Construct matrix coordinates on the literal conjugation action, without
assuming a splitting or any image-recognition conclusion. -/
noncomputable def conjugationCoordinates [Finite K] (P : Subgroup K)
    [P.Normal] [IsElementaryAbelian 3 P] (hP : Nat.card P = 9) :
    ConjugationCoordinates P := by
  classical
  have hpow : 3 ^ Module.finrank (ZMod 3) (Additive P) = 3 ^ 2 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive P)
    change Nat.card P = _ at hc
    simpa only [Nat.card_zmod, hP, show (3 : ℕ) ^ 2 = 9 by decide] using hc.symm
  have hd : Module.finrank (ZMod 3) (Additive P) = 2 :=
    Nat.pow_right_injective (by decide : 1 < 3) hpow
  let c : P ≃* Translation :=
    (Module.finBasisOfFinrankEq (ZMod 3) (Additive P) hd).equivFun.toAddEquiv.toMultiplicativeRight
  let e : MulAut P ≃* LinearGroup := (MulAut.congr c).trans naturalActionEquiv.symm
  refine ⟨c, e.toMonoidHom.comp MulAut.conjNormal, ?_⟩
  intro k p
  have he : naturalAction (e (MulAut.conjNormal k)) = MulAut.congr c (MulAut.conjNormal k) :=
    naturalActionEquiv.apply_symm_apply _
  rw [show (e.toMonoidHom.comp MulAut.conjNormal) k = e (MulAut.conjNormal k) from rfl, he]
  change k * (p : K) * k⁻¹ = (c.symm (c (MulAut.conjNormal k (c.symm (c p)))) : P)
  simp only [MulEquiv.symm_apply_apply]
  rfl

/-- The matrix kernel is precisely the centralizer of the marked original
subgroup; coordinates cannot discard any conjugation information. -/
theorem ConjugationCoordinates.ker_eq_centralizer {P : Subgroup K}
    (a : ConjugationCoordinates P) : a.action.ker = centralizer (P : Set K) := by
  ext k
  constructor
  · intro hk
    apply mem_centralizer_iff.mpr
    intro p hp
    have he := a.conjugates k ⟨p, hp⟩
    rw [show a.action k = 1 from hk, map_one] at he
    simp only [MulAut.one_apply, MulEquiv.symm_apply_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hk
    change a.action k = 1
    apply naturalActionEquiv.injective
    change naturalAction (a.action k) = naturalAction 1
    rw [map_one]
    ext x : 1
    obtain ⟨p, rfl⟩ := a.coordinate.surjective x
    have he := a.conjugates k p
    rw [← mem_centralizer_iff.mp hk p p.property, mul_inv_cancel_right] at he
    have he' : p = a.coordinate.symm (naturalAction (a.action k) (a.coordinate p)) :=
      Subtype.ext he
    exact (a.coordinate.apply_symm_apply _).symm.trans (congrArg a.coordinate he').symm

/-- A subgroup with trivial centralizer of P embeds in its marked matrix image. -/
theorem ConjugationCoordinates.injective_on {P : Subgroup K}
    (a : ConjugationCoordinates P) (A : Subgroup K)
    (hA : A ⊓ centralizer (P : Set K) = ⊥) :
    Function.Injective (a.action.comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hk : (x : K) ∈ centralizer (P : Set K) :=
    a.ker_eq_centralizer ▸ (show (x : K) ∈ a.action.ker from hx)
  apply Subtype.ext
  change (x : K) = 1
  exact mem_bot.mp (hA ▸ (show (x : K) ∈ A ⊓ centralizer (P : Set K) from ⟨x.property, hk⟩))

variable {G : Type*} [Group G]

/-- Faithfulness on the original odd subgroup follows from actual conjugate
core placement, including for a proper subgroup of Vγ*. -/
theorem star_centralizer_eq_bot_of_placement [Finite G] {p : ℕ}
    {H L₁ T M Vα B : Subgroup G} (r : ReducedOdd p H L₁ T M Vα)
    (h : H) (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H B ⊓ centralizer (Source.starImage H r.P : Set _) = ⊥ := by
  let := r.Pstar_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  apply bot_unique
  rintro x ⟨⟨b, hb, rfl⟩, hcent⟩
  have hc : q h * q b * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) := by
    refine ⟨h * b * h⁻¹, hB (mem_map_of_mem _ hb), ?_⟩
    change q (h * b * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hh := (inferInstance :
      (centralizer (Source.starImage H r.P : Set (Source.Hstar H))).Normal).conj_mem
      (q b) hcent (q h)
  have he : q h * q b * (q h)⁻¹ = 1 := by
    have hi := show q h * q b * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓
        centralizer (Source.starImage H r.P : Set (Source.Hstar H)) from ⟨hc, hh⟩
    rwa [RankOne.parabolic_core_star_centralizer r, mem_bot] at hi
  exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q h)).symm))

/-- The selected quadratic actor has trivial centralizer of the actual P*. -/
theorem source_actor_centralizer [Finite G]
    {H L L₁ M V V₃ V₁ Vα : Subgroup G} {T : Sylow 2 G}
    {c : CriticalGeometry.CriticalPair L T H V} (s : RankOne.Geometry c V₃ V₁ L₁)
    (r : ReducedOdd 3 H L₁ T M Vα) :
    Source.starImage H (c.Ugamma V₃) ⊓
      centralizer (Source.starImage H r.P : Set _) = ⊥ := by
  obtain ⟨h, hh⟩ := s.placement
  exact star_centralizer_eq_bot_of_placement r h
    ((map_mono s.Ugamma_le_Vgamma).trans hh)

/-- Faithful conjugation, as a homomorphism on the actual source actor. -/
theorem source_actor_faithful [Finite G]
    {H L L₁ M V V₃ V₁ Vα : Subgroup G} {T : Sylow 2 G}
    {c : CriticalGeometry.CriticalPair L T H V} (s : RankOne.Geometry c V₃ V₁ L₁)
    (r : ReducedOdd 3 H L₁ T M Vα) :
    letI := r.Pstar_normal
    Function.Injective ((MulAut.conjNormal : Source.Hstar H →*
      MulAut (Source.starImage H r.P)).comp (Source.starImage H (c.Ugamma V₃)).subtype) := by
  let := r.Pstar_normal
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hc : (a : Source.Hstar H) ∈ centralizer (Source.starImage H r.P : Set _) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun ha (⟨x, hx⟩ : Source.starImage H r.P))
    change (a : Source.Hstar H) * x * (a : Source.Hstar H)⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  apply Subtype.ext
  have hi : (a : Source.Hstar H) ∈ Source.starImage H (c.Ugamma V₃) ⊓
      centralizer (Source.starImage H r.P : Set _) := ⟨a.property, hc⟩
  change (a : Source.Hstar H) = 1
  simpa only [source_actor_centralizer s r, mem_bot] using hi

/-- Any marked coordinates on the original P* give an injective matrix action
of the selected source offender. -/
theorem source_actor_matrix_injective [Finite G]
    {H L L₁ M V V₃ V₁ Vα : Subgroup G} {T : Sylow 2 G}
    {c : CriticalGeometry.CriticalPair L T H V} (s : RankOne.Geometry c V₃ V₁ L₁)
    (r : ReducedOdd 3 H L₁ T M Vα)
    (a : ConjugationCoordinates (Source.starImage H r.P)) :
    Function.Injective (a.action.comp (Source.starImage H (c.Ugamma V₃)).subtype) :=
  a.injective_on _ (source_actor_centralizer s r)

/-- Matrix coordinates exist on this same source P*, before any recognition
of their image as SL₂(3) or GL₂(3). -/
noncomputable def source_coordinates [Finite G]
    {H L₁ T M Vα : Subgroup G} (r : ReducedOdd 3 H L₁ T M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    (hcard : Nat.card (Source.starImage H r.P) = 9) :
    ConjugationCoordinates (Source.starImage H r.P) := by
  let := r.Pstar_normal
  exact conjugationCoordinates _ hcard

/-- For E₉ the intrinsic Frattini subgroup disappears; this is a statement
about its specified embedding in H*, not a substituted quotient. -/
theorem starFrattini_eq_bot [Finite G]
    {H L₁ T M Vα : Subgroup G} (r : ReducedOdd 3 H L₁ T M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)] : starFrattini H r.P = ⊥ := by
  let : Fact (IsPGroup 3 (Source.starImage H r.P)) :=
    ⟨starImage_isPGroup H r.P r.P_isPGroup⟩
  unfold starFrattini
  rw [frattini_eq_bot_of_isElementaryAbelian (p := 3), Subgroup.map_bot]

/-- The supplied Frattini irreducibility is ordinary irreducibility on
the actual elementary-nine subgroup. -/
theorem source_irreducible [Finite G]
    {H L₁ T M Vα : Subgroup G} (r : ReducedOdd 3 H L₁ T M Vα)
    [IsElementaryAbelian 3 (Source.starImage H r.P)]
    (N : Subgroup (Source.Hstar H)) (hN : N ≤ Source.starImage H r.P)
    (hn : Source.starImage H (L₁ ⊔ T) ≤ normalizer (N : Set _)) :
    N = ⊥ ∨ N = Source.starImage H r.P := by
  have h := r.irreducible N (by rw [starFrattini_eq_bot r]; exact bot_le) hN hn
  rwa [starFrattini_eq_bot r] at h

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine

end
