module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.ModuleStructure.BinaryNormalizer.Concrete
public import Theory.ElementaryAbelian.PrimePlane

/-!
# Compatible full normalizers for arbitrary elementary binary sixteen

Choose binary vector coordinates, then use conjugacy of Sylow three-subgroups
in GL₄(2) to carry the original order-nine subgroup to the actual independent
plane rotations. Transport the concrete full-normalizer identification through
those same coordinates. The resulting isomorphism intertwines every original
automorphism on every vector and identifies the actor subgroup itself.

The Sylow argument uses |GL₄(2)|=20160 only to certify that both order-nine
subgroups are Sylow; recognition of their normalizer uses the quadratic form,
not an abstract order or group-family tag.

Source: Aschbacher--Smith, 15.4.12(6)(ii), printed pp.1160--1161, combined
manuscript (1 March 2004).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
namespace CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer

private theorem nine_conjugate {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 20160) (B C : Subgroup H) (hB : Nat.card B = 9) (hC : Nat.card C = 9) :
    ∃ g : H, B.map (MulAut.conj g).toMonoidHom = C := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hindex (D : Subgroup H) (hD : Nat.card D = 9) : ¬3 ∣ D.index := by
    have hh := D.card_mul_index
    rw [hD,hH] at hh
    have hi : D.index = 2240 := by omega
    rw [hi]
    decide
  let P : Sylow 3 H := (IsPGroup.of_card (p := 3) (n := 2) hB).toSylow (hindex B hB)
  let Q : Sylow 3 H := (IsPGroup.of_card (p := 3) (n := 2) hC).toSylow (hindex C hC)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P Q
  refine ⟨g,?_⟩
  exact congrArg Sylow.toSubgroup hg

/-- Choose actual binary coordinates carrying the original cubic actor onto
the independent rotations of the fixed orthogonal model. -/
theorem double_actor_coordinates {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 16)
    (A : Subgroup (MulAut W)) (hA : Nat.card A = 9) :
    ∃ c : W ≃* ModelSpace, A.map (MulAut.congr c).toMonoidHom = modelRotations := by
  have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  have hdim : Module.finrank (ZMod 2) (Additive W) = 4 :=
    Nat.pow_right_injective (by decide : 1 < 2) (hc.symm.trans hW)
  let l : Additive W ≃ₗ[ZMod 2] Space := LinearEquiv.ofFinrankEq _ _
    (by simp [hdim,Space,Plane,Module.finrank_prod])
  let c₀ : W ≃* ModelSpace := l.toAddEquiv.toMultiplicativeRight
  let B := A.map (MulAut.congr c₀).toMonoidHom
  have hB : Nat.card B = 9 :=
    (card_map_of_injective (MulAut.congr c₀).injective).trans hA
  have hAut : Nat.card (MulAut ModelSpace) = 20160 := by
    rw [←Nat.card_congr (MulAut.congr c₀).toEquiv,
      SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow W 4 hW]
    norm_num [Fin.prod_univ_succ]
  obtain ⟨g,hg⟩ := nine_conjugate hAut B modelRotations hB modelRotations_card
  refine ⟨c₀.trans g,?_⟩
  have he : (MulAut.congr (c₀.trans g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.congr c₀).toMonoidHom := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro w
    rfl
  rw [he,←map_map]
  exact hg

/-- Transport the full normalizer along the same vector coordinates. -/
noncomputable def normalizerTransport {W : Type*} [Group W]
    (A : Subgroup (MulAut W)) (c : W ≃* ModelSpace)
    (hc : A.map (MulAut.congr c).toMonoidHom = modelRotations) :
    normalizer (A : Set (MulAut W)) ≃* normalizer (modelRotations : Set (MulAut ModelSpace)) :=
  ((normalizer (A : Set (MulAut W))).equivMapOfInjective
    (MulAut.congr c).toMonoidHom (MulAut.congr c).injective).trans
    (MulEquiv.subgroupCongr (by rw [map_equiv_normalizer_eq,hc]))

theorem normalizerTransport_val {W : Type*} [Group W]
    (A : Subgroup (MulAut W)) (c : W ≃* ModelSpace)
    (hc : A.map (MulAut.congr c).toMonoidHom = modelRotations)
    (n : normalizer (A : Set (MulAut W))) :
    (normalizerTransport A c hc n : MulAut ModelSpace) = MulAut.congr c (n : MulAut W) := rfl

/-- The arbitrary faithful binary-four normalizer is the ACTUAL isometry group
of the fixed plus-type form, with the complete natural action intertwined. -/
theorem double_normalizer_coordinates {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 16)
    (A : Subgroup (MulAut W)) (hA : Nat.card A = 9) :
    ∃ (c : W ≃* ModelSpace)
      (e : normalizer (A : Set (MulAut W)) ≃* OrthogonalFourBinary.IsometryGroup),
      A.map (MulAut.congr c).toMonoidHom = modelRotations ∧
      ∀ (n : normalizer (A : Set (MulAut W))) (w : W),
        c ((n : MulAut W) w) = vectorAction (e n) (c w) := by
  obtain ⟨c,hc⟩ := double_actor_coordinates hW A hA
  let e := (normalizerTransport A c hc).trans modelNormalizerEquiv
  refine ⟨c,e,hc,?_⟩
  intro n w
  rw [show e n = modelNormalizerEquiv (normalizerTransport A c hc n) from rfl,
    modelNormalizerEquiv_apply,normalizerTransport_val]
  change c ((n : MulAut W) w) = c ((n : MulAut W) (c.symm (c w)))
  rw [c.symm_apply_apply]

end CFSG.Quasithin.Chapter15.Section04.FamilySource.ModuleStructure.BinaryNormalizer
