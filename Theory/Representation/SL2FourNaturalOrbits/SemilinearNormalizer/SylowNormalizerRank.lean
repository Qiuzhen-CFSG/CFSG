module

public import Theory.Representation.SL2FourNaturalOrbits.SemilinearNormalizer.Labels
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Two cubic directions in a marked semilinear Sylow normalizer

The scalar units of F₄ form a cubic group centralizing SL₂(4). The normalizer
in SL₂(4) of any full Sylow four-group is A₄, so it contains a second cubic.
Their product embeds in the normalizer in ΓL₂(4) of the literal Sylow image:
the scalar--special product is injective because its determinant is the
square of the scalar and the scalar has order dividing three.

The final transport theorem applies this bound to an actual ambient group
and a specified subgroup image. This retains the Sylow marking required in
the noncontained branch of Aschbacher--Smith 13.7.19; recognition
of the ambient semilinear group and identification of the source kernel are
separate inputs.
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
namespace Representation.SL2FourNatural.SemilinearNormalizer
open Matrix.GeneralLinearGroup

/-- Every nonzero scalar over F₄ has order dividing three. -/
theorem units_cube (c : Fˣ) : c ^ 3 = 1 := by
  have hc : Nat.card Fˣ = 3 := (Nat.card_eq_fintype_card).trans card_labels
  simpa only [hc] using (pow_card_eq_one' (x := c))

/-- The scalar--special product inside the literal linear group. -/
def scalarSpecial : Fˣ × SL →* LinearGroup where
  toFun x := GeneralLinearGroup.scalar (Fin 2) x.1 * SpecialLinearGroup.toGL x.2
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    calc
      (GeneralLinearGroup.scalar (Fin 2) x.1 * GeneralLinearGroup.scalar (Fin 2) y.1) *
          (SpecialLinearGroup.toGL x.2 * SpecialLinearGroup.toGL y.2) =
          GeneralLinearGroup.scalar (Fin 2) x.1 *
          (GeneralLinearGroup.scalar (Fin 2) y.1 * SpecialLinearGroup.toGL x.2) *
          SpecialLinearGroup.toGL y.2 := by simp only [mul_assoc]
      _ = GeneralLinearGroup.scalar (Fin 2) x.1 *
          (SpecialLinearGroup.toGL x.2 * GeneralLinearGroup.scalar (Fin 2) y.1) *
          SpecialLinearGroup.toGL y.2 :=
        congrArg (fun z => GeneralLinearGroup.scalar (Fin 2) x.1 * z *
          SpecialLinearGroup.toGL y.2)
          (GeneralLinearGroup.scalar_commute y.1 (SpecialLinearGroup.toGL x.2))
      _ = _ := by simp only [mul_assoc]

/-- Determinant records the square of the scalar coordinate. -/
theorem scalarSpecial_det (x : Fˣ × SL) : GeneralLinearGroup.det (scalarSpecial x) = x.1 ^ 2 := by
  change GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) x.1 * SpecialLinearGroup.toGL x.2) = _
  rw [map_mul, det_scalar, Fintype.card_fin]
  have h : GeneralLinearGroup.det (SpecialLinearGroup.toGL x.2) = 1 := Units.ext x.2.property
  rw [h, mul_one]

/-- Scalar units intersect the special linear group trivially. -/
theorem scalarSpecial_injective : Function.Injective scalarSpecial := by
  apply (MonoidHom.ker_eq_bot_iff scalarSpecial).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  have hh : scalarSpecial x = 1 := hx
  have hdet : x.1 ^ 2 = 1 := by
    have he := congrArg GeneralLinearGroup.det hh
    simpa only [scalarSpecial_det, map_one] using he
  have hc : x.1 = 1 := by
    have he := units_cube x.1
    have hx3 : x.1 ^ 3 = x.1 := by rw [pow_succ, hdet, one_mul]
    exact hx3.symm.trans he
  have hA : x.2 = 1 := by
    apply SpecialLinearGroup.toGL_injective
    change GeneralLinearGroup.scalar (Fin 2) x.1 * SpecialLinearGroup.toGL x.2 = 1 at hh
    rw [hc, map_one, one_mul] at hh
    simpa only [map_one] using hh
  exact Prod.ext hc hA

/-- The scalar subgroup of the literal semilinear group. -/
def scalar : Fˣ →* Gamma :=
  SemidirectProduct.inl.comp (GeneralLinearGroup.scalar (Fin 2))

/-- Scalars centralize the special linear image. -/
theorem scalar_special_commute (c : Fˣ) (g : SL) : Commute (scalar c) (special g) := by
  change SemidirectProduct.inl (GeneralLinearGroup.scalar (Fin 2) c) *
    SemidirectProduct.inl (SpecialLinearGroup.toGL g) =
    SemidirectProduct.inl (SpecialLinearGroup.toGL g) *
    SemidirectProduct.inl (GeneralLinearGroup.scalar (Fin 2) c)
  rw [← map_mul, ← map_mul, GeneralLinearGroup.scalar_commute]

/-- A full Sylow four-group in SL₂(4) has an A₄ normalizer. -/
theorem normalizer_sylow_card (Q : Sylow 2 SL) :
    Nat.card (Subgroup.normalizer (Q : Set SL)) = 12 := by
  let q := alternatingFiveEquiv
  let S := Q.mapSurjective (f := q.toMonoidHom) q.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) S AlternatingFiveProjection.sylow
  let e : SL ≃* alternatingGroup (Fin 5) := q.trans (MulAut.conj g)
  have hQ : (Q : Subgroup SL).map e.toMonoidHom = AlternatingFiveProjection.P := by
    change (Q : Subgroup SL).map ((MulAut.conj g).toMonoidHom.comp q.toMonoidHom) = _
    rw [← Subgroup.map_map]
    change (g • S).toSubgroup = AlternatingFiveProjection.P
    rw [hg]
    rfl
  have hn : (Subgroup.normalizer (Q : Set SL)).map e.toMonoidHom = BinaryPermutation.AlternatingFiveBorel.B := by
    change (Subgroup.normalizer ((Q : Subgroup SL) : Set SL)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq, hQ, AlternatingFiveProjection.normalizer_P]
  rw [Nat.card_congr ((Subgroup.normalizer (Q : Set SL)).equivMapOfInjective e.toMonoidHom e.injective).toEquiv, hn]
  exact (Nat.card_congr BinaryPermutation.AlternatingFiveBorel.marking.toEquiv.symm).trans
    (alternatingGroup.card_of_card_eq_four (by simp))

/-- The product of scalars with the actual special-linear Sylow normalizer. -/
def sylowNormalizerPair (Q : Sylow 2 SL) : Fˣ × Subgroup.normalizer (Q : Set SL) →* Gamma :=
  SemidirectProduct.inl.comp (scalarSpecial.comp
    ((MonoidHom.id Fˣ).prodMap (Subgroup.normalizer (Q : Set SL)).subtype))

/-- The two factors retain independent coordinates in ΓL₂(4). -/
theorem sylowNormalizerPair_injective (Q : Sylow 2 SL) :
    Function.Injective (sylowNormalizerPair Q) := by
  intro x y h
  have he := scalarSpecial_injective (SemidirectProduct.inl_injective h)
  change (x.1, x.2.val) = (y.1, y.2.val) at he
  have h1 : x.1 = y.1 := congrArg (fun z : Fˣ × SL => z.1) he
  have h2 : x.2.val = y.2.val := congrArg (fun z : Fˣ × SL => z.2) he
  exact Prod.ext h1 (Subtype.ext h2)

/-- Both factors normalize the image of the specified full Sylow subgroup. -/
theorem sylowNormalizerPair_mem (Q : Sylow 2 SL) (x : Fˣ × Subgroup.normalizer (Q : Set SL)) :
    sylowNormalizerPair Q x ∈ Subgroup.normalizer (((Q : Subgroup SL).map special : Subgroup Gamma) : Set Gamma) := by
  have hs : scalar x.1 ∈ centralizer (((Q : Subgroup SL).map special : Subgroup Gamma) : Set Gamma) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨g, hg, rfl⟩
    exact (scalar_special_commute x.1 g).symm
  have ht : special x.2.val ∈ Subgroup.normalizer (((Q : Subgroup SL).map special : Subgroup Gamma) : Set Gamma) :=
    (Q : Subgroup SL).le_normalizer_map special ⟨x.2.val, x.2.property, rfl⟩
  have hm := mul_mem (centralizer_le_normalizer _ hs) ht
  change scalar x.1 * special x.2.val ∈ _ at hm
  change SemidirectProduct.inl
    (GeneralLinearGroup.scalar (Fin 2) x.1 * SpecialLinearGroup.toGL x.2.val) ∈ _
  rw [map_mul]
  exact hm

/-- Two independent cubics normalize the image of any full SL₂(4) Sylow four-group. -/
theorem two_le_primeRank_sylow_normalizer (Q : Sylow 2 SL) :
    2 ≤ primeRank 3 (Subgroup.normalizer
      (((Q : Subgroup SL).map special : Subgroup Gamma) : Set Gamma)) := by
  let : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)
  have hd : 3 ∣ Nat.card (Subgroup.normalizer (Q : Set SL)) := by
    rw [normalizer_sylow_card]
    decide
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.normalizer (Q : Set SL)) 3 hd
  let C := Subgroup.zpowers b
  let : CommGroup C := IsMulCommutative.instCommGroup
  have hC : Nat.card C = 3 := (Nat.card_zpowers b).trans hb
  let f := (sylowNormalizerPair Q).comp ((MonoidHom.id Fˣ).prodMap C.subtype)
  let A := Subgroup.normalizer (((Q : Subgroup SL).map special : Subgroup Gamma) : Set Gamma)
  have hm (x : Fˣ × C) : f x ∈ A := sylowNormalizerPair_mem Q (x.1, x.2.val)
  let j : Fˣ × C →* A := f.codRestrict A hm
  have hj : Function.Injective j := by
    intro x y h
    have he := sylowNormalizerPair_injective Q (congrArg Subtype.val h)
    change (x.1, x.2.val) = (y.1, y.2.val) at he
    have h1 : x.1 = y.1 := congrArg (fun z : Fˣ × Subgroup.normalizer (Q : Set SL) => z.1) he
    have h2 : x.2.val = y.2.val := congrArg (fun z : Fˣ × Subgroup.normalizer (Q : Set SL) => z.2) he
    exact Prod.ext h1 (Subtype.ext h2)
  have hp (x : Fˣ × C) : x ^ 3 = 1 := by
    apply Prod.ext
    · exact units_cube x.1
    · have hc : x.2 ^ Nat.card C = 1 := pow_card_eq_one'
      rwa [hC] at hc
  have hc : Nat.card (Fˣ × C) = 3 ^ 2 := by
    rw [Nat.card_prod, hC, Nat.card_eq_fintype_card, card_labels]
    decide
  exact primeRank_ge_of_elementary_embedding hp hc j hj

/-- Transfer the two-cubic normalizer witness through an actual source marking. -/
theorem two_le_primeRank_normalizer_of_marking
    {H : Type*} [Group H] [Finite H] (R : Subgroup H) (e : H ≃* Gamma)
    (Q : Sylow 2 SL)
    (hR : R.map e.toMonoidHom = (Q : Subgroup SL).map special) :
    2 ≤ primeRank 3 (Subgroup.normalizer (R : Set H)) := by
  let : Finite Gamma := Nat.finite_of_card_ne_zero (by rw [gamma_card]; decide)
  let N := Subgroup.normalizer (R : Set H)
  have he : N.map e.toMonoidHom = Subgroup.normalizer
      (((Q : Subgroup SL).map special : Subgroup Gamma) : Set Gamma) := by
    change (Subgroup.normalizer (R : Set H)).map e.toMonoidHom = _
    rw [Subgroup.map_equiv_normalizer_eq, hR]
  let d := (N.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr he)
  rw [Theory.GroupTheory.primeRank_equiv 3 d]
  exact two_le_primeRank_sylow_normalizer Q

end Representation.SL2FourNatural.SemilinearNormalizer
