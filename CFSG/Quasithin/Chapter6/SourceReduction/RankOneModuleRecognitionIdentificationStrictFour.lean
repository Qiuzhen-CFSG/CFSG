module
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.SpFour
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Theory.SpecificGroups.PSp4Three.MatrixModel

/-!
# The strict catalogue's symplectic four-space exclusion

An invariant nondegenerate alternating form supplies an actual symplectic
basis and the six-letter polar action. The type-a₂ identity says every duad
is equal or disjoint from its image; a nonidentity such permutation has no
fixed letter, so it is a product of three transpositions.

If the subgroup order is divisible by ten, Cauchy supplies a five-cycle.
If it is divisible by eighteen, Sylow theory supplies a nine-subgroup.
Conjugate either into the standard coordinates. For each of the fifteen
triple transpositions, the displayed short word in these actual subgroup
generators is a nonidentity cubic centralizing it. Each identity is checked
by kernel reduction; no subgroup census is assumed. Conjugation and the
original linear intertwiner transfer the cubic's moved-plane transitivity
back to the given action and form.

This supplies the subgroup-analysis premise left explicit in `SpFour` and
discharges the last catalogue row for 6.2.19. In particular, the five-part
also produces the factor three used in the printed 15-or-18 refinement.
The subsequent strict consumer keeps the original marked moved plane.

Source: Aschbacher--Smith, G.11.2(2) and 6.2.19, printed pp.364,691
(PDF pp.375,708). The imported symplectic-basis port retains ATLAS attribution.
-/

public noncomputable section
open Subgroup Equiv Equiv.Perm
open scoped Matrix
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictFour
private abbrev S6 := Equiv.Perm (Fin 6)
local instance : Fintype (Equiv.Perm (Fin 6)) := fintypePerm

private def triples : Fin 15 → S6 := ![
  swap 0 1 * swap 2 3 * swap 4 5,
  swap 0 1 * swap 2 4 * swap 3 5,
  swap 0 1 * swap 2 5 * swap 3 4,
  swap 0 2 * swap 1 3 * swap 4 5,
  swap 0 2 * swap 1 4 * swap 3 5,
  swap 0 2 * swap 1 5 * swap 3 4,
  swap 0 3 * swap 1 2 * swap 4 5,
  swap 0 3 * swap 1 4 * swap 2 5,
  swap 0 3 * swap 1 5 * swap 2 4,
  swap 0 4 * swap 1 2 * swap 3 5,
  swap 0 4 * swap 1 3 * swap 2 5,
  swap 0 4 * swap 1 5 * swap 2 3,
  swap 0 5 * swap 1 2 * swap 3 4,
  swap 0 5 * swap 1 3 * swap 2 4,
  swap 0 5 * swap 1 4 * swap 2 3]

private def five : S6 := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4
private def left : S6 := swap 0 1 * swap 1 2
private def right : S6 := swap 3 4 * swap 4 5

private def words5 : Fin 15 → List (Fin 2) := ![
  [1, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1],
  [1, 0, 1, 1, 1, 0, 1],
  [1, 0, 1, 1, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
  [1, 0, 1, 1, 1, 0, 1],
  [1, 0, 1, 1, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1],
  [0, 1, 0, 1, 0, 1, 1, 1, 0, 1],
  [1, 1, 0, 1, 0, 1, 1],
  [1, 1, 0, 1, 0, 1, 1],
  [1, 0, 1, 1, 1, 0, 1],
  [0, 1, 0, 1, 0, 1, 1, 1, 0, 1]]

private def words9 : Fin 15 → List (Fin 3) := ![
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 2],
  [1, 1, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 1, 2],
  [1, 2],
  [1, 0, 1, 1, 2, 0, 2, 2],
  [1, 2],
  [1, 1, 2]]

private def witnessFive (i : Fin 15) : S6 := ((words5 i).map ![triples i, five]).prod
private def witnessNine (i : Fin 15) : S6 := ((words9 i).map ![triples i, left, right]).prod

private theorem five_certificate (i : Fin 15) :
    witnessFive i ^ 3 = 1 ∧ witnessFive i ≠ 1 ∧
    witnessFive i * triples i = triples i * witnessFive i := by
  fin_cases i <;> decide +kernel

private theorem nine_certificate (i : Fin 15) :
    witnessNine i ^ 3 = 1 ∧ witnessNine i ≠ 1 ∧
    witnessNine i * triples i = triples i * witnessNine i := by
  fin_cases i <;> decide +kernel

private theorem triples_exhaustive : ∀ a : S6, a ^ 2 = 1 → (∀ i, a i ≠ i) →
    ∃ j, a = triples j := by
  decide +kernel


private theorem word_mem (H : Subgroup S6) {n : ℕ} (g : Fin n → S6)
    (hg : ∀ i, g i ∈ H) (w : List (Fin n)) : (w.map g).prod ∈ H := by
  apply H.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact hg i

private theorem cubic_of_five_mem (H : Subgroup S6) (a : S6)
    (ha : a ∈ H) (ha2 : a ^ 2 = 1) (hfix : ∀ i, a i ≠ i) (hfive : five ∈ H) :
    ∃ c ∈ H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c a := by
  obtain ⟨i, rfl⟩ := triples_exhaustive a ha2 hfix
  refine ⟨witnessFive i, word_mem H ![triples i, five] ?_ (words5 i),
    five_certificate i⟩
  intro k
  fin_cases k <;> assumption

private theorem cubic_of_nine_mem (H : Subgroup S6) (a : S6)
    (ha : a ∈ H) (ha2 : a ^ 2 = 1) (hfix : ∀ i, a i ≠ i)
    (hl : left ∈ H) (hr : right ∈ H) :
    ∃ c ∈ H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c a := by
  obtain ⟨i, rfl⟩ := triples_exhaustive a ha2 hfix
  refine ⟨witnessNine i, word_mem H ![triples i, left, right] ?_ (words9 i),
    nine_certificate i⟩
  intro k
  fin_cases k <;> assumption

private theorem conjugate_no_fixed (a p : S6) (hfix : ∀ i, a i ≠ i) :
    ∀ i, (MulAut.conj p a) i ≠ i := by
  intro i hi
  have hh := congrArg p.symm hi
  exact hfix (p.symm i) (by simpa [MulAut.conj_apply, Perm.mul_apply] using hh)

private theorem cubic_transport (H : Subgroup S6) (a : S6) (e : S6 ≃* S6)
    (hc : ∃ c ∈ H.map e.toMonoidHom, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c (e a)) :
    ∃ c ∈ H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c a := by
  obtain ⟨c, ⟨b, hb, rfl⟩, hc3, hc1, hc⟩ := hc
  change e b ^ 3 = 1 at hc3
  change Commute (e b) (e a) at hc
  refine ⟨b, hb, e.injective (by simpa only [map_pow, map_one] using hc3),
    fun h => hc1 (by rw [h, map_one]), ?_⟩
  exact e.injective (by simpa only [map_mul] using hc.eq)

/-- The five-part gives an actual commuting cubic, via fifteen word identities. -/
private theorem cubic_of_five (H : Subgroup S6) (a : S6)
    (ha : a ∈ H) (ha2 : a ^ 2 = 1) (hfix : ∀ i, a i ≠ i) (hfive : 5 ∣ Nat.card H) :
    ∃ c ∈ H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c a := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 hfive
  have hg5 : (g : S6) ^ 5 = 1 := congrArg Subtype.val (hg ▸ pow_orderOf_eq_one g)
  have hg1 : (g : S6) ≠ 1 := by
    intro hh
    have : g = 1 := Subtype.ext hh
    simp [this] at hg
  have ht := cycleType_of_pow_prime_eq_one hg5
  have hn := card_cycleType_pos.mpr hg1
  have hs := (g : S6).sum_cycleType_le
  rw [ht, Multiset.sum_replicate] at hs
  simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] at hs
  have hc : (g : S6).cycleType.card = 1 := by omega
  have hconj : IsConj (g : S6) five := isConj_of_cycleType_eq (by
    rw [ht, hc]
    decide +kernel)
  obtain ⟨p, hp⟩ := isConj_iff.mp hconj
  apply cubic_transport H a (MulAut.conj p)
  apply cubic_of_five_mem _ _ (mem_map_of_mem _ ha)
    (by rw [← map_pow, ha2, map_one]) (conjugate_no_fixed a p hfix)
  rw [← hp]
  exact mem_map_of_mem (MulAut.conj p).toMonoidHom g.property

private abbrev C3 := Multiplicative (ZMod 3)
private def nineMap : C3 × C3 →* S6 where
  toFun x := left ^ x.1.toAdd.val * right ^ x.2.toAdd.val
  map_one' := by decide
  map_mul' := by decide
private theorem nineMap_injective : Function.Injective nineMap := by decide
private theorem nineMap_card : Nat.card nineMap.range = 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective nineMap_injective).toEquiv,
    Nat.card_prod]
  simp only [Nat.card_eq_fintype_card]
  decide
private theorem nineMap_left : left ∈ nineMap.range :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 3), 1), by decide⟩
private theorem nineMap_right : right ∈ nineMap.range :=
  ⟨(1, Multiplicative.ofAdd (1 : ZMod 3)), by decide⟩

/-- The nine-part gives an actual commuting cubic, using the literal Sylow nine. -/
private theorem cubic_of_nine (H : Subgroup S6) (a : S6)
    (ha : a ∈ H) (ha2 : a ^ 2 = 1) (hfix : ∀ i, a i ≠ i) (hnine : 9 ∣ Nat.card H) :
    ∃ c ∈ H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c a := by
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 2) hnine
  let Q := K.map H.subtype
  have hQ : Nat.card Q = 9 := by
    rw [card_map_of_injective H.subtype_injective, hK]
    rfl
  let S : Sylow 3 S6 := Sylow.ofCard Q (by
    rw [hQ, Nat.card_perm, Nat.card_fin]
    decide +kernel)
  let P : Sylow 3 S6 := Sylow.ofCard nineMap.range (by
    rw [nineMap_card, Nat.card_perm, Nat.card_fin]
    decide +kernel)
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq S6 S P
  have he : Q.map (MulAut.conj p).toMonoidHom = nineMap.range :=
    congrArg Sylow.toSubgroup hp
  have hle : nineMap.range ≤ H.map (MulAut.conj p).toMonoidHom := by
    rw [← he]
    exact map_mono (map_subtype_le K)
  apply cubic_transport H a (MulAut.conj p)
  exact cubic_of_nine_mem _ _ (mem_map_of_mem _ ha)
    (by rw [← map_pow, ha2, map_one]) (conjugate_no_fixed a p hfix)
    (hle nineMap_left) (hle nineMap_right)

private theorem cubic_of_order (H : Subgroup S6) (a : S6)
    (ha : a ∈ H) (ha2 : a ^ 2 = 1) (hfix : ∀ i, a i ≠ i)
    (horder : 10 ∣ Nat.card H ∨ 18 ∣ Nat.card H) :
    ∃ c ∈ H, c ^ 3 = 1 ∧ c ≠ 1 ∧ Commute c a := by
  rcases horder with h | h
  · exact cubic_of_five H a ha ha2 hfix ((by decide : 5 ∣ 10).trans h)
  · exact cubic_of_nine H a ha ha2 hfix ((by decide : 9 ∣ 18).trans h)


open Theory.SpecificGroups.SymmetricSix Representation.RankTwo

/-- The polar duad action makes every nonidentity type-a₂ element fixed-point-free
on the six letters. This uses the actual invariant form. -/
private theorem no_fixed_of_type (a : S6) (ha : a ≠ 1)
    (ht : ∀ w, polarForm w (SpFour.sixNatural a w) = 0) : ∀ i, a i ≠ i := by
  intro i hi
  apply ha
  apply Equiv.ext
  intro j
  change a j = j
  by_cases hij : i = j
  · simpa only [← hij] using hi
  obtain ⟨d, hd⟩ := duadSet_complete ({i,j} : Finset (Fin 6)) (by simp [hij])
  have hp := ht (polarVector d).val
  change polarForm (polarVector d).val (polarAction a (polarVector d).val) = 0 at hp
  rw [polarAction_vector] at hp
  rcases (polarVector_orthogonal _ _).mp hp with he | he
  · have hh := congrArg duadSet he
    rw [duadSet_smul, hd, Finset.image_insert, Finset.image_singleton, hi] at hh
    have hm : a j ∈ ({i,j} : Finset (Fin 6)) := hh.symm ▸ (by simp)
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact (hij (a.injective (hm.trans hi.symm)).symm).elim
    · exact Finset.mem_singleton.mp hm
  · have hm : i ∈ duadSet d ∩ duadSet (a • d) := by
      rw [duadSet_smul, hd]
      simp [hi]
    have hz := Finset.card_eq_zero.mp he.2
    rw [hz] at hm
    simp at hm

private theorem conjugate_standard (a : S6) (ha2 : a ^ 2 = 1) (hfix : ∀ i, a i ≠ i) :
    IsConj a SpFour.a2 := by
  obtain ⟨i, rfl⟩ := triples_exhaustive a ha2 hfix
  apply isConj_of_cycleType_eq
  fin_cases i <;> decide +kernel

/-- The original order clause supplies the cubic, rather than assuming it as
an additional subgroup-analysis input. -/
private theorem subgroup_transitive (H : Subgroup S6) (a : H)
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (ht : ∀ w, polarForm w (SpFour.sixNatural a w) = 0)
    (hr : Module.finrank (ZMod 2) (movedSpace (SpFour.sixNatural.comp H.subtype) a) = 2)
    (ho : 10 ∣ Nat.card H ∨ 18 ∣ Nat.card H) :
    StabilizerTransitive (SpFour.sixNatural.comp H.subtype)
      (movedSpace (SpFour.sixNatural.comp H.subtype) a) := by
  have hfix := no_fixed_of_type a (fun hh => ha1 (Subtype.ext hh)) ht
  obtain ⟨p, hp⟩ := isConj_iff.mp (conjugate_standard a (congrArg Subtype.val ha2) hfix)
  let K := H.map (MulAut.conj p).toMonoidHom
  let e : H ≃* K := H.equivMapOfInjective _ (MulAut.conj p).injective
  have hK : 10 ∣ Nat.card K ∨ 18 ∣ Nat.card K := by
    have hcK : Nat.card K = Nat.card H := card_map_of_injective
      (f := (MulAut.conj p).toMonoidHom) (MulAut.conj p).injective
    rwa [hcK]
  have hA : SpFour.a2 ∈ K := hp ▸ mem_map_of_mem (MulAut.conj p).toMonoidHom a.property
  have hfixA : ∀ i : Fin 6, SpFour.a2 i ≠ i := by decide
  obtain ⟨c, hc, hc3, hc1, hcomm⟩ := cubic_of_order K _ hA SpFour.a2_sq hfixA hK
  have analysis : SpFour.SubgroupAnalysis K := ⟨hK, hA,
    ⟨⟨c,hc⟩, Subtype.ext hc3, fun hh => hc1 (congrArg Subtype.val hh), hcomm⟩⟩
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv (SpFour.sixNatural.asGroupHom p)
  apply SpFour.stabilizerTransitive_of_actual_model
    (SpFour.sixNatural.comp H.subtype) analysis e f ?_ a hp hr
  intro g w
  change SpFour.sixNatural p (SpFour.sixNatural g w) =
    SpFour.sixNatural (p * g * p⁻¹) (SpFour.sixNatural p w)
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]


open Representation

private theorem coordinates {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4) (B : LinearMap.BilinForm (ZMod 2) V)
    (halt : B.IsAlt) (hn : B.Nondegenerate)
    (hp : ∀ g v w, B (ρ g v) (ρ g w) = B v w) :
    ∃ E : V ≃ₗ[ZMod 2] SpFour.W, ∃ j : G →* S6, Function.Injective j ∧
      (∀ g v, E (ρ g v) = SpFour.sixNatural (j g) (E v)) ∧
      ∀ v w, polarForm (E v) (E w) = B v w := by
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry 2 B halt hn hd
  let σ : Representation (ZMod 2) G SpFour.W :=
    e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (g : G) : f g ∈ Matrix.symplecticGroup (Fin 2) (ZMod 2) := by
    apply Matrix.PSp4Three.mem_iff_preserves.mpr
    intro v w
    change Matrix.PSp4Three.form ((LinearMap.toMatrix' (σ g)) *ᵥ v)
      ((LinearMap.toMatrix' (σ g)) *ᵥ w) = _
    rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    change Matrix.PSp4Three.form (e (ρ g (e.symm v))) (e (ρ g (e.symm w))) = _
    rw [e.map_app, hp]
    exact (e.map_app (e.symm w) (e.symm v)).symm.trans (by simp)
  let j : G →* SpFour.Sp4 := f.codRestrict _ hpres
  have hj : Function.Injective j := by
    intro a b h
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val h
  let k : G →* S6 :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp j
  refine ⟨e.toLinearEquiv, k,
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hj, ?_, ?_⟩
  · intro g v
    change e (ρ g v) = SpFour.sixNatural
      (Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm (j g)) (e v)
    rw [← SpFour.actualNatural_equivariant]
    change e (ρ g v) = LinearMap.toMatrix' (σ g) *ᵥ e v
    rw [LinearMap.toMatrix'_mulVec]
    change e (ρ g v) = e (ρ g (e.symm (e v)))
    exact congrArg (fun z => e (ρ g z)) (e.toLinearEquiv.symm_apply_apply v).symm
  · intro v w
    have hforms : Matrix.PSp4Three.form (n := 2) (F := ZMod 2) = polarForm := by
      unfold Matrix.PSp4Three.form polarForm
      congr 1
      ext i j
      exact CharTwo.neg_eq _
    change polarForm (e v) (e w) = B v w
    rw [← hforms]
    exact e.map_app w v

/-- The complete four-dimensional exclusion on the actual symplectic action.
The order clause produces the required cubic inside the actual actor. -/
theorem transitive_of_four_dimension {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (B : LinearMap.BilinForm (ZMod 2) V)
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (hAlt : B.IsAlt) (hND : B.Nondegenerate)
    (hpres : ∀ g v w, B (ρ g v) (ρ g w) = B v w)
    (a : G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (ht : ∀ w, B w (ρ a w) = 0)
    (hr : Module.finrank (ZMod 2) (movedSpace ρ a) = 2)
    (ho : 10 ∣ Nat.card G ∨ 18 ∣ Nat.card G) :
    StabilizerTransitive ρ (movedSpace ρ a) := by
  obtain ⟨E, j, hj, hE, hB⟩ := coordinates ρ hf hd B hAlt hND hpres
  let e : G ≃* j.range := MonoidHom.ofInjective hj
  let τ : Representation (ZMod 2) j.range SpFour.W := SpFour.sixNatural.comp j.range.subtype
  have he (g : G) (w : V) : E (ρ g w) = τ (e g) (E w) := hE g w
  apply stabilizerTransitive_transport ρ τ e E he a
  apply subgroup_transitive j.range (e a) (by rw [← map_pow, ha2, map_one])
    (fun hh => ha1 (e.injective (hh.trans (map_one e).symm))) ?_ ?_ ?_
  · intro w
    obtain ⟨v, rfl⟩ := E.surjective w
    change polarForm (E v) (τ (e a) (E v)) = 0
    rw [← he, hB, ht]
  · exact (finrank_movedSpace_transport ρ τ e E he a).symm.trans hr
  · simpa only [Nat.card_congr e.toEquiv] using ho

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.StrictFour
