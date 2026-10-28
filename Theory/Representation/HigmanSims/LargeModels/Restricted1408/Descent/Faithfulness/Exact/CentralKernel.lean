module
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Core
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound.TwoPrimary
public import Theory.SpecificGroups.J2HSMultipliers.HSUpperBound
public import Theory.SpecificGroups.J2HSMultipliers.HSDoubleCover
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations

/-!
# Faithfulness of the HS presentation from centrality of its kernel

The relations of orders 2, 5 and 11 make the literal ATLAS presentation
perfect. Its canonical map to the degree-100 carrier is therefore injective
once its kernel is central. To prove this, use the finite universal perfect
central cover of the carrier. The proved multiplier upper bound and the
concrete central double cover identify that universal cover with the double
cover. The latter has a lift of `(a * b²)⁵` whose square is the nonidentity
central sign. The source relation `(a * b²)¹⁰ = 1` forces this sign to vanish
in the presented group, so its map to the carrier has trivial kernel.

No finiteness, cardinal bound, model identification or simplicity hypothesis
is imposed on the presentation. Kernel centrality remains an explicit input;
the centralizer-index argument in ATLAS `HSG1-P1.M` is its intended producer.
The final application uses the already checked degree-1408 matrix relations.
Source: `../../source/HSG1-P1.M`, with the retained attribution, and the
independently proved HS multiplier and double-cover modules imported above.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation
open Subgroup
private theorem square_a : generator false ^ 2 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 0
private theorem fifth_b : generator true ^ 5 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 1
private theorem eleventh_ab : (generator false * generator true) ^ 11 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 2
private theorem images_one {B : Type*} [CommGroup B] (f : Universal →* B) :
    f (generator false) = 1 ∧ f (generator true) = 1 := by
  let a := f (generator false)
  let b := f (generator true)
  have ha : a ^ 2 = 1 := by change f (generator false) ^ 2 = 1; rw [← map_pow, square_a, map_one]
  have hb : b ^ 5 = 1 := by change f (generator true) ^ 5 = 1; rw [← map_pow, fifth_b, map_one]
  have hab : (a*b) ^ 11 = 1 := by change (f (generator false) * f (generator true)) ^ 11 = 1; rw [← map_mul, ← map_pow, eleventh_ab, map_one]
  have ha11 : a ^ 11 = a := by
    calc
      a ^ 11 = (a ^ 2) ^ 5 * a := by simp [← pow_mul, ← pow_succ]
      _ = a := by rw [ha]; simp
  have hb11 : b ^ 11 = b := by
    calc
      b ^ 11 = (b ^ 5) ^ 2 * b := by simp [← pow_mul, ← pow_succ]
      _ = b := by rw [hb]; simp
  rw [mul_pow, ha11, hb11] at hab
  have heq : a = b⁻¹ := eq_inv_of_mul_eq_one_left hab
  have ha5 : a ^ 5 = 1 := by rw [heq, inv_pow, hb, inv_one]
  have ha1 : a = 1 := by
    calc
      a = (a ^ 2) ^ 2 * a := by rw [ha]; simp
      _ = a ^ 5 := by simp [← pow_mul, ← pow_succ]
      _ = 1 := ha5
  exact ⟨ha1, by simpa [ha1] using hab⟩
/-- The first three literal relators kill the entire abelianization. -/
public instance universal_isPerfect : Group.IsPerfect Universal := by
  constructor
  apply top_unique
  rw [← Faithfulness.canonical_generates]
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  have h := images_one ((Abelianization.of : Universal →* Abelianization Universal))
  cases i
  · rw [← Abelianization.ker_of]; exact h.1
  · rw [← Abelianization.ker_of]; exact h.2

private theorem card_domain {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hf : Function.Surjective f) :
    Nat.card E = Nat.card f.ker * Nat.card B := by
  simpa only [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf,
    Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup B) ≃* B).toEquiv]
    using f.ker.card_mul_index.symm

private theorem small_kernel {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    Nat.card f.ker ≤ 2 :=
  Theory.SpecificGroups.J2HSMultipliers.HS.card_kernel_le_two_of_not_four_dvd f hf hk
    (Theory.SpecificGroups.J2HSMultipliers.HS.TwoPrimary.not_four_dvd_card_kernel f hf hk
      (Theory.SpecificGroups.J2HSMultipliers.HS.kernel_isPGroup f hf hk))

private theorem square_of_small_kernel {E B : Type*} [Group E] [Group B] [Finite E]
    (f : E →* B) (hc : Nat.card f.ker ≤ 2) (x : E) (hx : x ∈ f.ker) : x ^ 2 = 1 := by
  have hp : 0 < Nat.card f.ker := Nat.card_pos
  have h : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by omega
  rcases h with h | h
  · have he : f.ker = ⊥ := Subgroup.card_eq_one.mp h
    have hx1 : x = 1 := by simpa only [he, mem_bot] using hx
    rw [hx1, one_pow]
  · have he := pow_card_eq_one' (x := (⟨x, hx⟩ : f.ker))
    rw [h] at he
    exact congrArg Subtype.val he

open PerfectCentralCovering
private theorem tenth_ab2 : (generator false * generator true ^ 2) ^ 10 = 1 := by
  simpa [word, relatorLetters, letter, pow_succ, mul_assoc] using universal_word 3

/-- The centralizer route needs only centrality of the actual canonical kernel.
Abstract finiteness and the double-cover exclusion are proved internally. -/
public theorem toCarrier_injective_of_central_kernel
    (hk : toCarrier.ker ≤ center Universal) : Function.Injective toCarrier := by
  let : Group.IsPerfect Carrier := Group.IsPerfect.ofSurjective toCarrier_surjective
  let P := universalProjection Carrier
  obtain ⟨a, ha, _⟩ := universalProjection_existsUnique_lift
    Theory.SpecificGroups.J2HSMultipliers.HS.projection
    Theory.SpecificGroups.J2HSMultipliers.HS.projection_surjective
    Theory.SpecificGroups.J2HSMultipliers.HS.projection_ker_le_center
  have has : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      Theory.SpecificGroups.J2HSMultipliers.HS.projection a
      (ha ▸ universalProjection_surjective Carrier)
      Theory.SpecificGroups.J2HSMultipliers.HS.projection_ker_le_center
  have hpcard : Nat.card P.ker ≤ 2 := small_kernel P
    (universalProjection_surjective Carrier) (universalProjection_ker_le_center Carrier)
  have hacard : Nat.card (UniversalGroup Carrier) ≤
      Nat.card Theory.SpecificGroups.J2HSMultipliers.HS.DoubleCover := by
    rw [card_domain P (universalProjection_surjective Carrier),
      card_domain Theory.SpecificGroups.J2HSMultipliers.HS.projection
        Theory.SpecificGroups.J2HSMultipliers.HS.projection_surjective,
      Theory.SpecificGroups.J2HSMultipliers.HS.kernel_card]
    exact Nat.mul_le_mul_right _ hpcard
  let e := MulEquiv.ofBijective a (has.bijective_of_nat_card_le hacard)
  obtain ⟨b, hb, _⟩ := universalProjection_existsUnique_lift toCarrier toCarrier_surjective hk
  have hbs : Function.Surjective b :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect toCarrier b
      (hb ▸ universalProjection_surjective Carrier) hk
  let : Finite Universal := Finite.of_surjective b hbs
  let f := b.comp e.symm.toMonoidHom
  have hfs : Function.Surjective f := hbs.comp e.symm.surjective
  have hfac : toCarrier.comp f = Theory.SpecificGroups.J2HSMultipliers.HS.projection := by
    apply MonoidHom.ext
    intro x
    change toCarrier (b (e.symm x)) = Theory.SpecificGroups.J2HSMultipliers.HS.projection x
    have h1 := DFunLike.congr_fun hb (e.symm x)
    have h2 := DFunLike.congr_fun ha (e.symm x)
    change Theory.SpecificGroups.J2HSMultipliers.HS.projection (e (e.symm x)) = _ at h2
    rw [e.apply_symm_apply] at h2
    exact h1.trans h2.symm
  let w := (generator false * generator true ^ 2) ^ 5
  have hw : w ^ 2 = 1 := by
    change ((generator false * generator true ^ 2) ^ 5) ^ 2 = 1
    rw [← pow_mul]
    exact tenth_ab2
  have hmap : toCarrier (f Theory.SpecificGroups.J2HSMultipliers.HS.markedLift) =
      toCarrier w := by
    rw [← MonoidHom.comp_apply, hfac,
      Theory.SpecificGroups.J2HSMultipliers.HS.markedLift_projection]
    simp only [w, map_pow, map_mul, toCarrier_generator_false, toCarrier_generator_true,
      Theory.SpecificGroups.J2HSMultipliers.HS.involution]
  have hz : f Theory.SpecificGroups.J2HSMultipliers.HS.centralSign = 1 := by
    rw [← Theory.SpecificGroups.J2HSMultipliers.HS.markedLift_sq, map_pow]
    exact (square_eq_of_map_eq_of_kernel_exponent_two toCarrier hk
      (square_of_small_kernel toCarrier (small_kernel toCarrier toCarrier_surjective hk))
      hmap).trans hw
  apply toCarrier.ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨y, rfl⟩ := hfs x
  have hy : y ∈ Theory.SpecificGroups.J2HSMultipliers.HS.projection.ker := by
    change Theory.SpecificGroups.J2HSMultipliers.HS.projection y = 1
    rw [← hfac]
    exact hx
  rcases (Theory.SpecificGroups.J2HSMultipliers.HS.projection_ker y).mp hy with rfl | rfl
  · exact map_one f
  · exact hz
/-- It suffices to centralize the first marked generator. Normality of the
kernel and the order-five/order-eleven relations then force its centralizer
to contain both marked generators. This is the premise supplied by the source
centralizer-coset argument. -/
public theorem toCarrier_injective_of_kernel_centralizes_a
    (hk : ∀ k ∈ toCarrier.ker, k * generator false = generator false * k) :
    Function.Injective toCarrier := by
  apply toCarrier_injective_of_central_kernel
  let C : Subgroup Universal := centralizer (toCarrier.ker : Set Universal)
  let f := QuotientGroup.mk' C
  have haC : generator false ∈ C := mem_centralizer_iff.mpr hk
  have ha : f (generator false) = 1 := (QuotientGroup.eq_one_iff _).mpr haC
  have hb5 : f (generator true) ^ 5 = 1 := by
    rw [← map_pow, fifth_b, map_one]
  have hb11 : f (generator true) ^ 11 = 1 := by
    have hh := congrArg f eleventh_ab
    simpa only [map_pow, map_mul, map_one, ha, one_mul] using hh
  have hb : f (generator true) = 1 := by
    calc
      f (generator true) = (f (generator true) ^ 5) ^ 2 * f (generator true) := by
        rw [hb5]; simp
      _ = f (generator true) ^ 11 := by simp [← pow_mul, ← pow_succ]
      _ = 1 := hb11
  have hC : C = ⊤ := by
    apply top_unique
    rw [← Faithfulness.canonical_generates]
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    cases i
    · exact haC
    · exact (QuotientGroup.eq_one_iff _).mp hb
  intro k hker
  apply mem_center_iff.mpr
  intro g
  have hg : g ∈ C := by rw [hC]; trivial
  exact (mem_centralizer_iff.mp hg k hker).symm

end Sporadic.LeechRelated.HS.AtlasPresentation

namespace Representation.HigmanSims.LargeModels.Restricted1408
open Sporadic.LeechRelated.HS

/-- Centrality of the literal presentation kernel supplies the remaining
presentation input for the existing degree-1408 matrix descent. -/
public theorem matrixDescentExists_of_central_kernel
    (hk : AtlasPresentation.toCarrier.ker ≤ Subgroup.center AtlasPresentation.Universal) :
    MatrixDescentExists :=
  matrixDescentExists_of_presentation
    (fun _ => AtlasPresentation.toCarrier_injective_of_central_kernel hk) matrixRelations

end Representation.HigmanSims.LargeModels.Restricted1408
