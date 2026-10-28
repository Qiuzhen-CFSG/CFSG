module

public import Theory.Representation.SU3.CubicDegree.InnerActors.RootGeometry
public import Theory.Representation.BinaryOffender.CentralKernelImage
public import Theory.Representation.BinaryOffender.TwoWeightMaximizer
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.Representation.NormalInvariants

/-!
# Reducing the inner SU₃ actor bound to root geometry

An elementary actor in the actual linear image lifts isomorphically through
SU₃'s odd central action kernel. Its fixed space is unchanged. Within a root
group, maximize `|B|² |C_V(B)|`; normalizer irreducibility makes the largest
maximizer the whole root group. Three generating conjugates then give
`dim V ≤ 3 * (2*s)`. Irreducibility and the central kernel exclude global
fixed vectors, including for projective actions and the endpoint `s=2`.

The root control and three-conjugate generation inputs remain explicit;
this module does not assert their concrete SU₃ instances. The source
application uses the literal central cover in Chapter K's
`UnitaryRecognition.CubicDegree.InnerActors`.

Source: Guralnick--Malle, Classification of 2F-modules II, Lemma 2.1;
Aschbacher--Smith K.1 and K.3.3, printed pp.451--453,456. This is a
root-geometric route to the degree consequence, without an absolutely
irreducible module classification or Schur-field descent.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
namespace Representation.SU3.CubicDegree.InnerActors
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Offender maximization and three conjugate fixed spaces bound the degree. -/
theorem finrank_le_of_root_control (σ : Representation (ZMod 2) G V)
    (hfix : fixedSpace σ ⊤ = ⊥) {s : ℕ} (hr : RootControl G s)
    (hg : ThreeRootGeneration G) (A : Subgroup G) (hA : IsElementaryTwo A)
    (hc : fixedCodim σ A ≤ 2 * rank A) : Module.finrank (ZMod 2) V ≤ 6 * s := by
  obtain ⟨P, hAP, hcard, hinv⟩ := hr A hA
  obtain ⟨B, hBP, hB, hnorm, hV⟩ := TwoWeight.exists_normalized_offender σ (sylowCenter P) hAP hA hc
  have he := hinv B hBP hB hnorm
  rw [he] at hV
  obtain ⟨c, hc⟩ := hg P
  have hd := TwoWeight.finrank_le_of_conjugates σ hfix hV hcard.le c hc
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Lift an inner normalizer actor through the actual action homomorphism.
The lift preserves both its rank and its literal fixed subspace. -/
theorem exists_lifted_inner_actor (σ : Representation (ZMod 2) G V)
    (hk : Nat.Coprime 2 (Nat.card (actionHom σ).ker))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hinner : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    ∃ B : Subgroup G, IsElementaryTwo B ∧ rank B = rank A ∧
      fixedSpace σ B = fixedSpace (normalizerRepresentation σ) A := by
  let a : A →* actionImage σ :=
    { toFun x := ⟨x.val.val, hinner x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have ha : Function.Injective a := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : actionImage σ => z.val) he
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 a.range :=
    IsElementaryAbelian.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  obtain ⟨B, hB, hmap, hcard⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    (actionHom σ) σ.asGroupHom.rangeRestrict_surjective hk a.range
  have hca : Nat.card a.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).symm
  have hB0 : B ≠ ⊥ := by
    intro hb
    apply hA.1
    apply eq_bot_of_card_eq
    rw [← hca, ← hcard, hb, card_bot]
  refine ⟨B, ⟨hB0, hB⟩, ?_, ?_⟩
  · unfold rank
    rw [hcard, hca]
  · rw [← fixedSpace_actionSubgroup σ B]
    change fixedSpace (imageRepresentation σ) (B.map (actionHom σ)) = _
    rw [hmap]
    ext v
    constructor
    · intro hv x
      exact hv ⟨a x, ⟨x, rfl⟩⟩
    · intro hv ⟨_, x, rfl⟩
      exact hv x

variable {F : Type*} [Field F] [Finite F]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))

include hs hcard hconj

omit [FiniteDimensional (ZMod 2) V] in
/-- Every central action kernel of binary SU₃ has odd order. -/
theorem action_kernel_coprime (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hk : σ.ker ≤ center J.specialSubgroup) :
    Nat.Coprime 2 (Nat.card (actionHom σ).ker) := by
  have hz := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  have hle : (actionHom σ).ker ≤ J.specialToProjective.ker := by
    rw [hz]
    intro g hg
    apply hk
    change σ g = 1
    simpa only [imageRepresentation_actionHom, map_one] using
      congrArg (imageRepresentation σ) hg
  exact (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker).of_dvd_right
    (card_dvd_of_le hle)

omit [FiniteDimensional (ZMod 2) V] in
/-- An irreducible central-kernel SU₃ action has no global fixed vectors. -/
theorem fixedSpace_top_eq_bot (σ : Representation (ZMod 2) J.specialSubgroup V)
    (hi : σ.IsIrreducible) (hk : σ.ker ≤ center J.specialSubgroup) :
    fixedSpace σ ⊤ = ⊥ := by
  let : σ.IsIrreducible := hi
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 s (by omega) hcard hconj
  have hq : 2 < 2 ^ s := by
    have hh : 2 ^ 2 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs
    omega
  let : Theory.GroupTheory.IsQuasisimple J.specialSubgroup :=
    J.special_isQuasisimple_of_fixed_card hq hcard hfixed
  let : Nontrivial (actionImage σ) := actionImage_nontrivial_of_central_kernel σ hk
  by_contra hn
  have hker := σ.le_ker_of_normal_invariants_ne_bot ⊤ hn
  obtain ⟨x, hx⟩ := exists_ne (1 : actionImage σ)
  obtain ⟨g, hg⟩ := σ.asGroupHom.rangeRestrict_surjective x
  apply hx
  rw [← hg]
  apply Subtype.ext
  apply Units.ext
  exact hker (mem_top g)

/-- Conditional inner-actor estimate: the only remaining premises are the
two concrete group-geometric inputs. Cubicity is unnecessary for this route. -/
theorem finrank_le_of_inner_actor_of_root_geometry
    (hr : RootControl J.specialSubgroup s) (hg : ThreeRootGeneration J.specialSubgroup)
    (σ : Representation (ZMod 2) J.specialSubgroup V) (hi : σ.IsIrreducible)
    (hk : σ.ker ≤ center J.specialSubgroup)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hc : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hinner : A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    Module.finrank (ZMod 2) V ≤ 6 * s := by
  obtain ⟨B, hB, hrank, hfix⟩ := exists_lifted_inner_actor σ
    (action_kernel_coprime J hs hcard hconj σ hk) A hA hinner
  apply finrank_le_of_root_control σ (fixedSpace_top_eq_bot J hs hcard hconj σ hi hk) hr hg B hB
  change Module.finrank (ZMod 2) (V ⧸ fixedSpace σ B) ≤ 2 * rank B
  rw [hfix, hrank]
  exact hc
end Representation.SU3.CubicDegree.InnerActors
