module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Inputs
public import Theory.Representation.BinaryOffender.CentralKernelImage
public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.NormalForm
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.OddCentralInvolutionLifting
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.GroupTheory.PrimeRankHom

-- The existing central-quotient comparison has no public equation on
-- representatives. Access its body only for the private compatibility lemma below.
import all Theory.Representation.BinaryOffender.CentralKernelImage

/-!
# Lifting outer elementary SL₃ actors and selecting inner companions

Normalizer conjugation acts on the actual representation image, which may be a
proper central quotient of SL₃. Perfectness identifies the image's central
quotient with PSL₃. Binary standard-automorphism coverage then lifts the action
to SL₃, and uniqueness of maps from a perfect group to a central extension
recovers the literal intertwining equation for the original operator.

The diagonal outer subgroup has exponent three. Modulo that subgroup the
cyclic field image and the graph involution give two-rank at most two.
Consequently an elementary actor of larger rank has a nontrivial inner member:
binary Schur's lemma removes only the centralizing involution, without assuming
that the whole normalizer action is faithful. The odd central kernel gives a
unique involutory preimage of this member; commutativity of the original actor
makes that preimage fixed by the lifted outer automorphism.

Source: Guralnick–Malle, *Classification of 2F-modules II*, Proposition 4.8,
steps 2–5, manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
The concrete automorphism actions and their coverage are reused from the
attributed projective matrix development, including binary degrees one and two.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3.OuterSolvable
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
variable (F : Type*) [Field F] [Finite F]

private theorem cyclic_primeRank_le_one {G : Type*} [Group G] [Finite G] [IsCyclic G] :
    primeRank 2 G ≤ 1 := by
  let P : Sylow 2 G := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic inferInstance

private theorem quotient_rank : primeRank 2 (StandardOuterQuotient F) ≤ 2 := by
  let := standardOuterQuotient_isMulCommutative F
  let : CommGroup (StandardOuterQuotient F) := IsMulCommutative.instCommGroup
  let C := (fieldStandardQuotient F).range
  let : IsCyclic C := fieldStandardQuotient_isCyclic F
  let q := QuotientGroup.mk' C
  let D := zpowers (graphStandardQuotient F)
  have hsurj : Function.Surjective (q.comp D.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have h := congrArg (Subgroup.map q) (standardOuterQuotient_generators F)
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective C)] at h
    have hz : C.map q = ⊥ := QuotientGroup.map_mk'_self C
    change C.map q ⊔ D.map q = ⊤ at h
    simpa only [hz, bot_sup_eq] using h
  have hi : C.index ≤ 2 ^ 1 := by
    change Nat.card (StandardOuterQuotient F ⧸ C) ≤ 2
    exact (Nat.card_le_card_of_surjective _ hsurj).trans (by
      change Nat.card (zpowers (graphStandardQuotient F)) ≤ 2
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one (graphStandardQuotient_sq F)))
  have hC := cyclic_primeRank_le_one (G := C)
  have hQ := primeRank_le_add_of_index_le (p := 2) C hi
  omega

omit [Finite F] in
private theorem diagonal_cube (x : innerDiagonalOuter F) : x ^ 3 = 1 := by
  apply Subtype.ext
  obtain ⟨m, hm⟩ := x.property
  change (x : MulAut.Outer PSL(3,F)) ^ 3 = 1
  rw [← hm]
  change (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F m)) ^ 3 = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact Matrix.PSL3.OddInvolutionFixed.linearConj_cube_inner m

private theorem standard_rank : primeRank 2 (standardOuter F) ≤ 2 := by
  let D := (innerDiagonalOuter F).subgroupOf (standardOuter F)
  let q := QuotientGroup.mk' D
  have hd : primeRank 2 D ≤ 0 := by
    apply primeRank_le_of_pow_eq_one_subset (⊥ : Subgroup D) (by simp)
    intro x hx
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      change (x.val.val) ^ 3 = 1
      exact congrArg Subtype.val (diagonal_cube F ⟨x.val.val, x.property⟩)
    have hx1 : x = 1 := by simpa only [pow_succ, hx, one_mul] using hx3
    exact hx1
  have h := primeRank_le_ker_add (p := 2) q
  rw [show q.ker = D from QuotientGroup.ker_mk' D] at h
  have hQ := quotient_rank F
  change primeRank 2 (standardOuter F ⧸ D) ≤ 2 at hQ
  omega

/-- Odd diagonal automorphisms contribute no elementary two-rank; only the
cyclic field and graph images remain. -/
private theorem outer_rank {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2 ^ m) :
    primeRank 2 (MulAut.Outer PSL(3,F)) ≤ 2 := by
  have htop : standardOuter F = ⊤ := by
    rw [standardOuter, standard_eq_top_of_two_power_card F hm hF,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let e : standardOuter F ≃* MulAut.Outer PSL(3,F) :=
    (MulEquiv.subgroupCongr htop).trans (Subgroup.topEquiv)
  rw [← primeRank_equiv 2 e]
  exact standard_rank F
end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

noncomputable section
open Representation Representation.BinaryOffender Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.OuterSolvable
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

private instance coverPerfect : Group.IsPerfect SL(3,B.Carrier) := Atlas.sl_perfect 3 (by decide)
private instance imagePerfect : Group.IsPerfect (actionImage σ) :=
  Group.IsPerfect.ofSurjective σ.asGroupHom.rangeRestrict_surjective

private theorem centerAction_eq : centerAction B.Carrier =
    MulAut.centralQuotientAction (MulEquiv.refl PSL(3,B.Carrier)) := by
  ext a x
  induction x using QuotientGroup.induction_on with
  | H x =>
    change centerAction B.Carrier a (QuotientGroup.mk x) =
      MulAut.centralQuotientAction (MulEquiv.refl PSL(3,B.Carrier)) a
        ((MulEquiv.refl PSL(3,B.Carrier)) (QuotientGroup.mk' (center SL(3,B.Carrier)) x))
    rw [centerAction_mk, MulAut.centralQuotientAction_apply]
    rfl

private theorem centerAction_bijective : Function.Bijective (centerAction B.Carrier) := by
  refine ⟨?_, ?_⟩
  · rw [centerAction_eq]
    exact MulAut.centralQuotientAction_injective _
  · apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← standard_eq_top_of_two_power_card B.Carrier B.degree_pos B.card_eq]
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨m, rfl⟩
      exact ⟨linearConjSL B.Carrier m, rfl⟩
    · rintro _ ⟨τ, rfl⟩
      refine ⟨Atlas.fieldEquivSL 3 τ, ?_⟩
      ext x
      induction x using QuotientGroup.induction_on with
      | H x =>
        rw [centerAction_mk]
        exact (Atlas.fieldEquivPSL_mk 3 τ x).symm
    · exact zpowers_le.mpr ⟨graphSL B.Carrier, rfl⟩

private def coverAutEquiv : MulAut SL(3,B.Carrier) ≃* MulAut PSL(3,B.Carrier) :=
  MulEquiv.ofBijective (centerAction B.Carrier) (centerAction_bijective B)

/-- Compatibility of the existing comparison with the literal cover map.
This is the only use of the internal import of `CentralKernelImage`. -/
private theorem imageQuotient_mk (hk : σ.ker ≤ center SL(3,B.Carrier))
    (g : SL(3,B.Carrier)) :
    simpleQuotientEquivImage σ hk (QuotientGroup.mk' (center SL(3,B.Carrier)) g) =
      QuotientGroup.mk' (center (actionImage σ)) (actionHom σ g) := by
  rfl

private def projectiveConjugation (hk : σ.ker ≤ center SL(3,B.Carrier)) :
    linearNormalizer σ →* MulAut PSL(3,B.Carrier) :=
  (MulAut.centralQuotientAction (simpleQuotientEquivImage σ hk).symm).comp
    (actionImage σ).normalizerMonoidHom

private def coverConjugation (hk : σ.ker ≤ center SL(3,B.Carrier)) :
    linearNormalizer σ →* MulAut SL(3,B.Carrier) :=
  (coverAutEquiv B).symm.toMonoidHom.comp (projectiveConjugation B σ hk)

private theorem coverConjugation_projective (hk : σ.ker ≤ center SL(3,B.Carrier))
    (t : linearNormalizer σ) :
    centerAction B.Carrier (coverConjugation B σ hk t) =
      projectiveConjugation B σ hk t :=
  (coverAutEquiv B).apply_symm_apply _

private theorem coverConjugation_image (hk : σ.ker ≤ center SL(3,B.Carrier))
    (t : linearNormalizer σ) (g : SL(3,B.Carrier)) :
    actionHom σ (coverConjugation B σ hk t g) =
      (actionImage σ).normalizerMonoidHom t (actionHom σ g) := by
  let e := simpleQuotientEquivImage σ hk
  have he (g : SL(3,B.Carrier)) : e (QuotientGroup.mk' (center SL(3,B.Carrier)) g) =
      QuotientGroup.mk' (center (actionImage σ)) (actionHom σ g) := imageQuotient_mk B σ hk g
  have he' (g : SL(3,B.Carrier)) : e.symm
      (QuotientGroup.mk' (center (actionImage σ)) (actionHom σ g)) =
        QuotientGroup.mk' (center SL(3,B.Carrier)) g := by rw [← he, e.symm_apply_apply]
  let α := coverConjugation B σ hk t
  let β := (actionImage σ).normalizerMonoidHom t
  have hproj : (QuotientGroup.mk' (center (actionImage σ))).comp
      ((actionHom σ).comp α.toMonoidHom) =
    (QuotientGroup.mk' (center (actionImage σ))).comp (β.toMonoidHom.comp (actionHom σ)) := by
    ext x
    change QuotientGroup.mk' _ (actionHom σ (α x)) = QuotientGroup.mk' _ (β (actionHom σ x))
    apply e.symm.injective
    rw [he']
    have hh := MulAut.centralQuotientAction_apply e.symm β (actionHom σ x)
    rw [he'] at hh
    rw [← hh]
    change QuotientGroup.mk' _ (α x) = projectiveConjugation B σ hk t (QuotientGroup.mk' _ x)
    rw [← coverConjugation_projective]
    rfl
  have hh := PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    (QuotientGroup.mk' (center (actionImage σ))) (by rw [QuotientGroup.ker_mk'])
    ((actionHom σ).comp α.toMonoidHom) (β.toMonoidHom.comp (actionHom σ)) hproj
  exact DFunLike.congr_fun hh g

private theorem coverConjugation_intertwines (hk : σ.ker ≤ center SL(3,B.Carrier))
    (t : linearNormalizer σ) (g : SL(3,B.Carrier)) :
    t.val.val * σ g = σ (coverConjugation B σ hk t g) * t.val.val := by
  have h := congrArg Subtype.val (coverConjugation_image B σ hk t g)
  change σ.asGroupHom (coverConjugation B σ hk t g) =
    t.val * σ.asGroupHom g * t.val⁻¹ at h
  have hh : t.val * σ.asGroupHom g = σ.asGroupHom (coverConjugation B σ hk t g) * t.val := by
    rw [h, inv_mul_cancel_right]
  exact congrArg Units.val hh

/-- Every square-one normalizer operator has an involutory lift on the central cover. -/
private def liftedInvolution (hk : σ.ker ≤ center SL(3,B.Carrier))
    (t : linearNormalizer σ) (ht : t ^ 2 = 1) : LiftedInvolution B σ t where
  automorphism := coverConjugation B σ hk t
  actor_square := ht
  square := by rw [← map_pow, ht, map_one]
  intertwines := coverConjugation_intertwines B σ hk t


private theorem actionHom_kernel_central (hk : σ.ker ≤ center SL(3,B.Carrier)) :
    (actionHom σ).ker ≤ center SL(3,B.Carrier) := by
  intro g hg
  apply hk
  exact congrArg (fun x : actionImage σ => x.val.val) hg

private theorem actionHom_kernel_odd (hk : σ.ker ≤ center SL(3,B.Carrier)) :
    Odd (Nat.card (actionHom σ).ker) :=
  Odd.of_dvd_nat (Matrix.SL3.odd_card_center B.Carrier)
    (Subgroup.card_dvd_of_le (actionHom_kernel_central B σ hk))

private theorem inner_square_lift (α : MulAut SL(3,B.Carrier)) (ha : α ^ 2 = 1)
    (hi : ∃ x, α = MulAut.conj x) : ∃ x, x ^ 2 = 1 ∧ α = MulAut.conj x := by
  obtain ⟨x, hx⟩ := hi
  have hx2 : MulAut.conj (x ^ 2) = 1 := by rw [map_pow, ← hx, ha]
  have hc : x ^ 2 ∈ center SL(3,B.Carrier) := by
    apply mem_center_iff.mpr
    intro y
    have h := MulEquiv.congr_fun hx2 y
    change x ^ 2 * y * (x ^ 2)⁻¹ = y at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have hc3 : (x ^ 2) ^ 3 = 1 := by
    have h := orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_natCard (⟨x ^ 2, hc⟩ : center SL(3,B.Carrier))).trans
        (Matrix.SL3.card_center_dvd_three B.Carrier))
    exact congrArg Subtype.val h
  refine ⟨x ^ 3, ?_, ?_⟩
  · simpa only [← pow_mul, Nat.mul_comm] using hc3
  · rw [map_pow, ← hx, pow_succ, ha, one_mul]

private theorem operator_mem_image_of_cover_inner [IsIrreducible σ] (hk : σ.ker ≤ center SL(3,B.Carrier))
    (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hi : ∃ x, coverConjugation B σ hk t = MulAut.conj x) : t.val ∈ actionImage σ := by
  have ha : coverConjugation B σ hk t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  obtain ⟨x, hx2, hx⟩ := inner_square_lift B (coverConjugation B σ hk t) ha hi
  let y := σ.asGroupHom x
  have hy2 : y ^ 2 = 1 := by rw [← map_pow, hx2, map_one]
  have ht2 : t.val ^ 2 = 1 := congrArg Subtype.val ht
  have he (g : SL(3,B.Carrier)) :
      t.val * σ.asGroupHom g * t.val⁻¹ = y * σ.asGroupHom g * y⁻¹ := by
    have hh := congrArg Subtype.val (coverConjugation_image B σ hk t g)
    change σ.asGroupHom (coverConjugation B σ hk t g) =
      t.val * σ.asGroupHom g * t.val⁻¹ at hh
    rw [hx, MulAut.conj_apply, map_mul, map_mul, map_inv] at hh
    exact hh.symm
  have hty : Commute t.val y := by
    have h := he x
    change t.val * y * t.val⁻¹ = y * y * y⁻¹ at h
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hu2 : (y⁻¹ * t.val) ^ 2 = 1 := by
    rw [hty.symm.inv_left.mul_pow, inv_pow, hy2, ht2, inv_one, one_mul]
  have huc : y⁻¹ * t.val ∈ centralizer (actionImage σ : Set _) := by
    apply mem_centralizer_iff.mpr
    rintro g ⟨z, rfl⟩
    have hconj : (y⁻¹ * t.val) * σ.asGroupHom z * (y⁻¹ * t.val)⁻¹ = σ.asGroupHom z := by
      calc
        _ = y⁻¹ * (t.val * σ.asGroupHom z * t.val⁻¹) * y := by group
        _ = y⁻¹ * (y * σ.asGroupHom z * y⁻¹) * y := by rw [he]
        _ = _ := by group
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  let : IsIrreducible ((Units.coeHom (Module.End (ZMod 2) V)).comp (actionImage σ).subtype) :=
    imageRepresentation_isIrreducible σ inferInstance
  have hu := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    (Units.coeHom (Module.End (ZMod 2) V)) (actionImage σ)
    (fun _ _ h => Units.ext h) hu2 huc
  exact ⟨x, (inv_mul_eq_one.mp hu)⟩

/-- An inner member of the elementary actor lifts uniquely to a fixed involution
of SL₃. The displayed operator remains the original member of the actor. -/
private theorem companion_of_inner_member (hk : σ.ker ≤ center SL(3,B.Carrier))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (t u : A) (hu : u ≠ 1) (hui : u.val.val ∈ actionImage σ) :
    HasInnerCompanion B σ A (coverConjugation B σ hk t.val) := by
  let : IsElementaryAbelian 2 A := hA.2
  let b : actionImage σ := ⟨u.val.val, hui⟩
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    exact congrArg (fun a : linearNormalizer σ => a.val)
      (elemPow_eq_one_of_isElementaryAbelian u.val u.property)
  obtain ⟨x, hx, hx2⟩ := OddCentralLifting.exists_involution_lift (actionHom σ)
    (actionHom_kernel_odd B σ hk) σ.asGroupHom.rangeRestrict_surjective b hb2
  refine ⟨u, hu, x, hx2, ?_, (congrArg Subtype.val hx).symm⟩
  apply OddCentralLifting.involution_lift_unique (actionHom σ)
    (actionHom_kernel_odd B σ hk) (actionHom_kernel_central B σ hk)
  · rw [← map_pow, hx2, map_one]
  · exact hx2
  · rw [coverConjugation_image, hx]
    apply Subtype.ext
    change t.val.val * u.val.val * t.val.val⁻¹ = u.val.val
    have hcomm : t.val.val * u.val.val = u.val.val * t.val.val :=
      congrArg (fun a : A => a.val.val) (IsMulCommutative.is_comm.comm t u)
    rw [hcomm, mul_inv_cancel_right]


private theorem exists_inner_member [IsIrreducible σ] [FiniteDimensional (ZMod 2) V]
    (hk : σ.ker ≤ center SL(3,B.Carrier))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) (hr : 2 < rank A) :
    ∃ u : A, u ≠ 1 ∧ u.val.val ∈ actionImage σ := by
  classical
  let : IsElementaryAbelian 2 A := hA.2
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let φ : A →* MulAut.Outer PSL(3,B.Carrier) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,B.Carrier))).comp
      ((projectiveConjugation B σ hk).comp A.subtype)
  by_contra hn
  have hf : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro u hu
    have hγ : projectiveConjugation B σ hk u.val ∈ MulAut.innerSubgroup PSL(3,B.Carrier) :=
      (QuotientGroup.eq_one_iff _).mp hu
    obtain ⟨p, hp⟩ := hγ
    have hi : ∃ x, coverConjugation B σ hk u.val = MulAut.conj x := by
      apply (MulAut.centralQuotientAction_inner_iff (MulEquiv.refl PSL(3,B.Carrier)) _).mp
      refine ⟨p, ?_⟩
      rw [← centerAction_eq, coverConjugation_projective]
      exact hp.symm
    have hui := operator_mem_image_of_cover_inner B σ hk u.val
      (elemPow_eq_one_of_isElementaryAbelian u.val u.property) hi
    change u = 1
    by_contra hu1
    exact hn ⟨u, hu1, hui⟩
  have he : IsElementaryAbelian 2 φ.range :=
    IsElementaryAbelian.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut.Outer PSL(3,B.Carrier))).mp
    (outer_rank B.Carrier B.degree_pos B.card_eq) φ.range he
  have hcard : Nat.card A ≤ 2 ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).le.trans hc
  have hl := Nat.log_mono_right (b := 2) hcard
  have hrle : rank A ≤ 2 := by
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl
  omega

/-- Actual outer elementary actors lift to involutions on SL₃; above rank two,
an actual nontrivial component actor has a commuting involutory lift. -/
theorem lifted_outer_actors [IsIrreducible σ] [FiniteDimensional (ZMod 2) V]
    (hk : σ.ker ≤ center SL(3,B.Carrier)) : LiftedOuterActors B σ := by
  classical
  intro A hA hout
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨z, hz, hzout⟩ := SetLike.not_le_iff_exists.mp hout
  obtain ⟨t, ht, rfl⟩ := hz
  let tA : A := ⟨t, ht⟩
  let L := liftedInvolution B σ hk t
    (elemPow_eq_one_of_isElementaryAbelian t ht)
  refine ⟨tA, hzout, L, ?_⟩
  intro hr
  obtain ⟨u, hu, hui⟩ := exists_inner_member B σ hk A hA hr
  exact companion_of_inner_member B σ hk A hA tA u hu hui

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
