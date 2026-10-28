module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.RootDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.InnerGeometry
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.NormalizerGeometry
public import Theory.Representation.BinaryOffender.CubicFixedSpaceSaturation
public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.GroupTheory.QuasithinBasic

/-!
# The G₂ adjoint common-fixed-space obstruction

An elementary actor of rank at most `3*r` and fixed codimension at most twice
its rank forces equality with the fixed space of every nonidentity involution.
The inner calculation then embeds the actor in the pointwise kernel inside
that involution's centralizer. Its order bound `2^r` contradicts codimension
`6*r`. The outer calculation first removes field actors by their larger
codimension. Conjugating linear maps by a genuine intertwiner transports this
argument between the literal linear normalizers.

The imported root geometry and semilinear normalizer calculations discharge
both local contracts in `normalizer_obstruction`. Only the automorphism rank
bound remains an explicit input, owned by the Chapter 16 rank calculation.
`quasiequivalent_cubic_obstruction` supplies exactly the adjoint premise of
the cubic degree consumer, preserving its literal third-displacement condition.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 8.2,
pp.53–54, and Lemma 8.5, pp.55–56 of the author manuscript; see
`G2CubicDegree/Source.md`.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory CFSG.Quasithin.ChapterG.Section09
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction

private theorem strict_of_fixed_kernel
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {r : ℕ} (hr : 0 < r)
    (hd : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → 6 * r ≤ fixedCodim ρ (zpowers t))
    (hk : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → fixedCodim ρ (zpowers t) = 6 * r →
      Nat.card (involutionFixedKernel ρ t) ≤ 2 ^ r)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hAr : rank A ≤ 3 * r) :
    2 * rank A < fixedCodim ρ A := by
  by_contra! hsmall
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  have hdt := hd t ht1 ht2
  obtain ⟨hcod, heq⟩ := fixedSpace_eq_of_saturated_actor ρ ht hAr hsmall
    (by omega : 2 * (3 * r) ≤ fixedCodim ρ (zpowers t))
  have het : fixedCodim ρ (zpowers t) = 6 * r := by
    have h := congrArg (fun U : Submodule (ZMod 2) V => Module.finrank (ZMod 2) U) heq
    have ha := fixedCodim_add_finrank ρ A
    have hb := fixedCodim_add_finrank ρ (zpowers t)
    omega
  have hAK : A ≤ involutionFixedKernel ρ t := by
    intro a ha
    refine ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · exact congrArg Subtype.val (hA.2.is_comm.comm (⟨a, ha⟩ : A) (⟨t, ht⟩ : A))
    · intro v hv
      exact (show v ∈ fixedSpace ρ A from heq.symm ▸ hv) ⟨a, ha⟩
  have hcard := (Nat.card_le_card_of_injective (Subgroup.inclusion hAK)
    (Subgroup.inclusion_injective hAK)).trans (hk t ht1 ht2 het)
  have hlog := Nat.log_mono_right (b := 2) hcard
  have hAr' : rank A ≤ r := by
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hlog
  omega

private theorem normalizer_strict_of_calculations
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) G V) {r : ℕ} (hr : 0 < r)
    (hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hAut : primeRank 2 (MulAut G) ≤ 3 * r)
    (hd : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → 6 * r ≤ fixedCodim σ (zpowers t))
    (hk : ∀ t : G, t ≠ 1 → t ^ 2 = 1 → fixedCodim σ (zpowers t) = 6 * r →
      Nat.card (involutionFixedKernel σ t) ≤ 2 ^ r)
    (ho : ∀ t : linearNormalizer σ, t ^ 2 = 1 →
      t ∈ (normalizerEmbedding σ).range ∨
        7 * r ≤ fixedCodim (normalizerRepresentation σ) (zpowers t))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  by_contra! hsmall
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let : IsElementaryAbelian 2 A := hA.2
  have hσ : Function.Injective σ.asGroupHom := fun _ _ h => hf (congrArg Units.val h)
  let e : G ≃* actionImage σ := MonoidHom.ofInjective hσ
  have hbound := primeRank_linearNormalizer_le σ hi
  rw [← primeRank_equiv 2 (MulAut.congr e)] at hbound
  have hcard := (primeRank_le_iff_elementary_card_le (linearNormalizer σ)).mp
    (hbound.trans hAut) A hA.2
  have hAr : rank A ≤ 3 * r := by
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using
      Nat.log_mono_right (b := 2) hcard
  let j := normalizerEmbedding σ
  have hj : Function.Injective j := normalizerEmbedding_injective σ hf
  let B := A.comap j
  have hm : B.map j = A := by
    apply le_antisymm (map_comap_le _ _)
    intro t ht
    have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
    rcases ho t ht2 with ⟨x, hx⟩ | htlarge
    · exact ⟨x, show j x ∈ A from hx.symm ▸ ht, hx⟩
    · have hfix := Submodule.finrank_mono
        (fixedSpace_antitone (normalizerRepresentation σ) (zpowers_le.mpr ht))
      have ha := fixedCodim_add_finrank (normalizerRepresentation σ) A
      have hb := fixedCodim_add_finrank (normalizerRepresentation σ) (zpowers t)
      omega
  have hB : IsElementaryAbelian 2 B := {
    toIsMulCommutative := A.comap_injective_isMulCommutative hj
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      apply Subtype.ext
      apply hj
      change j ((x : G) ^ 2) = j 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (j x) x.property }
  have hBn : B ≠ ⊥ := by
    intro hb
    apply hA.1
    rw [← hm, hb, Subgroup.map_bot]
  have hBr : rank B = rank A := by
    rw [← hm, rank_map_injective j hj]
  have hcod : fixedCodim σ B = fixedCodim (normalizerRepresentation σ) A := by
    rw [← hm]
    exact fixedCodim_map_equivariant σ (normalizerRepresentation σ) j
      (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl) B
  have hh := strict_of_fixed_kernel σ hr hd hk B ⟨hBn, hB⟩ (hBr ▸ hAr)
  rw [hBr, hcod] at hh
  omega

section Transport
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) G V) (τ : Representation (ZMod 2) D W)

private theorem normalizer_equivalence (e : G ≃* D) (f : V ≃ₗ[ZMod 2] W)
    (h : ∀ g v, f (ρ g v) = τ (e g) (f v)) :
    ∃ j : linearNormalizer ρ ≃* linearNormalizer τ,
      ∀ t v, f (normalizerRepresentation ρ t v) = normalizerRepresentation τ (j t) (f v) := by
  let c := Units.mapEquiv f.conjRingEquiv.toMulEquiv
  have him : (actionImage ρ).map c.toMonoidHom = actionImage τ := by
    apply conjugate_action_image τ ρ e.symm.toMonoidHom f e.symm.surjective
    intro d v
    simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using (h (e.symm d) v).symm
  have hn : (linearNormalizer ρ).map c.toMonoidHom = linearNormalizer τ := by
    change (Subgroup.normalizer (actionImage ρ : Set _)).map c.toMonoidHom =
      Subgroup.normalizer (actionImage τ : Set _)
    rw [Subgroup.map_equiv_normalizer_eq, him]
  let j := (c.subgroupMap (linearNormalizer ρ)).trans (MulEquiv.subgroupCongr hn)
  refine ⟨j, ?_⟩
  intro t v
  change f (t.val.val v) = f (t.val.val (f.symm (f v)))
  rw [f.symm_apply_apply]

private theorem strict_transport
    (hq : Quasiequivalent ρ τ)
    (ht : ∀ A : Subgroup (linearNormalizer τ), IsElementaryTwo A →
      2 * rank A < fixedCodim (normalizerRepresentation τ) A) :
    ∀ A : Subgroup (linearNormalizer ρ), IsElementaryTwo A →
      2 * rank A < fixedCodim (normalizerRepresentation ρ) A := by
  obtain ⟨e, f, hf⟩ := hq
  obtain ⟨j, hj⟩ := normalizer_equivalence ρ τ e f hf
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo (A.map j.toMonoidHom) := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hb
    apply hA.1
    exact (Subgroup.map_injective j.injective) (by simpa only [Subgroup.map_bot] using hb)
  have hh := ht _ hB
  rw [rank_map_injective j.toMonoidHom j.injective,
    ← fixedCodim_map_equivariant (normalizerRepresentation ρ) (normalizerRepresentation τ)
      j.toMonoidHom f hj] at hh
  exact hh
end Transport

attribute [local instance] ZMod.algebra
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The two concrete local calculations exclude every elementary actor in the
literal binary linear normalizer. The calculation contracts remain premises. -/
theorem normalizer_obstruction_of_calculations {r : ℕ} (hr : 2 ≤ r)
    (hinner : InnerCalculations F r) (hnormalizer : NormalizerCalculations F r)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer (adjointBinary F))) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation (adjointBinary F)) A := by
  let : Finite (Atlas.G2.Restricted.Adjoint.Space F) :=
    Finite.of_injective (Atlas.G2.Restricted.Adjoint.Coordinates.equiv F)
      (Atlas.G2.Restricted.Adjoint.Coordinates.equiv F).injective
  let : Module.Finite (ZMod 2) (Atlas.G2.Restricted.Adjoint.Space F) := Module.Finite.of_finite
  exact normalizer_strict_of_calculations (adjointBinary F) (by omega)
    hnormalizer.faithful hnormalizer.irreducible hAut
    hinner.involution_codim hinner.fixed_kernel_card hnormalizer.involution_alternative A hA

/-- Transport through the actual group and vector-space equivalences supplies
exactly the `hadjoint` premise of `degree_lt_of_cubic_estimates`. The cubic
hypothesis is retained at that boundary; the local calculations give the
stronger exclusion of all elementary actors. -/
theorem quasiequivalent_cubic_obstruction_of_calculations
    (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) {r : ℕ} (hr : 2 ≤ r)
    (hinner : InnerCalculations F r) (hnormalizer : NormalizerCalculations F r)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hq : Quasiequivalent σ (adjointBinary F))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (_hc : IsCubic (normalizerRepresentation σ) A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  exact strict_transport σ (adjointBinary F) hq
    (normalizer_obstruction_of_calculations hr hinner hnormalizer hAut) A hA

/-- No nontrivial elementary two-subgroup of the actual adjoint's full binary
linear normalizer has fixed codimension at most twice its rank. The concrete
inner and outer calculations are discharged; the automorphism rank bound is
the independent Chapter 16 input. This also excludes actors acting cubically. -/
theorem normalizer_obstruction {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer (adjointBinary F))) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim (normalizerRepresentation (adjointBinary F)) A :=
  normalizer_obstruction_of_calculations hr (innerCalculations F hF)
    (normalizerCalculations F hr hF) hAut A hA

/-- Genuine quasiequivalence transports the common-fixed-space obstruction to
the original module and its literal linear normalizer. This discharges the
`hadjoint` premise of `degree_lt_of_cubic_estimates`, including the original
cubicity convention, with only the independent automorphism rank input. -/
theorem quasiequivalent_cubic_obstruction
    (σ : Representation (ZMod 2) (Atlas.G2.Model F) V)
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hq : Quasiequivalent σ (adjointBinary F))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (_hc : IsCubic (normalizerRepresentation σ) A) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A :=
  strict_transport σ (adjointBinary F) hq (normalizer_obstruction hr hF hAut) A hA
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
