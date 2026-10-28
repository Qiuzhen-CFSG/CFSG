module
public import Theory.Representation.HermitianTensorThree.Involutions
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals.LargeActors
/-!
# The (F-1)-offenders on the descended Hermitian tensor

An outer elementary actor has rank at most 2n+1. If it has rank greater
than one, its fixed codimension is at least 5n; the involution bound
handles rank one. Neither can be an (F-1)-offender. An inner actor has
fixed codimension at least 4n, so an (F-1)-offender has rank at least 3n.
The large-actor bound and the two-rank bound then force n = 1, actor
rank four, and fixed codimension five. The existing root-plane theorem
identifies its actual conjugacy class. Conversely that plane class at
n = 1 attains the inequality.

These are the alpha-column calculations following H.4.5, including the
exceptional field-four value. They hold in the full binary normalizer;
no odd-torus exclusion is asserted. The original-action application is
NonFFSourceNonMathieuHermitianNearOffenders in Chapter 12. The odd-element
bound, the resulting global r bound, and the source exclusion remain with
qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.4.4 and
the alpha calculation following H.4.5, printed pp.381–382
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace Representation.HermitianTensorThree.NearOffenders
variable (n : ℕ) [NeZero n]

private theorem elementary_rank_le (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    [IsElementaryAbelian 2 A] {k : ℕ} (h : primeRank 2 A ≤ k) : rank A ≤ k := by
  have ht : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective _ (⊤ : Subgroup A).subtype_injective
  have hc := (primeRank_le_iff_elementary_card_le A).mp h ⊤ ht
  have hl := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.card_congr topEquiv.toEquiv, Nat.log_pow Nat.one_lt_two, rank] using hl

private theorem outer_rank_le (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    [IsElementaryAbelian 2 A] (hAN : A ≤ binaryNormalizer n)
    (hAL : ¬ A ≤ binaryImage n) : rank A ≤ 2*n+1 := by
  obtain ⟨i, hiA, hiL⟩ := SetLike.not_le_iff_exists.mp hAL
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := A) i hiA)
    (fun h => hiL (h ▸ (binaryImage n).one_mem))
  obtain ⟨c, hc, hci⟩ := OuterRank.outer_involution_conjugate n (normalizerCoverage n)
    i (hAN hiA) hi2 hiL
  exact elementary_rank_le n A (OuterRank.elementary_outer_twoRank_le n
    ⟨FieldSections.centralizerEquiv n⟩ A
    (OuterRank.Coefficients.elementary_relIndex_le_two n (normalizerCoverage n)
      A inferInstance hAN) i hiA c hc hci)

/-- The complete (F-1)-offender alternative in the binary normalizer. -/
theorem classification (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hA : IsElementaryTwo A) (hAN : A ≤ binaryNormalizer n)
    (hnear : fixedCodim (UnipotentRadicals.ambientAction n) A ≤ rank A + 1) :
    n = 1 ∧ A ≤ binaryImage n ∧ rank A = 4 ∧
      fixedCodim (UnipotentRadicals.ambientAction n) A = 5 ∧
      ∃ c : Cover n, A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom =
        UnipotentRadicals.plane n := by
  let : IsElementaryAbelian 2 A := hA.2
  have hn := NeZero.pos n
  obtain ⟨i,hiA,hi⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := A) i hiA) hi
  have hlo : fixedCodim (UnipotentRadicals.ambientAction n) (zpowers i) ≤
      fixedCodim (UnipotentRadicals.ambientAction n) A := by
    have hle : fixedSpace (UnipotentRadicals.ambientAction n) A ≤
        fixedSpace (UnipotentRadicals.ambientAction n) (zpowers i) := by
      intro v hv a
      exact hv ⟨a, (zpowers_le.mpr hiA) a.property⟩
    have hd := Submodule.finrank_mono hle
    have h1 := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) (zpowers i)
    have h2 := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) A
    omega
  have hmin : 3*n ≤ fixedCodim (UnipotentRadicals.ambientAction n) A := by
    by_cases hL : i ∈ binaryImage n
    · rw [Involutions.inner_fixedCodim n i hL hi2] at hlo
      omega
    · rw [Involutions.outer_fixedCodim n i (hAN hiA) hL hi2] at hlo
      exact hlo
  have hAL : A ≤ binaryImage n := by
    by_contra hAL
    have hr := outer_rank_le n A hAN hAL
    have hgt : 1 < rank A := by omega
    have hfix := LargeActors.outer_fixed_rank_le n A hAN hAL hgt
    have hsum := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) A
    rw [finrank_binary] at hsum
    omega
  rw [Involutions.inner_fixedCodim n i (hAL hiA) hi2] at hlo
  have hrank := elementary_rank_le n A ((primeRank_le_of_injective 2
    (inclusion hAL) (inclusion_injective hAL)).trans (OuterRank.binaryImage_twoRank n).le)
  have hlarge : 3*n ≤ rank A := by omega
  have hfix := LargeActors.large_elementary_fixed_rank_le n A hAN hlarge
  have hsum := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) A
  rw [finrank_binary] at hsum
  have hn1 : n = 1 := by omega
  have hr4 : rank A = 4 := by omega
  have hc5 : fixedCodim (UnipotentRadicals.ambientAction n) A = 5 := by omega
  refine ⟨hn1,hAL,hr4,hc5,?_⟩
  exact UnipotentRadicals.maximal_elementary_plane_of_fixedRank n A hAL (by omega) (by omega)

private theorem plane_rank : rank (UnipotentRadicals.plane n) = 4*n := by
  rw [UnipotentRadicals.plane, rank_map_injective (UnipotentRadicals.unipotentHom n)
    (UnipotentRadicals.unipotentHom_injective n)]
  change Nat.log 2 (Nat.card (Matrix.PSL3Even.UnipotentGeometry.V₂ (E n))) = _
  rw [Matrix.PSL3Even.UnipotentGeometry.card_V₂,card_E,← pow_mul,
    Nat.log_pow Nat.one_lt_two]
  omega

/-- The exceptional possibility is exactly the plane-root-group conjugacy class. -/
theorem classification_iff (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hA : IsElementaryTwo A) (hAN : A ≤ binaryNormalizer n) :
    fixedCodim (UnipotentRadicals.ambientAction n) A ≤ rank A + 1 ↔
      n = 1 ∧ ∃ c : Cover n,
        A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  constructor
  · intro h
    obtain ⟨hn,_,_,_,hc⟩ := classification n A hA hAN h
    exact ⟨hn,hc⟩
  · rintro ⟨hn,c,hc⟩
    have hr : rank A = 4*n := by
      rw [← rank_map_conj A (binaryActionHom n c),hc,plane_rank]
    have hf := (fixedSpaceConjEquiv (UnipotentRadicals.ambientAction n) A
      (binaryActionHom n c)).finrank_eq
    rw [hc,UnipotentRadicals.finrank_plane_fixed] at hf
    have hs := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) A
    rw [finrank_binary] at hs
    omega

/-- Transport retains the original actor and its rank, not just its isomorphism type. -/
theorem of_equivariant {X W : Type*} [Group X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W)
    (j : X →* binaryNormalizer n) (hj : Function.Injective j)
    (e : W ≃ₗ[ZMod 2] Space n)
    (he : ∀ a v, e (ρ a v) = overgroupAction n (binaryNormalizer n) (j a) (e v))
    (A : Subgroup X) (hA : IsElementaryTwo A)
    (hnear : fixedCodim ρ A ≤ rank A + 1) :
    n = 1 ∧ rank A = 4 ∧ fixedCodim ρ A = 5 ∧
      A.map ((binaryNormalizer n).subtype.comp j) ≤ binaryImage n ∧
      ∃ c : Cover n,
        (A.map ((binaryNormalizer n).subtype.comp j)).map
          (MulAut.conj (binaryActionHom n c)).toMonoidHom = UnipotentRadicals.plane n := by
  let f := (binaryNormalizer n).subtype.comp j
  have hf : Function.Injective f := Subtype.val_injective.comp hj
  let B := A.map f
  let : IsElementaryAbelian 2 A := hA.2
  have hB : IsElementaryTwo B :=
    ⟨fun h => hA.1 ((map_eq_bot_iff_of_injective A hf).mp h),IsElementaryAbelian.map f⟩
  have hBN : B ≤ binaryNormalizer n := by
    rintro _ ⟨a,_,rfl⟩
    exact (j a).property
  have hcod := fixedCodim_map_equivariant ρ (UnipotentRadicals.ambientAction n)
    f e he A
  have hrank := rank_map_injective f hf A
  change fixedCodim ρ A = fixedCodim (UnipotentRadicals.ambientAction n) B at hcod
  change rank B = rank A at hrank
  obtain ⟨hn,hBL,hr,hc,hconj⟩ := classification n B hB hBN (by omega)
  exact ⟨hn,hrank.symm.trans hr,hcod.trans hc,hBL,hconj⟩

/-- Every nontrivial elementary actor has strictly larger codimension than rank. -/
theorem not_isFFModule (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hM : M ≤ binaryNormalizer n) : ¬ IsFFModule (overgroupAction n M) := by
  rintro ⟨A,hA,hoff⟩
  let j := inclusion hM
  obtain ⟨_,hr,hc,_,_⟩ := of_equivariant n (overgroupAction n M)
    j (inclusion_injective hM) (LinearEquiv.refl _ _) (fun _ _ => rfl) A hA
    (hoff.trans (Nat.le_add_right _ _))
  omega

/-- Over every larger field there are no (F-1)-offenders at all. -/
theorem rank_add_one_lt_fixedCodim {X W : Type*} [Group X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W)
    (j : X →* binaryNormalizer n) (hj : Function.Injective j)
    (e : W ≃ₗ[ZMod 2] Space n)
    (he : ∀ a v, e (ρ a v) = overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hn : 1 < n) (A : Subgroup X) (hA : IsElementaryTwo A) :
    rank A + 1 < fixedCodim ρ A := by
  by_contra h
  have hn1 := (of_equivariant n ρ j hj e he A hA (Nat.le_of_not_gt h)).1
  omega
/-- Every embedded action containing the marked component has an
(F-1)-offender exactly at half-degree one; the witness is an actual preimage
of the concrete plane radical. -/
theorem exists_iff_of_equivariant {X W : Type*} [Group X]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W)
    (j : X →* binaryNormalizer n) (hj : Function.Injective j)
    (e : W ≃ₗ[ZMod 2] Space n)
    (he : ∀ a v, e (ρ a v) = overgroupAction n (binaryNormalizer n) (j a) (e v))
    (hcover : binaryImage n ≤ ((binaryNormalizer n).subtype.comp j).range) :
    (∃ A : Subgroup X, IsElementaryTwo A ∧ fixedCodim ρ A ≤ rank A + 1) ↔ n = 1 := by
  constructor
  · rintro ⟨A,hA,ha⟩
    exact (of_equivariant n ρ j hj e he A hA ha).1
  · intro hn
    let f := (binaryNormalizer n).subtype.comp j
    have hf : Function.Injective f := Subtype.val_injective.comp hj
    have hPL : UnipotentRadicals.plane n ≤ binaryImage n := by
      rintro _ ⟨a,_,rfl⟩
      exact ⟨Matrix.PSL3Even.UnipotentGeometry.specialLinear (E n) a,rfl⟩
    let : IsElementaryAbelian 2 (UnipotentRadicals.plane n) :=
      IsElementaryAbelian.map (UnipotentRadicals.unipotentHom n)
    let A := (UnipotentRadicals.plane n).comap f
    have hi : Function.Injective (f.subgroupComap (UnipotentRadicals.plane n)) :=
      fun a b h => Subtype.ext (hf (congrArg
        (fun x : UnipotentRadicals.plane n => x.val) h))
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective _ hi
    have hm : A.map f = UnipotentRadicals.plane n := map_comap_eq_self (hPL.trans hcover)
    have hr : rank A = 4*n := by
      rw [← rank_map_injective f hf,hm,plane_rank]
    have hc := fixedCodim_map_equivariant ρ (UnipotentRadicals.ambientAction n) f e he A
    rw [hm] at hc
    have hs := fixedCodim_add_finrank (UnipotentRadicals.ambientAction n) (UnipotentRadicals.plane n)
    rw [UnipotentRadicals.finrank_plane_fixed,finrank_binary] at hs
    refine ⟨A,⟨?_,inferInstance⟩,by omega⟩
    intro hz
    rw [hz,BinaryOffender.rank_bot] at hr
    omega


end Representation.HermitianTensorThree.NearOffenders
