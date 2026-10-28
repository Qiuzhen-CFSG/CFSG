module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.OrbitConsequences
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Displacement
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Core

/-!
# Singular fixed subgroups and dual-core control for 15.3.46(4)

A whole conjugate `A = V^g` in `T` already normalizes `V`, so its offender
normalizer is `A` itself. The actual inequality `r(G,V)>1` therefore puts its
dual core at one in `N_V(A)`. If `V` does not normalize `A`, that core is
proper and the actual induced automizer has rank at least two.

The fixed subgroup `C_A(V)` is singular after inverse conjugation to the
original quadratic space. In the nonnormalizing case its centralizer escapes
`N_G(A)`. In the normalizing case, both commutators lie in singular
intersections; the displacement theorem excludes a fixed nonsingular vector.
Thus the fixed subgroup of a noncentralizing conjugate has order at most four.
All conjugations here use the actual ambient automorphisms, and normalizers
are relative only when explicitly intersected with `V`.

The final lemma reduces the nonnormalizing contradiction to the orders of the
actual dual core and its fixed subgroups, and the pointwise centralizer bound
for a singular plane. Those finite module calculations remain explicit inputs.
Neither positivity of `globalW` nor Hypothesis E.3.24 is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.46(4),
printed p.1141; E.3.30–32, pp.237–238; Definition F.4.41, p.294.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
variable {G : Type*} [Group G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]

private theorem map_conj_inv_conj (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = U := by
  rw [map_map]
  have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by ext x; simp [MulAut.conj_apply, mul_assoc]
  rw [hc, map_id]

private theorem map_conj_conj_inv (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = U := by
  simpa only [inv_inv] using map_conj_inv_conj U g⁻¹

private theorem centralizer_map_equiv (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom =
      centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

omit [IsElementaryAbelian 2 V] in
/-- A whole conjugate inside `T` is its own offender normalizer. -/
theorem offenderNormalizer_eq (h : EarlierFusionInputs T M V P) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T) :
    ChapterE.offenderNormalizer V g = V.map (MulAut.conj g).toMonoidHom :=
  inf_eq_left.mpr (hgT.trans (h.sylow_le.trans h.normalizer_eq.le))

variable [Finite G]

/-- The actual dual core at one normalizes the conjugate, by `r(G,V)>1`. -/
theorem dualCore_one_le_normalizer
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T) :
    ChapterE.automizerDualCore V
      (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1 ≤
        V ⊓ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hr := one_lt_globalR d.form d.nondegenerate d.dimension h.normalizer_eq
    (nonsingular_centralizer_le_of_orthogonal_calculations c h)
  have he := offenderNormalizer_eq h g hgT
  have hb := ChapterE.automizerDualCore_le_conjugate_normalizer (V := V) g 1
  rw [he] at hb
  apply hb
  simpa [ChapterE.subgroupCorank] using hr

/-- In the nonnormalizing case this is a proper subgroup of `V`. -/
theorem dualCore_one_lt
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    ChapterE.automizerDualCore V
      (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1 < V := by
  have hc := dualCore_one_le_normalizer d h c g hgT
  apply lt_of_le_of_ne (hc.trans inf_le_left)
  intro he
  have hb := hc.trans inf_le_right
  rw [he] at hb
  exact hn hb

/-- The nonnormalizing case forces rank at least two for the actual image. -/
theorem one_lt_automizer_rank
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    1 < Representation.BinaryOffender.rank
      (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) := by
  have hr := one_lt_globalR d.form d.nondegenerate d.dimension h.normalizer_eq
    (nonsingular_centralizer_le_of_orthogonal_calculations c h)
  have hb := ChapterE.globalR_le_conjugate_centralizer_corank g hn
  have he := ChapterE.offender_centralizer_corank V g
  rw [offenderNormalizer_eq h g hgT] at he
  have hz : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom) = 0 := by simp [ChapterE.subgroupCorank]
  rw [hz, zero_add] at he
  rw [he] at hb
  exact_mod_cast lt_of_lt_of_le hr hb

/-- Pulling back the fixed subgroup gives its singularity in the original form.
This expresses singularity in the conjugate space without choosing a second form. -/
theorem fixed_pullback_totallySingular_of_not_normalizes
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    IsTotallySingular d.form
      ((V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := A ⊓ centralizer (V : Set G)
  have hBV : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ V := by
    have hb := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (show B ≤ A from inf_le_left)
    exact hb.trans_eq (map_conj_conj_inv V g)
  apply totallySingular_of_normalizer_escape d.form h.normalizer_eq
    (controlsFusion_of_orthogonal_calculations c h)
    (nonsingular_centralizer_le_of_orthogonal_calculations c h) hBV
  intro hN
  have hVB : V ≤ centralizer (B : Set G) := le_centralizer_iff.mpr inf_le_right
  have hVM : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ M :=
    (map_mono hVB).trans ((map_centralizer_le_centralizer_image _ _).trans
      ((Subgroup.centralizer_le_normalizer _).trans hN))
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hVM
  rw [map_conj_inv_conj, h.normalizer_eq, map_equiv_normalizer_eq] at hm
  exact hn hm

/-- The fixed subgroup in the nonnormalizing case has order at most four. -/
theorem card_fixed_le_four_of_not_normalizes
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) ≤ 4 := by
  have hs := fixed_pullback_totallySingular_of_not_normalizes d h c g hn
  have hc := card_le_four_of_totallySingular d.form d.nondegenerate d.dimension hs.1 hs
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hc

/-- Mutual normalization places the commutator in the singular intersection. -/
theorem commutator_totallySingular_of_normalizes
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgM : g ∉ M) (hAM : V.map (MulAut.conj g).toMonoidHom ≤ M)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    IsTotallySingular d.form ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ := by
  have hi := totallySingular_intersection_of_fusion d.form h.normalizer_eq
    (controlsFusion_of_orthogonal_calculations c h)
    (nonsingular_centralizer_le_of_orthogonal_calculations c h) g hgM
  have hle : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom := le_inf
    (le_normalizer_iff_commutator_le_left.mp
      (hAM.trans h.normalizer_eq.le))
    (le_normalizer_iff_commutator_le_right.mp hn)
  exact ⟨hle.trans inf_le_left, fun v hv => hi.2 v (hle hv)⟩

/-- An actor subgroup with singular displacement cannot both act nontrivially
and fix a nonsingular vector. -/
theorem fixed_totallySingular_of_singular_commutator
    (d : NaturalOrthogonalAction M V) {A : Subgroup G} (hAM : A ≤ M)
    (hs : IsTotallySingular d.form ⁅V, A⁆) (hne : ¬ A ≤ centralizer (V : Set G)) :
    IsTotallySingular d.form (V ⊓ centralizer (A : Set G)) := by
  refine ⟨inf_le_left, ?_⟩
  intro v hv
  by_contra hq
  apply hne
  intro a ha
  have hsmall : IsTotallySingular d.form ⁅V, zpowers a⁆ :=
    ⟨(commutator_mono le_rfl (zpowers_le.mpr ha)).trans hs.1,
      fun u hu => hs.2 u ((commutator_mono le_rfl (zpowers_le.mpr ha)) hu)⟩
  have hbot : ⁅V, zpowers a⁆ = ⊥ := by
    by_contra hb
    apply d.not_totallySingular_commutator_of_fixed_nonsingular ⟨a, hAM ha⟩ v hq ?_ hb hsmall
    change a * (v : G) * a⁻¹ = v
    rw [hv.2 a ha, mul_assoc, mul_inv_cancel, mul_one]
  exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot)) (mem_zpowers a)

/-- In the mutually normalizing case, singularity of the fixed subgroup is
proved by applying the displacement argument after inverse conjugation. -/
theorem fixed_pullback_totallySingular_of_normalizes
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hne : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    IsTotallySingular d.form
      ((V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom) := by
  have hAN := hgT.trans (h.sylow_le.trans h.normalizer_eq.le)
  have hAM : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn
    rwa [map_equiv_normalizer_eq, map_conj_conj_inv, ← h.normalizer_eq] at hm
  have hVN : V ≤ normalizer (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G) := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAN
    rwa [map_conj_conj_inv, map_equiv_normalizer_eq] at hm
  have hgM : g⁻¹ ∉ M := by
    intro hg
    have hg' : g ∈ M := by simpa only [inv_inv] using M.inv_mem hg
    apply hne
    have he : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (h.normalizer_eq.le hg')
    rw [he]
    exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hne' : ¬ V.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (V : Set G) := by
    intro hc
    have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hc
    rw [map_conj_inv_conj, centralizer_map_equiv] at hm
    exact hne (le_centralizer_iff.mp hm)
  have hs := commutator_totallySingular_of_normalizes d h c g⁻¹ hgM hAM hVN
  have hf := fixed_totallySingular_of_singular_commutator d hAM hs hne'
  rwa [map_inf _ _ _ (MulAut.conj g⁻¹).injective, map_conj_conj_inv,
    centralizer_map_equiv]

/-- In either case, a noncentralizing whole conjugate has a singular fixed
subgroup when transported back along its defining conjugation. -/
theorem fixed_pullback_totallySingular
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    IsTotallySingular d.form
      ((V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)).map
        (MulAut.conj g⁻¹).toMonoidHom) := by
  by_cases hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)
  · exact fixed_pullback_totallySingular_of_normalizes d h c g hgT hn hne
  · exact fixed_pullback_totallySingular_of_not_normalizes d h c g hn

/-- The fixed subgroup of a noncentralizing whole conjugate has order at most four. -/
theorem card_fixed_le_four
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) ≤ 4 := by
  have hs := fixed_pullback_totallySingular d h c g hgT hne
  have hc := card_le_four_of_totallySingular d.form d.nondegenerate d.dimension hs.1 hs
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hc

/-- The remaining case reduces to the actual core orders and the pointwise
centralizer bound for a singular plane. Both are explicit calculation inputs;
this theorem does not assert them. -/
theorem false_of_not_normalizes_of_core_bounds
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcore : Nat.card (ChapterE.automizerDualCore V
      (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1) = 8)
    (hfixed : Nat.card (ChapterE.automizerDualCore V
      (ChapterE.inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1 ⊓
        centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) = 2)
    (hB : Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) :
      Subgroup G) = 4)
    (hfixer : ∀ B X : Subgroup G, IsTotallySingular d.form B → Nat.card B = 4 →
      X ≤ M → X ≤ centralizer (B : Set G) →
      Nat.card X ≤ 2 * Nat.card (X ⊓ centralizer (V : Set G) : Subgroup G)) : False := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let B := A ⊓ centralizer (V : Set G)
  let U := ChapterE.automizerDualCore V (ChapterE.inducedAutomizer V A) 1
  let B' := B.map (MulAut.conj g⁻¹).toMonoidHom
  let U' := U.map (MulAut.conj g⁻¹).toMonoidHom
  have hUN : U ≤ V ⊓ normalizer (A : Set G) := dualCore_one_le_normalizer d h c g hgT
  have hUM : U' ≤ M := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hUN.trans inf_le_right)
    rwa [map_equiv_normalizer_eq, map_conj_conj_inv, ← h.normalizer_eq] at hm
  have hUB : U ≤ centralizer (B : Set G) :=
    (hUN.trans inf_le_left).trans (le_centralizer_iff.mpr inf_le_right)
  have hU'B' : U' ≤ centralizer (B' : Set G) :=
    (map_mono hUB).trans (map_centralizer_le_centralizer_image _ _)
  have hBsing : IsTotallySingular d.form B' :=
    fixed_pullback_totallySingular_of_not_normalizes d h c g hn
  have hBcard : Nat.card B' = 4 := by
    rw [show B' = B.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hB
  have hUcard : Nat.card U' = 8 := by
    rw [show U' = U.map (MulAut.conj g⁻¹).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hcore
  have hCcard : Nat.card (U' ⊓ centralizer (V : Set G) : Subgroup G) = 2 := by
    have he : (U ⊓ centralizer (A : Set G)).map (MulAut.conj g⁻¹).toMonoidHom =
        U' ⊓ centralizer (V : Set G) := by
      rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, centralizer_map_equiv]
      change U' ⊓ centralizer ((V.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj g⁻¹).toMonoidHom : Set G) = _
      rw [map_conj_conj_inv]
    rw [← he, card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hfixed
  have hb := hfixer B' U' hBsing hBcard hUM hU'B'
  rw [hUcard, hCcard] at hb
  omega

end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
