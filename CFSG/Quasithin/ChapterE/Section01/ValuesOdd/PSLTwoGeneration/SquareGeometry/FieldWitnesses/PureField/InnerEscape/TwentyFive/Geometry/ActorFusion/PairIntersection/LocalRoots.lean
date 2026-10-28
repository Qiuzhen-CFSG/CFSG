module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.PairIntersection.LocalRoots.Permutations
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.PairIntersection.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion.LocalCalculation.Coordinates

/-!
# Linear square roots in the characteristic-five centralizers

Both marked field involutions centralize the common Sylow two-subgroup.
Sylow maximality puts them in that Sylow. After transport through the actual
pure-field centralizer and five-point comparisons, its centralizer in S₅
is even, so both involutions belong to each literal large subgroup.

The intrinsic linear marking puts a linear large element in the local
commutator and in its Sylow four-group. Its product coordinates therefore
have trivial second component and an even first component whose fourth
power is one. The explicit five-point square root lifts to the actual
centralizer. Multiplication by its marked central field involution corrects
the ambient field coordinate without changing the square. Nontriviality
of that square makes the resulting linear root have order four.

The final theorem discharges exactly `PairIntersection.LocalSquareRoots`.
It supports Aschbacher--Smith E.1.5, E.1.8 and E.1.14(6), printed
pp.210--214, with the last citing Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

omit [Finite F] in
include hσ in
private theorem involution_mem_sylow (j : Bool) : c.involution j ∈ (c.T : Subgroup _) := by
  have hp : IsPGroup 2 (zpowers (c.involution j)) := IsPGroup.of_card (by
    simpa only [Nat.card_zpowers, pow_one] using c.involution_order hσ j :
      Nat.card (zpowers (c.involution j)) = 2 ^ 1)
  have hc : c.involution j ∈ centralizer (c.T : Set (innerModel F σ)) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    exact (mem_centralizer_singleton_iff.mp (c.sylow_le j hy))
  have hm : c.involution j ∈ zpowers (c.involution j) ⊓ normalizer (c.T : Set _) :=
    ⟨mem_zpowers _, Subgroup.centralizer_le_normalizer _ hc⟩
  rw [hp.inf_normalizer_sylow c.T] at hm
  exact hm.2

include hF hσ in
private theorem local_fixed_card : Nat.card (FixedPoints.subfield (zpowers σ) F) = 5 :=
  fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2

variable [Finite (innerModel F σ)]

private theorem involution_mem_large (i j : Bool) : c.involution j ∈ c.large hF hσ i := by
  let K := FixedPoints.subfield (zpowers σ) F
  let ε : PGL2 K ≃* Equiv.Perm (Fin 5) :=
    (Theory.PSL2.exists_pgl2_five_equiv K (local_fixed_card hF hσ)).some
  let e := (c.productCoordinates hF hσ i).trans
    (MulEquiv.prodCongr ε (MulEquiv.refl (zpowers σ)))
  let f := (MonoidHom.fst (Equiv.Perm (Fin 5)) (zpowers σ)).comp e.toMonoidHom
  have hf : Function.Surjective f := fun x => ⟨e.symm (x, 1), by simp [f]⟩
  let P := (c.T.subtype (c.sylow_le i)).mapSurjective hf
  have ht := involution_mem_sylow c hσ j
  let v : c.centralizerAt i := ⟨c.involution j, c.sylow_le i ht⟩
  have heven : f v ∈ alternatingGroup (Fin 5) := by
    apply LocalRoots.even_of_centralizes_sylow P (f v)
    rintro y ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (c.sylow_le j ht)
  refine ⟨ht, v, ?_, rfl⟩
  change c.projection hF hσ i v ∈
    (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
  rw [← Theory.PSL2.pgl2_five_equiv_maps_psl K (local_fixed_card hF hσ) ε] at heven
  have he : f v = ε (c.projection hF hσ i v) := rfl
  rw [he, mem_map_equiv, MulEquiv.symm_apply_apply] at heven
  exact heven

private theorem linear_local_root (i : Bool) (x : innerModel F σ)
    (hx : x ∈ c.large hF hσ i) (hxl : (x : PGammaL2 F).right = 1) (hxn : x ≠ 1) :
    ∃ r : innerModel F σ, r ∈ c.centralizerAt i ∧
      (r : PGammaL2 F).right = 1 ∧ r ^ 2 = x ∧ orderOf r = 4 := by
  let K := FixedPoints.subfield (zpowers σ) F
  let ε : PGL2 K ≃* Equiv.Perm (Fin 5) :=
    (Theory.PSL2.exists_pgl2_five_equiv K (local_fixed_card hF hσ)).some
  let e := (c.productCoordinates hF hσ i).trans
    (MulEquiv.prodCongr ε (MulEquiv.refl (zpowers σ)))
  let u : c.centralizerAt i := ⟨x, c.sylow_le i hx.1⟩
  have hul : x ∈ pGammaL2LinearKernel F (innerModel F σ) :=
    (mem_pGammaL2LinearKernel_iff _ _ _).mpr hxl
  have hup : c.projection hF hσ i u ∈
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range := by
    obtain ⟨v, hv, hvx⟩ := hx.2
    have hvu : v = u := Subtype.ext hvx
    exact hvu ▸ hv
  have hud := (c.local_linear_iff_derived hF hσ i u hup).mp hul
  have hus : (e u).2 = 1 := by
    let f := (MonoidHom.snd (Equiv.Perm (Fin 5)) (zpowers σ)).comp e.toMonoidHom
    have hm : (commutator (c.centralizerAt i)).map f ≤ commutator (zpowers σ) := by
      rw [map_commutator_eq, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    have hs := hm (mem_map_of_mem f hud)
    rwa [commutator_eq_bot, mem_bot] at hs
  have hue : (e u).1 ∈ alternatingGroup (Fin 5) := by
    rw [← Theory.PSL2.pgl2_five_equiv_maps_psl K (local_fixed_card hF hσ) ε]
    exact mem_map_of_mem ε.toMonoidHom hup
  have hsmall : x ∈ c.small hF hσ i := by
    rw [← c.local_linear_marking hF hσ i]
    exact ⟨hx, hul⟩
  have hx4 : x ^ 4 = 1 := by
    have h := pow_card_eq_one' (x := (⟨x, hsmall⟩ : c.small hF hσ i))
    rw [c.local_small_card hF hσ i] at h
    exact congrArg Subtype.val h
  have hu4 : u ^ 4 = 1 := Subtype.ext hx4
  have hp4 : (e u).1 ^ 4 = 1 := by
    simpa only [map_pow, Prod.pow_fst, map_one, Prod.fst_one] using
      congrArg (fun z => (e z).1) hu4
  obtain ⟨hp2, a, ha⟩ := LocalRoots.even_fourth_roots (e u).1 hp4
    (Equiv.Perm.mem_alternatingGroup.mp hue)
  have hu2 : u ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact Prod.ext hp2 (by simp [Prod.pow_snd, hus])
  have hx2 : x ^ 2 = 1 := congrArg Subtype.val hu2
  let y := e.symm (a, 1)
  have hy2 : y ^ 2 = u := by
    apply e.injective
    rw [map_pow]
    change (e (e.symm (a, 1))) ^ 2 = e u
    rw [e.apply_symm_apply]
    exact Prod.ext ha (by simpa using hus.symm)
  let v : c.centralizerAt i := ⟨c.involution i, by
    exact mem_centralizer_singleton_iff.mpr rfl⟩
  have hv2 : v ^ 2 = 1 := Subtype.ext
    ((orderOf_eq_prime_iff.mp (c.involution_order hσ i)).1)
  have hyv : Commute y v := by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp y.property
  have hvf : ((v : innerModel F σ) : PGammaL2 F).right = σ := by
    cases i
    · rfl
    · change (c.z : PGammaL2 F).right * σ = σ
      rw [c.z_linear, one_mul]
  have finish (r : c.centralizerAt i)
      (hr : ((r : innerModel F σ) : PGammaL2 F).right = 1) (hr2 : r ^ 2 = u) :
      ∃ r : innerModel F σ, r ∈ c.centralizerAt i ∧
        (r : PGammaL2 F).right = 1 ∧ r ^ 2 = x ∧ orderOf r = 4 := by
    have hs : (r : innerModel F σ) ^ 2 = x := congrArg Subtype.val hr2
    refine ⟨r, r.property, hr, hs, ?_⟩
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · simpa only [pow_one, hs] using hxn
    · simpa only [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by decide, pow_mul, hs] using hx2
  rcases fieldAut_eq_one_or (by decide : Nat.Prime 5) hF σ
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
    (((y : innerModel F σ) : PGammaL2 F).right) with h | h
  · exact finish y h hy2
  · refine finish (y * v) ?_ ?_
    · change ((y : innerModel F σ) : PGammaL2 F).right *
        ((v : innerModel F σ) : PGammaL2 F).right = 1
      rw [h, hvf, ← pow_two]
      exact (orderOf_eq_prime_iff.mp hσ).1
    · rw [hyv.mul_pow, hv2, mul_one, hy2]

/-- Linear square roots in both actual marked centralizers. -/
theorem localSquareRoots : PairIntersection.LocalSquareRoots c hF hσ where
  twist_mem i := involution_mem_large c hF hσ i true
  roots := linear_local_root c hF hσ

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frame
