module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.Collection

/-!
# Long-root exchanges for normalized triality sections

The arms torus fixes the highest long root and moves each other long root by
the cubic norm. Scalar-equivariant uniqueness therefore eliminates the two
commuting-pair defects. Combining the square of an arms actor with a central
actor of parameter equal to its norm fixes long root 0 and scales long roots
1 and 2 by the same nonidentity scalar. The candidate A₂ conjugation word is
additive, and the same uniqueness argument proves the exchange in the cover.

This uses a cubic-field unit with nonidentity norm, which exists already for
q = 4. It does not require a fixed-field unit with nonidentity cube.
Sources: GLS3 2.4.5(b)(1), 2.4.7(f), and §6.1; Aschbacher–Smith I.1.3.
-/

@[expose] public section
namespace Triality.Standard.CentralCovers.TwoPrimary
open Parabolics ConcreteBruhat RadicalCoordinates.LeviCommutators
open Theory.AlgebraicGroup.StandardRootSystem PositiveCoordinates
open Parabolics.RankOneMatrices PositiveCoordinates.SumExchangeData
noncomputable section
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn

namespace RootSections

/-- Compare an actual conjugation with an additive candidate word. This
removes the central defect, using one scalar that fixes the conjugating element. -/
theorem conjugation_eq_of_scalar {F : Type*} [Field F]
    (hk : f.ker ≤ Subgroup.center E) (u v : Multiplicative F →* E)
    (x z : E) (c : F) (hc : c ≠ 1)
    (hfix : z * x * z⁻¹ = x)
    (hproj : ∀ a, f (x * u (.ofAdd a) * x⁻¹) = f (v (.ofAdd a)))
    (hu : ∀ a, z * u (.ofAdd a) * z⁻¹ = u (.ofAdd (c*a)))
    (hv : ∀ a, z * v (.ofAdd a) * z⁻¹ = v (.ofAdd (c*a))) :
    ∀ a, x * u (.ofAdd a) * x⁻¹ = v (.ofAdd a) := by
  let w := (MulAut.conj x).toMonoidHom.comp u
  have h : w = v := hom_ext_of_scalar_equivariant n hn f hk w v
    (MonoidHom.ext fun a => hproj a.toAdd) z c hc (by
      intro a
      change (MulAut.conj z) (x * u (.ofAdd a) * x⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      change (z*x*z⁻¹) * (z*u (.ofAdd a)*z⁻¹) * (z*x*z⁻¹)⁻¹ = _
      rw [hfix, hu]
      rfl) hv
  intro a
  exact DFunLike.congr_fun h (.ofAdd a)

/-- A fixed element commutes with a moved additive root whenever their
projections commute. The conclusion is an equality in the extension. -/
theorem commute_of_scalar {F : Type*} [Field F]
    (hk : f.ker ≤ Subgroup.center E) (u : Multiplicative F →* E)
    (x z : E) (c : F) (hc : c ≠ 1)
    (hfix : z*x*z⁻¹ = x)
    (hbase : ∀ a, Commute (f x) (f (u (.ofAdd a))))
    (hu : ∀ a, z*u (.ofAdd a)*z⁻¹ = u (.ofAdd (c*a))) :
    ∀ a, Commute x (u (.ofAdd a)) := by
  have h := conjugation_eq_of_scalar hk u u x z c hc hfix (by
    intro a
    rw [map_mul, map_mul, map_inv, (hbase a).eq, mul_inv_cancel_right]) hu hu
  intro a
  exact mul_inv_eq_iff_eq_mul.mp (h a)

private def longWeights : Fin 3 → Fin 4 → ℤ :=
  ![![-1, 2, -1, -1], ![1, -1, 1, 1], ![0, 1, 0, 0]]

private theorem long_pairing (i : Fin 3) (j : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex (longPosition i))
      (typeDSimpleRootIndex 2 j) = longWeights i j := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex j) k *
      rootCoords (positiveIndex (longPosition i)) k) = longWeights i j := by
    revert i j
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (longWeights i j : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem conj_mul {G : Type*} [Group G] (a b x : G) :
    (a*b)*x*(a*b)⁻¹ = a*(b*x*b⁻¹)*a⁻¹ := by group

private theorem arms_highest_fixed (Q : Parameters) (hp : Q.prime = 2)
    (t : (ExtensionField Q)ˣ) (u : fixedField Q) :
    elementaryInclusion Q (torusElementary Q hp .arms t) * longSplit Q 2 u *
      (elementaryInclusion Q (torusElementary Q hp .arms t))⁻¹ = longSplit Q 2 u := by
  simp only [torusElementary_arms_val, conj_mul, longSplit,
    torusWord_curve_conjugate Q hp, long_pairing]
  simp [longWeights]

private theorem central_lowest_scale (Q : Parameters) (hp : Q.prime = 2)
    (t : (fixedField Q)ˣ) (u : fixedField Q) :
    elementaryInclusion Q (torusElementary Q hp .central t) * longSplit Q 0 u *
      (elementaryInclusion Q (torusElementary Q hp .central t))⁻¹ =
      longSplit Q 0 (t.val^2*u) := by
  simp only [torusElementary_central_val, longSplit,
    torusWord_curve_conjugate Q hp, long_pairing]
  simp [longWeights, TorusCoordinates.fixedUnit]

/-- Weights of the actual arms actors on the three fixed-field roots. -/
def longArmsWeight (t : (ExtensionField P)ˣ) : Fin 3 → fixedField P :=
  ![(cubicNorm P t.val)⁻¹, cubicNorm P t.val, 1]

/-- Weights of the actual central actors on the three fixed-field roots. -/
def longCentralWeight (t : (fixedField P)ˣ) : Fin 3 → fixedField P :=
  ![t.val^2, t.val⁻¹, t.val]

private theorem descend_long_scale (Q : Parameters) (hp : Q.prime = 2)
    (i : Fin 3) (a : Node) (t : (RootField Q a)ˣ) (c : fixedField Q)
    (h : ∀ u, elementaryInclusion Q (torusElementary Q hp a t) * longSplit Q i u *
      (elementaryInclusion Q (torusElementary Q hp a t))⁻¹ = longSplit Q i (c*u))
    (u : fixedField Q) :
    torusActor Q hp a t * long Q hp i u * (torusActor Q hp a t)⁻¹ = long Q hp i (c*u) := by
  simp only [torusActor, long, ← map_mul, ← map_inv]
  apply congrArg (toCarrier Q)
  apply elementaryInclusion_injective Q
  simp only [map_mul, map_inv, longElementary_val]
  exact h u

/-- Simultaneous arms action on the given normalized long-root sections. -/
theorem normalized_long_arms (L : RootSections n hn f) (hL : L.TorusNormalized)
    (t : (ExtensionField P)ˣ) (z : E) (hz : f z = torusActor P rfl .arms t)
    (i : Fin 3) (u : fixedField P) :
    z * L.longValue i u * z⁻¹ = L.longValue i (longArmsWeight t i * u) := by
  apply hL.2 i .arms t (longArmsWeight t i) _ z hz u
  intro v
  apply descend_long_scale P rfl i .arms t (longArmsWeight t i)
  fin_cases i
  · exact torus_arms_long_zero_conjugate P rfl t
  · exact torus_arms_long_one_conjugate P rfl t
  · simpa [longArmsWeight] using arms_highest_fixed P rfl t

/-- Simultaneous central action on the given normalized long-root sections. -/
theorem normalized_long_central (L : RootSections n hn f) (hL : L.TorusNormalized)
    (t : (fixedField P)ˣ) (z : E) (hz : f z = torusActor P rfl .central t)
    (i : Fin 3) (u : fixedField P) :
    z * L.longValue i u * z⁻¹ = L.longValue i (longCentralWeight t i * u) := by
  apply hL.2 i .central t (longCentralWeight t i) _ z hz u
  intro v
  apply descend_long_scale P rfl i .central t (longCentralWeight t i)
  fin_cases i
  · exact central_lowest_scale P rfl t
  · exact torus_central_long_one_conjugate P rfl t
  · exact torus_central_long_two_conjugate P rfl t

private theorem base_long_commute_highest (i : Fin 3) (hi : i ≠ 2)
    (s t : fixedField P) : Commute (long P rfl i s) (long P rfl 2 t) := by
  have h : Commute (longElementary P rfl i s) (longElementary P rfl 2 t) := by
    change longElementary P rfl i s * longElementary P rfl 2 t =
      longElementary P rfl 2 t * longElementary P rfl i s
    apply elementaryInclusion_injective P
    simp only [map_mul, longElementary_val P rfl i s, longElementary_val P rfl 2 t]
    apply nonsumCommute_parameters P (longPosition i) (longPosition 2)
      (by fin_cases i <;> simp_all [longPosition])
    rintro ⟨k, hk⟩
    have hsum : ∀ j : Fin 3, ∀ k : Fin 12,
        (longPosition j, longPosition 2, k) ∉ SumExchangeData.sumTriples := by decide +kernel
    exact hsum i k ((SumExchangeData.mem_sumTriples_iff _ _ _).mpr
      ((SumExchangeData.root_sum_iff _ _ _).mp hk))
  exact h.map (toCarrier P)

private theorem large_q (hlarge : 2 ≤ n) : 2 < (binaryParameters n hn).q := by
  change 2 < 2^n
  simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 1 < n)

/-- The two commuting long-root pairs lift without a central defect,
including over the fixed field of order four. -/
theorem normalized_long_commute_highest (L : RootSections n hn f)
    (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (i : Fin 3) (hi : i ≠ 2) (s t : fixedField P) :
    Commute (L.longValue i s) (L.longValue 2 t) := by
  obtain ⟨a, ha⟩ := exists_cubicNorm_ne_one P (large_q hlarge)
  obtain ⟨z, hz⟩ := hf (torusActor P rfl .arms a)
  have hc : longArmsWeight a i ≠ 1 := by
    fin_cases i
    · exact inv_ne_one.mpr ha
    · exact ha
    · exact (hi rfl).elim
  apply Commute.symm
  apply commute_of_scalar hk (L.longRoot i) (L.longValue 2 t) z (longArmsWeight a i) hc
  · simpa [longArmsWeight] using L.normalized_long_arms hL a z hz 2 t
  · intro b
    simpa only [longValue, L.project_long] using (base_long_commute_highest i hi b t).symm
  · exact L.normalized_long_arms hL a z hz i

/-- The A₂ exchange among the three long roots holds in the extension,
not merely after applying its projection. -/
theorem normalized_long_exchange (L : RootSections n hn f)
    (hL : L.TorusNormalized) (hlarge : 2 ≤ n)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    L.LongExchangeRelation := by
  obtain ⟨a, ha⟩ := exists_cubicNorm_ne_one P (large_q hlarge)
  have hN : cubicNorm P a.val ≠ 0 := by
    intro h
    have hv := congrArg Subtype.val h
    change a.val * fieldFrobenius P a.val * fieldFrobenius P (fieldFrobenius P a.val) = 0 at hv
    exact (mul_ne_zero (mul_ne_zero a.ne_zero ((fieldFrobenius P).map_ne_zero_iff.mpr a.ne_zero))
      ((fieldFrobenius P).map_ne_zero_iff.mpr ((fieldFrobenius P).map_ne_zero_iff.mpr a.ne_zero))) hv
  let c : (fixedField P)ˣ := Units.mk0 (cubicNorm P a.val) hN
  obtain ⟨za, hza⟩ := hf (torusActor P rfl .arms a)
  obtain ⟨zc, hzc⟩ := hf (torusActor P rfl .central c)
  let z := za * za * zc
  have hz (i : Fin 3) (t : fixedField P) :
      z * L.longValue i t * z⁻¹ =
        L.longValue i (![1, c.val, c.val] i * t) := by
    dsimp [z]
    simp only [conj_mul, L.normalized_long_central hL c zc hzc,
      L.normalized_long_arms hL a za hza]
    congr 1
    fin_cases i <;> simp [longArmsWeight, longCentralWeight, c, pow_two, hN,
      mul_assoc, mul_comm, mul_left_comm]
  intro s t
  let v : Multiplicative (fixedField P) →* E := {
    toFun := fun u => L.longValue 1 u.toAdd * L.longValue 2 (s*u.toAdd)
    map_one' := by simp [longValue]
    map_mul' := by
      intro u w
      change L.longValue 1 (u.toAdd+w.toAdd) * L.longValue 2 (s*(u.toAdd+w.toAdd)) = _
      rw [mul_add, show L.longValue 1 (u.toAdd+w.toAdd) =
        L.longValue 1 u.toAdd * L.longValue 1 w.toAdd from (L.longRoot 1).map_mul _ _,
        show L.longValue 2 (s*u.toAdd+s*w.toAdd) =
        L.longValue 2 (s*u.toAdd) * L.longValue 2 (s*w.toAdd) from (L.longRoot 2).map_mul _ _]
      have hc := L.normalized_long_commute_highest hL hlarge hf hk 1 (by decide)
        w.toAdd (s*u.toAdd)
      calc
        _ = L.longValue 1 u.toAdd *
          (L.longValue 1 w.toAdd * L.longValue 2 (s*u.toAdd)) * L.longValue 2 (s*w.toAdd) := by group
        _ = _ := by rw [hc.eq]; group }
  have he := conjugation_eq_of_scalar hk (L.longRoot 1) v (L.longValue 0 s) z c.val ha
    (by simpa using hz 0 s) (by
      intro u
      change f (L.longValue 0 s * L.longValue 1 u * (L.longValue 0 s)⁻¹) =
        f (L.longValue 1 u * L.longValue 2 (s*u))
      simp only [map_mul, map_inv, longValue, L.project_long]
      rw [long_zero_one_exchange P rfl]
      have hc := base_long_commute_highest 0 (by decide) s (s*u)
      calc
        _ = long P rfl 1 u *
          (long P rfl 0 s * long P rfl 2 (s*u) * (long P rfl 0 s)⁻¹) := by group
        _ = _ := by rw [hc.eq]; simp [mul_assoc])
    (by intro u; simpa using hz 1 u) (by
      intro u
      change (MulAut.conj z) (L.longValue 1 u * L.longValue 2 (s*u)) = _
      rw [map_mul]
      change (z*L.longValue 1 u*z⁻¹) * (z*L.longValue 2 (s*u)*z⁻¹) = _
      simp only [hz, Matrix.cons_val_one, Matrix.cons_val_zero]
      change L.longValue 1 (c.val*u) * L.longValue 2 (c.val*(s*u)) =
        L.longValue 1 (c.val*u) * L.longValue 2 (s*(c.val*u))
      rw [mul_left_comm c.val s u]) t
  have hc := L.normalized_long_commute_highest hL hlarge hf hk 0 (by decide) s (s*t)
  change L.longValue 0 s * L.longValue 1 t = _
  calc
    _ = (L.longValue 1 t * L.longValue 2 (s*t)) * L.longValue 0 s :=
      mul_inv_eq_iff_eq_mul.mp he
    _ = _ := by rw [mul_assoc, hc.symm.eq, ← mul_assoc]

end RootSections
end
end Triality.Standard.CentralCovers.TwoPrimary
