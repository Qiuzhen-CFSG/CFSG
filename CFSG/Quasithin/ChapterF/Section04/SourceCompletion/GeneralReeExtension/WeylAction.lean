module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Recognition
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Cartan
public import Theory.SpecificGroups.ReeF4.SmallCompletion.TorusAction

/-!
# The possible Ree mixed relation centralizes the marked Cartan

The two endpoint maps transport the exact native torus actions. Iterating
their product transports the native eighth-power identity on the torus,
even though that identity is not known for the group elements themselves.
Thus the possible relation element centralizes the full marked Cartan.
If it lies in the native Borel image, Cartan self-normalization places it
in the Cartan. Both statements hold for every positive parameter, including
q=8, without an order or apartment hypothesis.

Source: the Cartan localization in Aschbacher–Smith F.4.10,16, pp.279,282.
The native half-turn inverts this Cartan, whose order is odd, so such a
Cartan defect is trivial. Thus the remaining relation is exactly its native
Borel membership; this membership is not inferred from the order bound.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
open Subgroup Theory.GroupTheory ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.SmallCompletion
variable {m : ℕ} (E : SourceExtension m) {M : Type*} [Group M] (c : Completion E M)

/-- The actual native Cartan homomorphism induced by the marked Borel. -/
def cartanHom : fixedTorus m →* M :=
  (nativeBorelMap E c).comp (inclusion (fixedTorus_le_borel m))

private def endpointMap : (s : Side) → parabolic m s →* M
  | .linear => nativeLeft E c
  | .suzuki => nativeRight E c

private theorem endpointMap_borel (s : Side) (b : borel m) :
    endpointMap E c s ⟨b.val,borel_le_parabolic m s b.property⟩ = nativeBorelMap E c b := by
  cases s with
  | linear => rfl
  | suzuki =>
    exact (DFunLike.congr_fun c.compatible
      ⟨MulAut.conj b.val,
        ((nativeLeftLocal E) ⟨b.val,borel_le_parabolic m .linear b.property⟩).property,
        ((nativeRightLocal E) ⟨b.val,borel_le_parabolic m .suzuki b.property⟩).property⟩).symm

private theorem cartanHom_endpoint (s : Side) (t : fixedTorus m) :
    cartanHom E c t = endpointMap E c s
      ⟨t.val,borel_le_parabolic m s (fixedTorus_le_borel m t.property)⟩ :=
  (endpointMap_borel E c s ⟨t.val,fixedTorus_le_borel m t.property⟩).symm

private theorem reflection_conjugates (s : Side) (t : fixedTorus m) :
    endpointMap E c s (reflection m s) * cartanHom E c t *
      (endpointMap E c s (reflection m s))⁻¹ =
      cartanHom E c (torusReflection m s t) := by
  rw [cartanHom_endpoint E c s,cartanHom_endpoint E c s,←map_inv,←map_mul,←map_mul]
  apply congrArg (endpointMap E c s)
  apply Subtype.ext
  rfl

private theorem rotation_conjugates (t : fixedTorus m) :
    weylProduct E c * cartanHom E c t * (weylProduct E c)⁻¹ =
      cartanHom E c ((torusReflection m .linear * torusReflection m .suzuki) t) := by
  calc
    _ = endpointMap E c .linear (reflection m .linear) *
        (endpointMap E c .suzuki (reflection m .suzuki) * cartanHom E c t *
          (endpointMap E c .suzuki (reflection m .suzuki))⁻¹) *
        (endpointMap E c .linear (reflection m .linear))⁻¹ := by
      change (nativeLeft E c (reflection m .linear) * nativeRight E c (reflection m .suzuki)) *
        _ * (nativeLeft E c (reflection m .linear) * nativeRight E c (reflection m .suzuki))⁻¹ = _
      simp only [endpointMap]
      group
    _ = _ := by rw [reflection_conjugates,reflection_conjugates]; rfl

private theorem rotation_power_conjugates (k : ℕ) (t : fixedTorus m) :
    weylProduct E c ^ k * cartanHom E c t * (weylProduct E c ^ k)⁻¹ =
      cartanHom E c (((torusReflection m .linear * torusReflection m .suzuki)^k) t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    calc
      _ = weylProduct E c ^ k *
          (weylProduct E c * cartanHom E c t * (weylProduct E c)⁻¹) *
          (weylProduct E c ^ k)⁻¹ := by rw [pow_succ]; group
      _ = _ := by rw [rotation_conjugates,ih,pow_succ]; rfl

/-- The eighth-power defect centralizes the full marked native Cartan. -/
theorem weylProduct_eight_centralizes_nativeCartan :
    weylProduct E c ^ 8 ∈ centralizer (nativeCartan E c : Set M) := by
  rintro x ⟨b,hb,rfl⟩
  let t : fixedTorus m := ⟨b.val,hb⟩
  have h := rotation_power_conjugates E c 8 t
  rw [torusReflection_product_eight] at h
  change weylProduct E c ^ 8 * nativeBorelMap E c b * (weylProduct E c ^ 8)⁻¹ =
    nativeBorelMap E c b at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

/-- Borel membership localizes the possible mixed relation to the actual
Cartan image. Membership itself is not inferred from the order bound. -/
theorem weylProduct_eight_mem_cartan_of_mem_borel (hm : 0 < m)
    (hb : weylProduct E c ^ 8 ∈ (nativeBorelMap E c).range) :
    weylProduct E c ^ 8 ∈ nativeCartan E c := by
  apply (nativeBorel_inf_normalizer_nativeCartan E c hm).le
  exact ⟨hb,(centralizer_le_normalizer (nativeCartan E c : Set M))
    (weylProduct_eight_centralizes_nativeCartan E c)⟩

private theorem cartanHom_injective (hm : 0 < m) : Function.Injective (cartanHom E c) := by
  intro t u he
  apply Subtype.ext
  apply ReeF4.SmallCompletion.conj_injective m hm
  exact congrArg Subtype.val (c.left_injective he)

/-- The transported half-turn inverts every marked Cartan element. -/
theorem weylProduct_four_inverts_cartan (t : fixedTorus m) :
    weylProduct E c ^ 4 * cartanHom E c t * (weylProduct E c ^ 4)⁻¹ =
      (cartanHom E c t)⁻¹ := by
  rw [rotation_power_conjugates,torusReflection_product_four,map_inv]

/-- A relation defect lying in the native Cartan is trivial: the half-turn
inverts it, while every power of the same Weyl product centralizes it. -/
theorem weylProduct_eight_eq_one_of_mem_cartan (hm : 0 < m)
    (ht : weylProduct E c ^ 8 ∈ nativeCartan E c) : weylProduct E c ^ 8 = 1 := by
  obtain ⟨b,hb,he⟩ := ht
  let t : fixedTorus m := ⟨b.val,hb⟩
  have hp : cartanHom E c t = weylProduct E c ^ 8 := he
  have hi := weylProduct_four_inverts_cartan E c t
  rw [hp] at hi
  have hinv : weylProduct E c ^ 8 = (weylProduct E c ^ 8)⁻¹ := by
    calc
      _ = weylProduct E c ^ 4 * weylProduct E c ^ 8 * (weylProduct E c ^ 4)⁻¹ := by group
      _ = _ := hi
  have hs : (cartanHom E c t)^2 = 1 := by
    rw [hp,pow_two]
    nth_rw 1 [hinv]
    exact inv_mul_cancel _
  have ht2 : t^2 = 1 := cartanHom_injective E c hm (by rw [map_pow,hs,map_one])
  have hcop : (Nat.card (fixedTorus m)).Coprime 2 := Nat.coprime_two_right.mpr
    (fixedTorus_odd_card m (ReeF4.SectionGeometry.BNPair.splitTorus_card_odd m))
  have ht1 : t = 1 := (powCoprime hcop).injective (by
    change t^2 = (1 : fixedTorus m)^2
    simpa only [one_pow] using ht2)
  rw [←hp,ht1,map_one]

/-- The unresolved native marked apartment closure is exactly a Borel
membership question, with the possible Cartan kernel already eliminated. -/
theorem weylProduct_eight_eq_one_iff_mem_borel (hm : 0 < m) :
    weylProduct E c ^ 8 = 1 ↔ weylProduct E c ^ 8 ∈ (nativeBorelMap E c).range := by
  constructor
  · intro he
    rw [he]
    exact one_mem _
  · intro hb
    exact weylProduct_eight_eq_one_of_mem_cartan E c hm
      (weylProduct_eight_mem_cartan_of_mem_borel E c hm hb)

/-- The exact remaining native Borel membership supplies the full requested
faithful extension action through the marked paired comparison. -/
theorem faithful_extension_of_marked_borel_membership (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hb : weylProduct E c ^ 8 ∈ (nativeBorelMap E c).range) :
    Nat.card M = Nat.card E.carrier ∧
      ∃ a : M →* MulAut (ReeF4.Model m), Function.Injective a ∧
        (MulAut.conj : ReeF4.Model m →* MulAut (ReeF4.Model m)).range ≤ a.range ∧
        ∀ g : M, UnitaryNonbinary.PreservesTypes
          (parabolic m .linear) (parabolic m .suzuki) (a g) :=
  faithful_extension_of_weyl_relation E c hm hc
    ((weylProduct_eight_eq_one_iff_mem_borel E c hm).mpr hb)

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
