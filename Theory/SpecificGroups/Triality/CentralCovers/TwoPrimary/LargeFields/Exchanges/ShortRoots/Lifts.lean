module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Weights
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Model
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.ShortRoots.Additivity

/-!
# Removing central defects from the four short triality exchanges

Compare actual conjugation with the additive polynomial candidates. Their
projections agree by the checked carrier calculations, and both maps are
equivariant for an actor fixing the conjugating root and moving the variable
by a nonidentity scalar. Central-kernel uniqueness identifies the maps.
The trace relations come first, then short0/short1, then short0/long0.

Source: GLS3 §§2.4.5(b), 2.4.7 and 6.1; Aschbacher–Smith I.1.3.
-/

set_option linter.unusedSimpArgs false
@[expose] public section
noncomputable section
namespace Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
open Parabolics RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers ConcreteBruhat
variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E]
variable {f : E →* BinaryCarrier n hn}
local notation "P" => binaryParameters n hn
local notation "F" => fieldFrobenius P
local notation "T" => cubicTrace P

private theorem compare (hk : f.ker ≤ Subgroup.center E) {K : Type*} [Field K]
    (u : Multiplicative K →* E) (x z : E) (hx : x⁻¹ = x) (c : K) (hc : c ≠ 1)
    (hfix : z*x*z⁻¹ = x) (hu : ∀ s, z*u (.ofAdd s)*z⁻¹ = u (.ofAdd (c*s)))
    (w : K → E) (hzero : w 0 = 1) (hadd : ∀ s t, w (s+t)=w s*w t)
    (hproj : ∀ s, f (u (.ofAdd s))*f x = f x*f (w s))
    (hw : ∀ s, z*w s*z⁻¹ = w (c*s)) :
    ∀ s, u (.ofAdd s)*x = x*w s := by
  let v : Multiplicative K →* E := {
    toFun := fun a => w a.toAdd
    map_one' := hzero
    map_mul' := fun a b => hadd a.toAdd b.toAdd }
  have hx2 : x*x=1 := by calc
    x*x = x⁻¹*x := by rw [hx]
    _ = 1 := inv_mul_cancel x
  have he := conjugation_eq_of_scalar hk u v x z c hc hfix (by
    intro s
    change f (x*u (.ofAdd s)*x⁻¹) = f (w s)
    calc
      _ = f x*(f (u (.ofAdd s))*f x) := by simp only [hx, map_mul, mul_assoc]
      _ = f x*(f x*f (w s)) := by rw [hproj]
      _ = _ := by rw [← mul_assoc, ← map_mul, hx2, map_one, one_mul]) hu hw
  intro s
  calc
    _ = x*(x*u (.ofAdd s)*x⁻¹) := by simp only [hx, ← mul_assoc, hx2, one_mul]
    _ = x*w s := congrArg (x*·) (he s)

private theorem trace_scale (c : fixedField P) (s t : ExtensionField P) :
    T (F (F (c.val*s))*t) = c * T (F (F s)*t) := by
  apply Subtype.ext
  have hc : F c.val = c.val := c.property
  simp only [cubicTrace_coe, map_mul, hc, Subfield.coe_mul]
  ring

theorem lift_trace (L : RootSections n hn f) (hL : L.TorusNormalized)
    (hC : L.CommutingRelations) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (c : (fixedField P)ˣ) (hc : c.val ≠ 1)
    (i : Fin 2) (s t : ExtensionField P) :
    L.shortValue (Fin.castSucc i) s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue (Fin.castSucc i) s *
        L.longValue (Fin.succ i) (T (F (F s)*t)) := by
  obtain ⟨z, hz⟩ := hf (torusActor P rfl .central c)
  let d : (fixedField P)ˣ := if i = 0 then c⁻¹ else c
  have hd : d.val ≠ 1 := by dsimp [d]; split_ifs <;> simpa using hc
  have hdF : d.val.val ≠ 1 := by intro h; exact hd (Subtype.ext h)
  have hs (u : ExtensionField P) : z*L.shortValue (Fin.castSucc i) u*z⁻¹ =
      L.shortValue (Fin.castSucc i) (d.val.val*u) := by
    rw [short_central L hL c z hz]; fin_cases i <;> simp [d]
  have hl (u : fixedField P) : z*L.longValue (Fin.succ i) u*z⁻¹ =
      L.longValue (Fin.succ i) (d.val*u) := by
    rw [L.normalized_long_central hL c z hz]; fin_cases i <;> simp [d, longCentralWeight]
  have hcomm (u : ExtensionField P) (v : fixedField P) :
      Commute (L.shortValue (Fin.castSucc i) u) (L.longValue (Fin.succ i) v) := by
    fin_cases i
    · exact hC.short0_long1 u v
    · exact hC.short1_long2 u v
  have he := compare hk (L.shortRoot (Fin.castSucc i)) (L.shortValue 2 t) z
    (short_inv L 2 t) d.val.val hdF
    (by simpa using short_central L hL c z hz 2 t) hs
    (fun u => L.shortValue (Fin.castSucc i) u * L.longValue (Fin.succ i) (T (F (F u)*t)))
    (by simp [shortValue, longValue, -fieldFrobenius_apply])
    (by
      intro u v
      simp only [map_add, add_mul, short_add, long_add]
      simp only [mul_assoc, append_relation (hcomm v (T (F (F u)*t))).symm.eq])
    (by
      intro u
      simp only [map_mul, shortValue, longValue, L.project_short, L.project_long]
      fin_cases i
      · simpa [Fin.castSucc, Fin.succ, mul_assoc] using base_trace02 P rfl u t
      · simpa [Fin.castSucc, Fin.succ, mul_assoc] using base_trace12 P rfl u t)
    (by
      intro u
      rw [conj_mul, hs, hl, trace_scale]) s
  simpa only [mul_assoc] using he

theorem lift01 (L : RootSections n hn f) (hL : L.TorusNormalized)
    (hC : L.CommutingRelations) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (c : (fixedField P)ˣ) (hc : c.val ≠ 1)
    (h02 : ∀ s t, L.shortValue 0 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 0 s * L.longValue 1 (T (F (F s)*t)))
    (s t : ExtensionField P) :
    L.shortValue 0 s * L.shortValue 1 t =
      L.shortValue 1 t * L.shortValue 0 s * L.shortValue 2 (higherCoefficient P s t) *
        L.longValue 1 (T (s*F s*F (F t))) * L.longValue 2 (T (s*F t*F (F t))) := by
  obtain ⟨z, hs, hl⟩ := actor01 L hL hf c
  have hcF : F c.val.val = c.val.val := c.val.property
  have hc1 : c.val.val ≠ 1 := fun h => hc (Subtype.ext h)
  have he := compare hk (L.shortRoot 0) (L.shortValue 1 t) z (short_inv L 1 t)
    c.val.val hc1 (by simpa using hs 1 t) (by intro u; simpa using hs 0 u)
    (fun u => L.shortValue 0 u * L.shortValue 2 (higherCoefficient P u t) *
      L.longValue 1 (T (u*F u*F (F t))) * L.longValue 2 (T (u*F t*F (F t))))
    (by simp [shortValue, longValue, higherCoefficient, -fieldFrobenius_apply])
    (candidate01_add L hC h02 t)
    (by
      intro u
      simp only [map_mul, shortValue, longValue, L.project_short, L.project_long]
      simpa only [mul_assoc] using short_zero_one_exchange P rfl u t)
    (by
      intro u
      simp only [conj_mul, hs, hl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      repeat' first
        | apply congrArg₂ (fun a b : E => a*b)
        | apply congrArg (L.shortValue _)
        | apply congrArg (L.longValue _)
      all_goals try rfl
      all_goals try apply Subtype.ext
      all_goals simp only [higherCoefficient, cubicTrace_coe, Subfield.coe_mul, SubmonoidClass.coe_pow,
        map_mul, map_add, hcF, fieldFrobenius_three]
      all_goals ring) s
  simpa only [mul_assoc] using he

theorem lift00 (L : RootSections n hn f) (hL : L.TorusNormalized)
    (hC : L.CommutingRelations) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (c : (fixedField P)ˣ) (hc : c.val ≠ 1)
    (h02 : ∀ s t, L.shortValue 0 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 0 s * L.longValue 1 (T (F (F s)*t)))
    (h12 : ∀ s t, L.shortValue 1 s * L.shortValue 2 t =
      L.shortValue 2 t * L.shortValue 1 s * L.longValue 2 (T (F (F s)*t)))
    (h01 : ∀ s t, L.shortValue 0 s * L.shortValue 1 t =
      L.shortValue 1 t * L.shortValue 0 s * L.shortValue 2 (higherCoefficient P s t) *
        L.longValue 1 (T (s*F s*F (F t))) * L.longValue 2 (T (s*F t*F (F t))))
    (s : ExtensionField P) (t : fixedField P) :
    L.shortValue 0 s * L.longValue 0 t =
      L.longValue 0 t * L.shortValue 0 s * L.shortValue 1 (s*t.val) *
        L.shortValue 2 (s*F s*t.val) * L.longValue 1 (cubicNorm P s*t) := by
  obtain ⟨z, hs, hl⟩ := actor00 L hL hf c
  have hcF : F c.val.val = c.val.val := c.val.property
  have hc1 : c.val.val ≠ 1 := fun h => hc (Subtype.ext h)
  have he := compare hk (L.shortRoot 0) (L.longValue 0 t) z (long_inv L 0 t)
    c.val.val hc1 (by simpa using hl 0 t) (by intro u; simpa using hs 0 u)
    (fun u => L.shortValue 0 u * L.shortValue 1 (u*t.val) *
      L.shortValue 2 (u*F u*t.val) * L.longValue 1 (cubicNorm P u*t))
    (by
      have hN : cubicNorm P 0 = 0 := by apply Subtype.ext; simp [cubicNorm]
      simp [shortValue, longValue, hN, -fieldFrobenius_apply])
    (candidate00_add L hC h02 h12 h01 t)
    (by
      intro u
      simp only [map_mul, shortValue, longValue, L.project_short, L.project_long]
      simpa only [mul_assoc] using base_mixed P rfl u t)
    (by
      intro u
      simp only [conj_mul, hs, hl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      repeat' first
        | apply congrArg₂ (fun a b : E => a*b)
        | apply congrArg (L.shortValue _)
        | apply congrArg (L.longValue _)
      all_goals try rfl
      all_goals try apply Subtype.ext
      all_goals try simp only [cubicNorm, Subfield.coe_mul, SubmonoidClass.coe_pow, map_mul, hcF]
      all_goals ring) s
  simpa only [mul_assoc] using he

end Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
