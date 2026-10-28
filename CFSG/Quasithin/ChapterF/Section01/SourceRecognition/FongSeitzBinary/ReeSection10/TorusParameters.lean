module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSection10.MixedTorusTable

/-!
# Native torus parameters for the synchronized Section 10 torus

The synchronized actors are indexed by the two rank-one parameters used in
the source calculation, whereas `SourceBorel.TorusData` uses the two native
simple-root characters.  The change of coordinates is

`(a,b) ↦ (a² b^(1+2^m), (ab)⁻¹)`.

This module records that coordinate change and its injectivity, including the
binary endpoint.  The remaining root-action equations are deliberately kept
at the consumer boundary: they are the literal mixed equations of Section 10,
not consequences of the cardinality or Weyl data alone.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
open RootPresentationRecognition Parabolics.RadicalCoordinates.FixedCoordinates

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) {n m : ℕ}
  (c : ReeSixHData Q split n m)

def torusCharacters : TorusParameter m →* TorusParameter m where
  toFun p := (p.1^2*p.2^(1+2^m),(p.1*p.2)⁻¹)
  map_one' := by simp
  map_mul' p q := by
    apply Prod.ext <;> simp only [Prod.fst_mul, Prod.snd_mul, mul_pow, mul_inv]
    · ac_rfl
    · ac_rfl

theorem torusCharacters_injective : Function.Injective (torusCharacters (m := m)) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨a,b⟩ hab
  have ha : a = b⁻¹ := by
    have h := congrArg Prod.snd hab
    change (a*b)⁻¹ = 1 at h
    exact eq_inv_of_mul_eq_one_left (inv_eq_one.mp h)
  have hb : (b : CoefficientField m)^(2^m) = b := by
    have h := congrArg (fun p : TorusParameter m => (p.1 : CoefficientField m)) hab
    change (a : CoefficientField m)^2*(b : CoefficientField m)^(1+2^m) = 1 at h
    rw [ha, Units.val_inv_eq_inv_val, pow_add, pow_one] at h
    field_simp at h
    exact h
  have hbf : halfFrobenius m (b : CoefficientField m) = b := by
    change (b : CoefficientField m)^(2^m) = b
    exact hb
  have ht : titsEnd m b = b := by
    have h := congrArg (titsEnd m) hbf
    rw [titsEnd_halfFrobenius] at h
    exact h.symm
  have hb1 : b = 1 := by
    apply Units.ext
    have hs : (b : CoefficientField m)^2 = b := by
      have h := halfFrobenius_sq m (b : CoefficientField m)
      rw [hbf, ht] at h
      exact h
    have h := mul_left_cancel₀ b.ne_zero
      (show (b : CoefficientField m)*b = b*1 from by simpa [pow_two] using hs)
    exact h
  subst b
  simp only [inv_one] at ha
  subst a
  rfl

def torusCharacterEquiv : TorusParameter m ≃* TorusParameter m :=
  MulEquiv.ofBijective (torusCharacters (m := m))
    ⟨torusCharacters_injective (m := m),
      Finite.surjective_of_injective (torusCharacters_injective (m := m))⟩

/-- The synchronized Cartan with native `SourceBorel` parameters. -/
def normalizedSynchronizedTorus : TorusParameter m →* X ⧸ Q.D :=
  (synchronizedTorus Q split c).comp (torusCharacterEquiv (m := m)).symm.toMonoidHom

theorem normalizedSynchronizedTorus_range :
    (normalizedSynchronizedTorus Q split c).range = Q.tits.B ⊓ Q.tits.N := by
  apply le_antisymm
  · rintro x ⟨t, rfl⟩
    change synchronizedTorus Q split c
      ((torusCharacterEquiv (m := m)).symm t) ∈ Q.tits.B ⊓ Q.tits.N
    exact synchronizedTorus_mem_cartan Q split c _ _
  · intro x hx
    have hx' : x ∈ (synchronizedTorus Q split c).range := by
      rw [synchronizedTorus_range Q split c]
      exact hx
    obtain ⟨t, rfl⟩ := hx'
    refine ⟨torusCharacterEquiv (m := m) t, ?_⟩
    change synchronizedTorus Q split c
      ((torusCharacterEquiv (m := m)).symm (torusCharacterEquiv (m := m) t)) =
      synchronizedTorus Q split c t
    rw [MulEquiv.symm_apply_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSection10
