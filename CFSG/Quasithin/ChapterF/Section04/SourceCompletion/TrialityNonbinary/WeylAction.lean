module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.FixedApartment
public import Theory.SpecificGroups.Triality.SmallCompletion.TorusAction

/-!
# Eliminating the marked triality apartment defect

The endpoint markings transport the native half-turn inversion on the full
Cartan. The sixth power therefore centralizes this Cartan. Once the native
hexagon places it in the native Borel, Cartan self-normalization puts it in
the odd Cartan. A power of the rotation commutes with the half-turn, so
inversion forces the defect to be trivial. This uses the actual native
Borel, not the potentially larger outer overlap.

Source: Aschbacher--Smith F.4.10,16,24, pp.279,282,287--288.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open scoped Pointwise

private theorem borel_normalizer_torus (m : ℕ) (hm : 0 < m) (hm2 : 1 < m)
    (b : BinaryCarrier m hm) (hb : b ∈ borel (binaryParameters m hm))
    (hn : b ∈ normalizer (torus (binaryParameters m hm) : Set (BinaryCarrier m hm))) :
    b ∈ torus (binaryParameters m hm) := by
  have hprod : b ∈ (unipotent (binaryParameters m hm) : Set (BinaryCarrier m hm)) *
      (torus (binaryParameters m hm) : Set (BinaryCarrier m hm)) := by
    rw [←borel_eq_mul (binaryParameters m hm) rfl]
    exact hb
  obtain ⟨u,hu,t,ht,rfl⟩ := hprod
  have hun : u ∈ normalizer (torus (binaryParameters m hm) : Set (BinaryCarrier m hm)) := by
    have hh := (normalizer (torus (binaryParameters m hm) : Set (BinaryCarrier m hm))).mul_mem hn
      ((normalizer (torus (binaryParameters m hm) : Set (BinaryCarrier m hm))).inv_mem
        ((torus (binaryParameters m hm)).le_normalizer ht))
    simpa only [mul_inv_cancel_right] using hh
  change u*t ∈ torus (binaryParameters m hm)
  rw [TrialityOuterTorus.unipotent_torus_normalizer_trivial m hm hm2 u hu hun,one_mul]
  exact ht

private theorem torusReflection_power_val (m : ℕ) (hm : 0 < m) (k : ℕ)
    (t : torus (binaryParameters m hm)) :
    (((torusReflection m hm .arms * torusReflection m hm .central)^k) t).val =
      ((reflection m hm .arms).val*(reflection m hm .central).val)^k*t.val*
        (((reflection m hm .arms).val*(reflection m hm .central).val)^k)⁻¹ := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih]
    change _ * ((reflection m hm .arms).val *
      ((reflection m hm .central).val*t.val*(reflection m hm .central).val⁻¹)*
      (reflection m hm .arms).val⁻¹) * _ = _
    rw [pow_succ]
    group

private theorem torusReflection_cube (m : ℕ) (hm : 0 < m)
    (t : torus (binaryParameters m hm)) :
    ((torusReflection m hm .arms * torusReflection m hm .central)^3) t=t⁻¹ := by
  apply Subtype.ext
  rw [torusReflection_power_val]
  exact SmallCompletion.simpleProduct_cube_inverts m hm t

private theorem torusReflection_six (m : ℕ) (hm : 0 < m)
    (t : torus (binaryParameters m hm)) :
    ((torusReflection m hm .arms * torusReflection m hm .central)^6) t=t := by
  rw [show (6 : ℕ)=3+3 from rfl,pow_add,MulAut.mul_apply,torusReflection_cube,
    torusReflection_cube,inv_inv]

namespace NativeCompletion
variable {m : ℕ} {hm : 0 < m} {M : Type*} [Group M] (c : NativeCompletion m hm M)

/-- The rotation determined by the literal native endpoint markings. -/
def weylProduct : M := c.left (reflection m hm .arms)*c.right (reflection m hm .central)

private def torusMap : torus (binaryParameters m hm) →* M :=
  c.middle.comp (inclusion (torus_le_borel _))

private def endpointMap : (s : Node) → parabolic (binaryParameters m hm) s →* M
  | .arms => c.left
  | .central => c.right

private theorem endpointMap_borel (s : Node) (b : borel (binaryParameters m hm)) :
    endpointMap c s ⟨b.val,borel_le_parabolic _ s b.property⟩=c.middle b := by
  cases s with
  | arms => rfl
  | central => exact (DFunLike.congr_fun c.compatible b).symm

private theorem torusMap_endpoint (s : Node) (t : torus (binaryParameters m hm)) :
    torusMap c t=endpointMap c s ⟨t.val,borel_le_parabolic _ s (torus_le_borel _ t.property)⟩ :=
  (endpointMap_borel c s ⟨t.val,torus_le_borel _ t.property⟩).symm

private theorem reflection_conjugates (s : Node) (t : torus (binaryParameters m hm)) :
    endpointMap c s (reflection m hm s)*torusMap c t*(endpointMap c s (reflection m hm s))⁻¹ =
      torusMap c (torusReflection m hm s t) := by
  rw [torusMap_endpoint c s,torusMap_endpoint c s,←map_inv,←map_mul,←map_mul]
  rfl

private theorem rotation_conjugates (t : torus (binaryParameters m hm)) :
    weylProduct c * torusMap c t * (weylProduct c)⁻¹ =
      torusMap c ((torusReflection m hm .arms*torusReflection m hm .central) t) := by
  calc
    _ = endpointMap c .arms (reflection m hm .arms)*
        (endpointMap c .central (reflection m hm .central)*torusMap c t*
          (endpointMap c .central (reflection m hm .central))⁻¹)*
        (endpointMap c .arms (reflection m hm .arms))⁻¹ := by
      dsimp [weylProduct,endpointMap]
      group
    _ = _ := by rw [reflection_conjugates,reflection_conjugates]; rfl

private theorem rotation_power_conjugates (k : ℕ) (t : torus (binaryParameters m hm)) :
    weylProduct c ^ k * torusMap c t * (weylProduct c ^ k)⁻¹ =
      torusMap c (((torusReflection m hm .arms*torusReflection m hm .central)^k) t) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    calc
      _ = weylProduct c ^ k * (weylProduct c * torusMap c t * (weylProduct c)⁻¹) *
          (weylProduct c ^ k)⁻¹ := by rw [pow_succ]; group
      _ = _ := by rw [rotation_conjugates,ih,pow_succ]; rfl

/-- Native Borel membership kills the actual sixth-power relation defect. -/
theorem weylProduct_six_eq_one_of_mem_middle (hm2 : 1 < m)
    (hb : weylProduct c ^ 6 ∈ c.middle.range) : weylProduct c ^ 6=1 := by
  obtain ⟨b,hb⟩ := hb
  have hcent : b.val ∈ centralizer (torus (binaryParameters m hm) : Set (BinaryCarrier m hm)) := by
    intro t ht
    let z : torus (binaryParameters m hm) := ⟨t,ht⟩
    have hh := rotation_power_conjugates c 6 z
    rw [torusReflection_six,←hb] at hh
    have he : c.middle b * torusMap c z = torusMap c z * c.middle b :=
      mul_inv_eq_iff_eq_mul.mp hh
    have he' : b*⟨t,torus_le_borel _ ht⟩=⟨t,torus_le_borel _ ht⟩*b :=
      c.middle_injective (by simp only [map_mul]; exact he)
    exact (congrArg Subtype.val he').symm
  have hbt := borel_normalizer_torus m hm hm2 b.val b.property
    (centralizer_le_normalizer _ hcent)
  let t : torus (binaryParameters m hm) := ⟨b.val,hbt⟩
  have hp : torusMap c t=weylProduct c ^ 6 := hb
  have hi := rotation_power_conjugates c 3 t
  rw [torusReflection_cube,map_inv,hp] at hi
  have hinv : weylProduct c ^ 6=(weylProduct c ^ 6)⁻¹ := by
    calc
      _ = weylProduct c ^ 3*weylProduct c ^ 6*(weylProduct c ^ 3)⁻¹ := by group
      _ = _ := hi
  have hs : (torusMap c t)^2=1 := by
    rw [hp,pow_two]
    nth_rw 1 [hinv]
    exact inv_mul_cancel _
  have hti : Function.Injective (torusMap c) :=
    c.middle_injective.comp (inclusion_injective (torus_le_borel _))
  have ht2 : t^2=1 := hti (by rw [map_pow,hs,map_one])
  have hcop : (Nat.card (torus (binaryParameters m hm))).Coprime 2 :=
    Nat.coprime_two_right.mpr (by
      rw [TorusCoordinates.card_torus _ rfl]
      exact TorusCoordinates.odd_torus_order _ rfl)
  have ht1 : t=1 := (powCoprime hcop).injective (by
    change t^2=(1 : torus (binaryParameters m hm))^2
    simpa only [one_pow] using ht2)
  rw [←hp,ht1,map_one]
end NativeCompletion

/-- The original full extension bound forces the literal marked hexagon
relation, uniformly for every nonbinary exponent, including m=2. -/
theorem marked_six_eq_one {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)
    {M : Type*} [Group M] [Finite M] (c : Completion E M) (hm2 : 1 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    (c.left (E.nativeLeft (reflection m hm .arms))*
      c.right (E.nativeRight (reflection m hm .central)))^6=1 := by
  have hb := (nativeCompletion E c).marked_six_mem_middle_of_diameter hm2
    (nativeCompletion_overlap E c ho) (nativeCore_diameter_le E c hm2 ho horder)
  exact congrArg Subtype.val
    ((nativeCompletion E c).weylProduct_six_eq_one_of_mem_middle hm2 hb)
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
