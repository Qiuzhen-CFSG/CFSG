module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand

/-!
# Fixed spaces and Cartan normality through the literal quotient

The corrected center identity reduces Cartan fixed-space equality to the
first flag subgroup. The ambient fixed summand is nonzero exactly when its
embedded binary subspace is. A factorization modulo C_Y(Z1) normalizes the
Cartan image; the proved source stabilizer equality gives the GO normality
clause. No normality of X in the whole stabilizer is assumed.

Source: Aschbacher--Smith, 11.1.5, printed p.766. The local factorization and
line-centralizer calculation remain with the source geometry construction.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The center identity reduces equality of the two centralizers to the
preceding fixed-point calculation on the original flag line. -/
theorem fixedSubspace_eq_of_line {R L U X : Subgroup G}
    (hX : X ≤ L) (hz : radicalOmegaCenter R = U ⊔ radicalFixedCenter R L)
    (hline : U ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) :
    fixedSubspace R X = fixedSubspace R L := by
  have he : radicalFixedCenter R X = radicalFixedCenter R L := by
    apply le_antisymm
    · rintro z ⟨hzZ, hzX⟩
      refine ⟨hzZ, ?_⟩
      have hUZ : U ≤ radicalOmegaCenter R := hz ▸ le_sup_left
      have hz' : (⟨z, hzZ⟩ : radicalOmegaCenter R) ∈
          U.subgroupOf (radicalOmegaCenter R) ⊔
          (radicalFixedCenter R L).subgroupOf (radicalOmegaCenter R) := by
        rw [← subgroupOf_sup hUZ (show radicalFixedCenter R L ≤ radicalOmegaCenter R from inf_le_left)]
        exact hz ▸ hzZ
      obtain ⟨u, hu, w, hw, he⟩ := Subgroup.mem_sup_of_normal_right.mp hz'
      have hprod : (u : G) * (w : G) = z := congrArg Subtype.val he
      rw [← hprod] at hzX ⊢
      have hwX : (w : G) ∈ centralizer (X : Set G) := centralizer_le hX hw.2
      have huX : (u : G) ∈ centralizer (X : Set G) := by
        have hh := (centralizer (X : Set G)).mul_mem hzX
          ((centralizer (X : Set G)).inv_mem hwX)
        simpa only [mul_inv_cancel_right] using hh
      exact (centralizer (L : Set G)).mul_mem (hline ⟨hu, huX⟩) hw.2
    · exact inf_le_inf_left _ (centralizer_le hX)
  unfold fixedSubspace
  rw [he]

omit [Finite G] in
/-- The original quotient fixes exactly C_{Z₁}(L) once the preceding
line-centralizer identity is supplied. -/
theorem fixedSpace_eq_of_line {R L U X : Subgroup G}
    (hXY : X ≤ normalizer (R : Set G)) (hXL : X ≤ L)
    (hz : radicalOmegaCenter R = U ⊔ radicalFixedCenter R L)
    (hline : U ⊓ centralizer (X : Set G) ≤ centralizer (L : Set G)) :
    fixedSpace (representation R) (cartanImage R X) = fixedSubspace R L := by
  rw [fixedSpace_cartanImage R X hXY]
  exact fixedSubspace_eq_of_line hXL hz hline

omit [Finite G] in
/-- Nontriviality of the ambient fixed summand is preserved by its original
inclusion as a binary subspace. -/
theorem fixedSubspace_ne_bot {R L : Subgroup G}
    (hne : radicalFixedCenter R L ≠ ⊥) : fixedSubspace R L ≠ ⊥ := by
  intro he
  apply hne
  apply bot_unique
  intro z hz
  have hh : Additive.ofMul (⟨z, hz.1⟩ : radicalOmegaCenter R) ∈ fixedSubspace R L := hz
  rw [he] at hh
  exact congrArg (fun w : Additive (radicalOmegaCenter R) => (w.toMul : G))
    (show Additive.ofMul (⟨z, hz.1⟩ : radicalOmegaCenter R) = 0 from hh)

omit [Finite G] in
/-- Oddness is inherited through the literal restriction and projection. -/
theorem cartanImage_odd {T : Sylow 2 G} {R L X : Subgroup G}
    (hX : IsCartan T L X) (hXY : X ≤ normalizer (R : Set G)) :
    Odd (Nat.card (cartanImage R X)) := by
  have ho : Odd (Nat.card (X.subgroupOf (normalizer (R : Set G)))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXY).toEquiv]
    exact hX.odd
  exact ho.of_dvd_nat (card_map_dvd _ (projection R))

omit [Finite G] in
/-- A local factorization modulo the *actual* centralizer kernel suffices
for normality of the Cartan image. This does not require X itself to be
normal in the stabilizer. -/
theorem cartanImage_normalized_of_cover {R L X : Subgroup G}
    (hcover : (normalizer (L : Set G)).subgroupOf (normalizer (R : Set G)) ≤
      kernel R ⊔ normalizer (X.subgroupOf (normalizer (R : Set G)) : Set _)) :
    ((normalizer (L : Set G)).subgroupOf (normalizer (R : Set G))).map (projection R) ≤
      normalizer (cartanImage R X : Set _) := by
  apply le_trans (map_mono hcover)
  rw [Subgroup.map_sup]
  apply sup_le
  · have hk : (kernel R).map (projection R) = ⊥ := QuotientGroup.map_mk'_self (kernel R)
    rw [hk]
    exact bot_le
  · exact (X.subgroupOf (normalizer (R : Set G))).le_normalizer_map (projection R)

/-- The previously proved source stabilizer equality converts the local
factorization into precisely the GO normality clause. -/
theorem chosen_normal_in_stabilizer
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) {X : Subgroup G}
    (hne : radicalFixedCenter (f.Ri 0) L ≠ ⊥)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (hcover : (normalizer (L : Set G)).subgroupOf (normalizer (f.Ri 0 : Set G)) ≤
      kernel (f.Ri 0) ⊔ normalizer (X.subgroupOf (normalizer (f.Ri 0 : Set G)) : Set _)) :
    ∀ a : Actor (f.Ri 0),
      (fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X)).map
        (representation (f.Ri 0) a) =
        fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) →
      (cartanImage (f.Ri 0) X).map (MulAut.conj a).toMonoidHom =
        cartanImage (f.Ri 0) X := by
  intro a ha
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (kernel (f.Ri 0)) a
  rw [hfixed] at ha
  have hs : y ∈ (subspaceStabilizer (representation (f.Ri 0))
      (fixedSubspace (f.Ri 0) L)).comap (projection (f.Ri 0)) :=
    (mem_subspaceStabilizer_iff_map _ _).mpr ha
  rw [stabilizer_comap] at hs
  have hyL : (y : G) ∈ normalizer (L : Set G) :=
    ((chosen_fixed_stabilizer D S f hne) ▸
      (show (y : G) ∈ normalizer (f.Ri 0 : Set G) ⊓
        normalizer (radicalFixedCenter (f.Ri 0) L : Set G) from ⟨y.property, hs⟩)).2
  exact mem_normalizer_iff_map_conj_eq.mp
    (cartanImage_normalized_of_cover hcover (mem_map_of_mem _ hyL))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair
