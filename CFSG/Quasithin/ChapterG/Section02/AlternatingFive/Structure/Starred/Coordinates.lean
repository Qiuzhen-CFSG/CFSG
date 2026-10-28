module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.KernelGeometry
public import Theory.Representation.BinaryPermutation.FiveAction
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The derived singular coordinate and Borel in G.2.4

Restrict the given Sylow subgroup of LT to L and pass through the actual
star quotient. A Sylow four-group fixes just one nonzero vector in the
five-point augmentation core, a weight-four word. Thus the original V₁
has a singular coordinate without adding a marking to the hypotheses.
Its normalizer has the full A₄ stabilizer image. Cubic generators show
that this image is unchanged on taking the original two-residual L₁.
The coordinate compatibility also proves that the given g moves the point.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.4(1), printed pp.334–335, PDF pp.345–346.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
namespace Starred
local notation "A5" => alternatingGroup (Fin 5)
open BinaryPermutation

def pointWord (i : Fin 5) : core (Fin 5) :=
  ⟨fun j => if j = i then 0 else 1, by
    change (∑ j : Fin 5, if j = i then (0 : ZMod 2) else 1) = 0
    fin_cases i <;> decide⟩

theorem pointWord_injective : Function.Injective pointWord := by
  intro i j h
  have hv := congrArg (fun v : core (Fin 5) => v.val i) h
  by_contra hn
  simp [pointWord, hn] at hv

theorem pointWord_action (s : Equiv.Perm (Fin 5)) (i : Fin 5) :
    coreRepresentation (Fin 5) s (pointWord i) = pointWord (s i) := by
  apply Subtype.ext
  funext j
  change (if s.symm j = i then (0 : ZMod 2) else 1) = if j = s i then 0 else 1
  simp only [s.symm_apply_eq]

theorem pointWord_singular (i : Fin 5) : FiveGeometry.form (pointWord i) = 0 := by
  fin_cases i <;> decide

private theorem standard_fixed (v : core (Fin 5))
    (ha : coreRepresentation (Fin 5) CubicFixedSpace.Five.first.val v = v)
    (hb : coreRepresentation (Fin 5) CubicFixedSpace.Five.second.val v = v) :
    v = 0 ∨ v = pointWord 4 := by
  have hc : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      representation (Fin 5) CubicFixedSpace.Five.first.val x = x →
      representation (Fin 5) CubicFixedSpace.Five.second.val x = x →
      x = 0 ∨ x = (pointWord 4).val := by decide +kernel
  exact (hc v.val v.property (congrArg Subtype.val ha) (congrArg Subtype.val hb)).imp
    Subtype.ext Subtype.ext

theorem sylow_fixed_pointWord (P : Sylow 2 A5) (v : core (Fin 5)) (hv : v ≠ 0)
    (hfix : ∀ a ∈ P, coreRepresentation (Fin 5) a.val v = v) :
    ∃ i, v = pointWord i := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := CubicFixedSpace.Five.klein_isPGroup.exists_le_sylow
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq A5 Q P
  have hm : (Q : Subgroup A5).map (MulAut.conj s).toMonoidHom = (P : Subgroup A5) := by
    rw [← hs, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  let r := coreRepresentation (Fin 5)
  have hinv (w : core (Fin 5)) : r s.val⁻¹ (r s.val w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (w : core (Fin 5)) : r s.val (r s.val⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hf (a : A5) (ha : a ∈ CubicFixedSpace.Five.klein) :
      r a.val (r s.val⁻¹ v) = r s.val⁻¹ v := by
    have hh := hfix (s * a * s⁻¹) (by
      change s * a * s⁻¹ ∈ (P : Subgroup A5)
      rw [← hm]
      exact mem_map_of_mem _ (hQ ha))
    change r (s.val * a.val * s.val⁻¹) v = v at hh
    have hh' := congrArg (r s.val⁻¹) hh
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, Module.End.mul_apply, hinv] using hh'
  have he := standard_fixed (r s.val⁻¹ v)
    (hf _ CubicFixedSpace.Five.first_mem) (hf _ CubicFixedSpace.Five.second_mem)
  rcases he with he | he
  · exact (hv (by rw [← hginv v, he, map_zero])).elim
  · refine ⟨s.val 4, ?_⟩
    rw [← hginv v, he]
    exact pointWord_action _ _
private def cubic (i : Fin 5) : A5 :=
  MulAut.conjNormal (Equiv.swap 4 i) BinaryPermutation.CubicFixedSpace.Five.cycle

private theorem cubic_facts (i : Fin 5) :
    (cubic i).val i = i ∧ cubic i ^ 3 = 1 := by
  revert i
  decide +kernel

private theorem cubic_factor (i : Fin 5) (a : A5) (ha : a.val i = i) :
    a ^ 3 = 1 ∨ (a * cubic i) ^ 3 = 1 := by
  have h : ∀ (j : Fin 5) (b : A5), b.val j = j →
      b ^ 3 = 1 ∨ (b * cubic j) ^ 3 = 1 := by decide +kernel
  exact h i a ha

/-- A₄ is its two-residual, proved using its cubic generators. -/
theorem stabilizer_twoResidual (i : Fin 5) :
    pResidual 2 (MulAction.stabilizer A5 i) = ⊤ := by
  let B := MulAction.stabilizer A5 i
  have hmem (a : B) (ha : a ^ 3 = 1) : a ∈ pResidual 2 B :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one ha))
  apply top_unique
  intro a _
  rcases cubic_factor i a.val a.property with ha | ha
  · exact hmem a (Subtype.ext ha)
  · let c : B := ⟨cubic i, (cubic_facts i).1⟩
    have hc : c ^ 3 = 1 := Subtype.ext (cubic_facts i).2
    have hac : a * c ∈ pResidual 2 B := hmem _ (Subtype.ext ha)
    simpa only [mul_inv_cancel_right] using
      (pResidual 2 B).mul_mem hac ((pResidual 2 B).inv_mem (hmem c hc))
end Starred

namespace Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The five-point action obtained from the supplied quotient coordinates. -/
def fiveAction : D.L →* alternatingGroup (Fin 5) :=
  d.model.toMonoidHom.comp (starProjection D)

theorem fiveAction_surjective : Function.Surjective d.fiveAction :=
  d.model.surjective.comp (starProjection_surjective D)

theorem exists_point_generator : ∃ a : D.V₁, a ≠ 1 ∧ ∀ b : D.V₁, b ≠ 1 → b = a := by
  obtain ⟨a, ha, hu⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
  exact ⟨a, ha, fun b hb => hu b hb⟩

noncomputable def pointGenerator : D.V₁ := d.exists_point_generator.choose

theorem pointGenerator_ne_one : d.pointGenerator ≠ 1 :=
  d.exists_point_generator.choose_spec.1

theorem eq_pointGenerator (a : D.V₁) (ha : a ≠ 1) : a = d.pointGenerator :=
  d.exists_point_generator.choose_spec.2 a ha

noncomputable def pointVector : BinaryPermutation.core (Fin 5) :=
  (d.coordinates ⟨d.pointGenerator, le_conjugateSpanBy D.V₁ D.L d.pointGenerator.property⟩).toAdd

theorem pointVector_ne_zero : d.pointVector ≠ 0 := by
  intro h
  apply d.pointGenerator_ne_one
  have he : (⟨d.pointGenerator, le_conjugateSpanBy D.V₁ D.L d.pointGenerator.property⟩ : D.VL) = 1 :=
    d.coordinates.injective (h.trans d.coordinates.map_one.symm)
  exact Subtype.ext (congrArg (fun v : D.VL => (v : G)) he)

theorem mem_G₁_iff_fixes_generator (x : G) :
    x ∈ D.G₁ ↔ x * (d.pointGenerator : G) * x⁻¹ = d.pointGenerator := by
  constructor
  · intro hx
    have hm := (mem_normalizer_iff.mp hx (d.pointGenerator : G)).mp d.pointGenerator.property
    have hn : (⟨x * (d.pointGenerator : G) * x⁻¹, hm⟩ : D.V₁) ≠ 1 := by
      intro he
      apply d.pointGenerator_ne_one
      apply Subtype.ext
      have he' := congrArg (fun v : D.V₁ => (v : G)) he
      exact (MulAut.conj x).injective (he'.trans (map_one (MulAut.conj x)).symm)
    exact congrArg Subtype.val (d.eq_pointGenerator _ hn)
  · intro hx
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      by_cases h1 : a = 1
      · simp [h1]
      have he : (⟨a, ha⟩ : D.V₁) = d.pointGenerator := d.eq_pointGenerator _ (fun h => h1 (congrArg Subtype.val h))
      have he' : a = (d.pointGenerator : G) := congrArg Subtype.val he
      rw [he', hx]
      exact d.pointGenerator.property
    · intro ha
      by_cases h1 : x * a * x⁻¹ = 1
      · have : a = 1 := (MulAut.conj x).injective (h1.trans (map_one (MulAut.conj x)).symm)
        simp [this]
      have he := congrArg Subtype.val (d.eq_pointGenerator ⟨_, ha⟩
        (fun h => h1 (congrArg Subtype.val h)))
      have : a = (d.pointGenerator : G) := (MulAut.conj x).injective (he.trans hx.symm)
      rw [this]
      exact d.pointGenerator.property

theorem mem_G₁_iff_fixes_pointVector (l : D.L) :
    (l : G) ∈ D.G₁ ↔ BinaryPermutation.coreRepresentation (Fin 5)
      (d.fiveAction l).val d.pointVector = d.pointVector := by
  rw [d.mem_G₁_iff_fixes_generator]
  have he := d.equivariant l
    ⟨d.pointGenerator, le_conjugateSpanBy D.V₁ D.L d.pointGenerator.property⟩
  constructor
  · intro h
    have hv : (⟨(l : G) * d.pointGenerator * (l : G)⁻¹, (mem_normalizer_iff.mp (L_normalizes_VL D l.property) _).mp (le_conjugateSpanBy D.V₁ D.L d.pointGenerator.property)⟩ : D.VL) =
        ⟨d.pointGenerator, le_conjugateSpanBy D.V₁ D.L d.pointGenerator.property⟩ := Subtype.ext h
    rw [hv] at he
    exact he.symm
  · intro h
    have hv := d.coordinates.injective (he.trans h)
    exact congrArg Subtype.val hv

/-- Restrict the supplied Sylow of LT to its normal subgroup L. -/
theorem exists_sylow_L_le_T : ∃ P : Sylow 2 D.L,
    (P : Subgroup D.L).map D.L.subtype ≤ D.T := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := D.L.subgroupOf D.LT
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le D.L.le_normalizer d.setup.T_normalizes_L)
  obtain ⟨P, hP⟩ := d.setup.sylow_LT
  obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal N
  let e : N ≃* D.L := subgroupOfEquivOfLe le_sup_left
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro _ ⟨l, hl, rfl⟩
  obtain ⟨n, hn, rfl⟩ := hl
  have hnP : n.val ∈ P := by
    change n ∈ (P : Subgroup D.LT).subgroupOf N
    rw [← hQ]
    exact hn
  rw [← hP]
  exact ⟨n.val, hnP, rfl⟩

/-- The original point has a derived, rather than assumed, singular coordinate. -/
theorem exists_point_coordinate : ∃ i : Fin 5, d.pointVector = Starred.pointWord i := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := d.exists_sylow_L_le_T
  apply Starred.sylow_fixed_pointWord (P.mapSurjective d.fiveAction_surjective)
    d.pointVector d.pointVector_ne_zero
  rintro a ⟨l, hl, rfl⟩
  exact (d.mem_G₁_iff_fixes_pointVector l).mp
    (d.setup.T_normalizes_point (hP (mem_map_of_mem D.L.subtype hl)))

noncomputable def pointIndex : Fin 5 := d.exists_point_coordinate.choose

theorem pointVector_eq_pointWord : d.pointVector = Starred.pointWord d.pointIndex :=
  d.exists_point_coordinate.choose_spec

theorem pointVector_singular : BinaryPermutation.FiveGeometry.form d.pointVector = 0 := by
  rw [d.pointVector_eq_pointWord]
  exact Starred.pointWord_singular _

/-- This compatibility retains the original quotient marking and its coordinates. -/
theorem mem_G₁_iff_fixes_pointIndex (l : D.L) :
    (l : G) ∈ D.G₁ ↔ (d.fiveAction l).val d.pointIndex = d.pointIndex := by
  rw [d.mem_G₁_iff_fixes_pointVector, d.pointVector_eq_pointWord, Starred.pointWord_action]
  exact Starred.pointWord_injective.eq_iff

/-- The relative normalizer maps onto the full, correctly marked A₄. -/
theorem normalizer_fiveAction :
    ((D.L ⊓ D.G₁).subgroupOf D.L).map d.fiveAction =
      MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex := by
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact (d.mem_G₁_iff_fixes_pointIndex l).mp hl.2
  · intro ha
    obtain ⟨l, rfl⟩ := d.fiveAction_surjective a
    exact ⟨l, ⟨l.property, (d.mem_G₁_iff_fixes_pointIndex l).mpr ha⟩, rfl⟩

/-- Images under the coordinates agree with the literal star quotient. -/
theorem fiveAction_map (A : Subgroup G) (hA : A ≤ D.L) :
    (A.subgroupOf D.L).map d.fiveAction =
      ((D.star A).subgroupOf (D.star D.L)).map d.model.toMonoidHom := by
  have hs : (A.subgroupOf D.L).map (starProjection D) =
      (D.star A).subgroupOf (D.star D.L) := by
    apply map_injective (D.star D.L).subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le (binary_star_mono hA)]
    exact binaryStarRestriction_map D.L A le_sup_left hA
  change (A.subgroupOf D.L).map (d.model.toMonoidHom.comp (starProjection D)) = _
  rw [← map_map, hs]

/-- Stabilizer identification inside the actual starred L. -/
theorem star_normalizer_model :
    ((D.star (D.L ⊓ D.G₁)).subgroupOf (D.star D.L)).map d.model.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex := by
  rw [← d.fiveAction_map _ inf_le_left, d.normalizer_fiveAction]

/-- The original conjugator moves the derived singular coordinate. -/
theorem g_moves_pointIndex :
    (d.fiveAction ⟨g, d.g_mem⟩).val d.pointIndex ≠ d.pointIndex :=
  fun h => d.g_not_normalizes ((d.mem_G₁_iff_fixes_pointIndex _).mpr h)

/-- The image of the original two-residual is the full Borel, not its two-core. -/
theorem local_fiveAction :
    (D.L₁.subgroupOf D.L).map d.fiveAction =
      MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex := by
  let N := D.L ⊓ D.G₁
  let N' := N.subgroupOf D.L
  let e : N' ≃* N := subgroupOfEquivOfLe inf_le_left
  have hr : ((pResidual 2 N').map N'.subtype).map D.L.subtype = D.L₁ := by
    calc
      _ = ((pResidual 2 N').map e.toMonoidHom).map N.subtype := by
        rw [map_map, map_map]
        rfl
      _ = _ := by rw [map_pResidual]; rfl
  have hl : (pResidual 2 N').map N'.subtype = D.L₁.subgroupOf D.L := by
    apply map_injective D.L.subtype_injective
    rw [hr, map_subgroupOf_eq_of_le (show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left)]
  rw [← hl, map_embedded_pResidual]
  have hn : N'.map d.fiveAction = MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex :=
    d.normalizer_fiveAction
  rw [hn, Starred.stabilizer_twoResidual, ← MonoidHom.range_eq_map, range_subtype]

/-- The actual starred local two-residual has the derived point-stabilizer marking. -/
theorem star_local_model :
    ((D.star D.L₁).subgroupOf (D.star D.L)).map d.model.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) d.pointIndex := by
  rw [← d.fiveAction_map D.L₁ (show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left), d.local_fiveAction]

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
