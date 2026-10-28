module

public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.EightPointLine.Model
public import Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry
public import Theory.SpecificGroups.BinaryLinear.FourParabolicAction.Geometry
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality
public import Theory.Alternating.Aut

/-!
# Sylow-fixed vectors for the orthogonal plane parabolic

Four even binary-tree permutations force a representative of a Sylow-fixed
vector to be constant on each of the two four-point blocks. The entire
four-block stabilizer therefore fixes its deleted class. Sylow conjugacy
inside this stabilizer gives the same assertion for each of its Sylow groups.

To use an independently chosen alternating-group marking, first move the
supplied two-plane to the standard plane. The checked exceptional equivalence
identifies its parabolic with the even four-block stabilizer. Every automorphism
of A₈ is induced by a permutation, so comparing the two genuine equivalences
also transports the module action. No agreement between model markings is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.1–2,
printed pp.83–84, and the orthogonal exclusion in 15.3.24, printed p.1129.
The exceptional equivalence and its attribution are retained in
`Theory.SpecificGroups.SymmetricEight.FourBlockParabolic.Geometry`.
-/

public section

open Subgroup BinaryPermutation
open Theory.SpecificGroups.SymmetricEight
open A6ShadowTwoLocals
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.EightPoint
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Orthogonal.Parabolic

/-- Any independently chosen A₈ marking takes a binary plane parabolic
to a permutation conjugate of the actual four-block stabilizer. -/
private theorem exists_four_block_marking {K : Type*} [Group K]
    (e : K ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (m : K ≃* alternatingGroup (Fin 8))
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hW : Module.finrank (ZMod 2) W = 2) :
    ∃ r : Equiv.Perm (Fin 8), ∀ k : K,
      e k ∈ BinaryLinear.parabolic W ↔
        r * (m k).val * r⁻¹ ∈ fourStabilizer := by
  obtain ⟨g, hg⟩ := BinaryLinear.FourParabolicAction.exists_linearEquiv_map_eq W
    FourBlockParabolic.plane (hW.trans FourBlockParabolic.plane_finrank.symm)
  let m' := (e.trans (MulAut.conj g)).trans FourBlockParabolic.equiv.symm
  obtain ⟨r, hr⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    8 (by decide) (by decide)).surjective (m.symm.trans m')
  have hm (k : K) : (m' k).val = r * (m k).val * r⁻¹ := by
    have hh := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) => (f (m k)).val) hr
    change r * (m k).val * r⁻¹ = (m' (m.symm (m k))).val at hh
    simpa only [MulEquiv.symm_apply_apply] using hh.symm
  refine ⟨r, fun k => ?_⟩
  rw [← hm]
  have hc (a : alternatingGroup (Fin 8)) :
      FourBlockParabolic.equiv a ∈ BinaryLinear.parabolic FourBlockParabolic.plane ↔
        a.val ∈ fourStabilizer := by
    change a ∈ (BinaryLinear.parabolic FourBlockParabolic.plane).comap
      FourBlockParabolic.equiv.toMonoidHom ↔ _
    rw [FourBlockParabolic.parabolic_comap]
    rfl
  rw [← hc]
  change e k ∈ BinaryLinear.parabolic W ↔
    FourBlockParabolic.equiv (FourBlockParabolic.equiv.symm (MulAut.conj g (e k))) ∈ _
  rw [MulEquiv.apply_symm_apply, ← hg,
    ← BinaryLinear.InvariantNodeActions.inner_map_parabolic,
    Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem binary_relation (a b c d : ZMod 2) :
    (a = b ↔ c = d) ↔ a - c = b - d := by
  revert a b c d
  decide

private theorem two_coordinates (w : Full (Fin 8))
    (h : ∀ i : Fin 64, deletedRepresentation (Fin 8) (twoWord i)
      ((constants (Fin 8)).mkQ w) = (constants (Fin 8)).mkQ w) :
    ∀ i : Fin 8, w i = if i.val < 4 then w 0 else w 4 := by
  have ha := (deleted_fixed_iff_of_fixed_point (twoWord 1) w 4 (by decide)).mp (h 1)
  have hb := (deleted_fixed_iff_of_fixed_point (twoWord 8) w 4 (by decide)).mp (h 8)
  have hc := (deleted_fixed_iff_of_fixed_point (twoWord 6) w 0 (by decide)).mp (h 6)
  have hd := (deleted_fixed_iff_of_fixed_point (twoWord 16) w 0 (by decide)).mp (h 16)
  have h01 := congrFun ha 0
  have h23 := congrFun ha 2
  have h02 := congrFun hb 0
  have h45 := congrFun hc 4
  have h67 := congrFun hc 6
  have h46 := congrFun hd 4
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 2 = w 0 at h02
  change w 5 = w 4 at h45
  change w 7 = w 6 at h67
  change w 6 = w 4 at h46
  intro i
  fin_cases i <;> simp_all

/-- Every even-tree fixed natural vector is fixed by the entire four-block stabilizer. -/
private theorem two_fixed_four (v : natural (Fin 8))
    (h : ∀ a ∈ twoGroup, naturalRepresentation (Fin 8) a.val v = v) :
    ∀ g ∈ fourStabilizer, naturalRepresentation (Fin 8) g v = v := by
  obtain ⟨w, _, hw⟩ := v.property
  have hcoords := two_coordinates w (fun i => by
    have hi := congrArg Subtype.val (h (twoElement i) ((mem_twoGroup _).mpr ⟨i, rfl⟩))
    simpa only [naturalRepresentation_apply, ← hw, twoElement] using hi)
  intro g hg
  apply Subtype.ext
  change deletedRepresentation (Fin 8) g v.val = v.val
  rw [← hw, deleted_fixed_iff]
  refine ⟨w (g.symm 0) - w 0, fun i => ?_⟩
  apply (binary_relation _ _ _ _).mp
  have hg' := fourStabilizer.inv_mem hg
  have hr (i j : Fin 8) : (w (g.symm i) = w (g.symm j)) ↔ w i = w j := by
    by_cases he : w 0 = w 4
    · rw [hcoords (g.symm i), hcoords (g.symm j), hcoords i, hcoords j, he]
      simp
    · have hrel (a b : Fin 8) : w a = w b ↔ a.val / 4 = b.val / 4 := by
        rw [hcoords a, hcoords b]
        fin_cases a <;> fin_cases b <;> simp [he, Ne.symm he]
      rw [hrel, hrel]
      exact hg' i j
  exact hr i 0


private theorem action_injective (r : S8) :
    Function.Injective (naturalRepresentation (Fin 8) r) := by
  intro x y h
  have := congrArg (naturalRepresentation (Fin 8) r⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using this

private theorem conjugate_apply (r g : S8) (v : natural (Fin 8)) :
    naturalRepresentation (Fin 8) (r * g * r⁻¹)
      (naturalRepresentation (Fin 8) r v) =
      naturalRepresentation (Fin 8) r (naturalRepresentation (Fin 8) g v) := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right,
    map_mul, Module.End.mul_apply]

/-- The even four-block parabolic fixes every vector fixed by one of
its Sylow two-subgroups. The Sylow group is a Sylow group of A₈ itself. -/
private theorem four_fixed_of_sylow (Q : Sylow 2 Alt)
    (hQ : (Q : Subgroup Alt) ≤ fourStabilizer.subgroupOf Alt)
    (v : natural (Fin 8))
    (hv : ∀ a ∈ (Q : Subgroup Alt), naturalRepresentation (Fin 8) a.val v = v) :
    ∀ a ∈ fourStabilizer.subgroupOf Alt, naturalRepresentation (Fin 8) a.val v = v := by
  let P := fourStabilizer.subgroupOf Alt
  have ht : (twoSylow : Subgroup Alt) ≤ P :=
    fun _ h => treeGroup_le_flagStabilizer h |>.2
  obtain ⟨r, hr⟩ := MulAction.exists_smul_eq P (Q.subtype hQ) (twoSylow.subtype ht)
  rw [Sylow.smul_subtype] at hr
  have hr' : (r.val • Q : Sylow 2 Alt) = twoSylow := Sylow.subtype_injective hr
  have hmap : (Q : Subgroup Alt).map (MulAut.conj r.val).toMonoidHom = twoGroup :=
    congrArg Sylow.toSubgroup hr'
  have hfixed : ∀ a ∈ twoGroup, naturalRepresentation (Fin 8) a.val
      (naturalRepresentation (Fin 8) r.val.val v) =
        naturalRepresentation (Fin 8) r.val.val v := by
    intro a ha
    rw [← hmap] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    change naturalRepresentation (Fin 8) (r.val.val * b.val * r.val.val⁻¹)
      (naturalRepresentation (Fin 8) r.val.val v) = _
    rw [conjugate_apply, hv b hb]
  intro a ha
  apply action_injective r.val.val
  rw [← conjugate_apply]
  exact two_fixed_four _ hfixed _
    (fourStabilizer.mul_mem (fourStabilizer.mul_mem r.property ha)
      (fourStabilizer.inv_mem r.property))


/-- In any actual alternating-group marking, the binary plane parabolic
fixes every natural-module vector fixed by its Sylow two-subgroup. -/
theorem plane_fixed_of_sylow {K : Type*} [Group K] [Finite K]
    (e : K ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (m : K ≃* alternatingGroup (Fin 8))
    (W : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hW : Module.finrank (ZMod 2) W = 2)
    (S : Sylow 2 K) (hS : ∀ s ∈ (S : Subgroup K), e s ∈ BinaryLinear.parabolic W)
    (v : natural (Fin 8))
    (hv : ∀ s ∈ (S : Subgroup K), naturalRepresentation (Fin 8) (m s).val v = v) :
    ∀ k : K, e k ∈ BinaryLinear.parabolic W →
      naturalRepresentation (Fin 8) (m k).val v = v := by
  obtain ⟨r, hr⟩ := exists_four_block_marking e m W hW
  let m' : K ≃* alternatingGroup (Fin 8) := m.trans (MulAut.conjNormal r)
  let Q := S.mapSurjective (f := m'.toMonoidHom) m'.surjective
  have hQ : (Q : Subgroup Alt) ≤ fourStabilizer.subgroupOf Alt := by
    rintro a ⟨s, hs, rfl⟩
    exact (hr s).mp (hS s hs)
  have hfix : ∀ a ∈ (Q : Subgroup Alt), naturalRepresentation (Fin 8) a.val
      (naturalRepresentation (Fin 8) r v) = naturalRepresentation (Fin 8) r v := by
    rintro a ⟨s, hs, rfl⟩
    change naturalRepresentation (Fin 8) (r * (m s).val * r⁻¹)
      (naturalRepresentation (Fin 8) r v) = _
    rw [conjugate_apply, hv s hs]
  intro k hk
  apply action_injective r
  rw [← conjugate_apply]
  exact four_fixed_of_sylow Q hQ _ hfix (m' k) ((hr k).mp hk)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Orthogonal.Parabolic

end
