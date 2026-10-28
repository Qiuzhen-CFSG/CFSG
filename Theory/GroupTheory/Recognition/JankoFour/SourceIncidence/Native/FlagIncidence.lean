module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarOrbit
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneCardinality
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.Residue

/-!
# Native flags forced by the literal intersection index

The existing checked sextet-stabilizer forest covers all trios. Each of its
three nonincident roots has sixteen distinct recorded orbit members, whereas
an incident orbit has at most the fifteen synthemes. Thus index fifteen
forces incidence, and all incident trios come from the fourth root. Its
transporters and the original sextet conjugators prove flag transitivity.
No new forest or exhaustive enumeration is introduced.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), §§3,5, pp.593–600,
DOI 10.1007/BF01232280. This identifies the actual point-residue flags from
the earlier algebraic subgroup markings.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeFlags
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open SourceCycleBase.Native
open scoped Pointwise Matrix

private theorem orbit_card (l : Line) (π : Plane) :
    Nat.card (MulAction.orbit (sextetStabilizer π) l) =
      (trioStabilizer l).relIndex (sextetStabilizer π) := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (sextetStabilizer π) l)]
  change (MulAction.stabilizer (sextetStabilizer π) l).index = _
  congr 1
  ext g
  exact ⟨fun hg => congrArg Trio.parts hg, fun hg => line_parts_injective hg⟩

private def samples : Fin 3 → Fin 16 → Fin 3795 :=
  ![![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
    ![17,49,81,94,126,152,182,211,260,288,318,333,360,376,378,380],
    ![19,20,23,24,26,29,45,48,52,53,56,57,77,78,83,84]]

private theorem samples_root (r : Fin 3) (i : Fin 16) :
    (FarOrbit.row (samples r i)).root = r.castLE (by decide) := by
  revert r i; decide +kernel

private theorem samples_injective (r : Fin 3) : Function.Injective (samples r) := by
  revert r; decide +kernel

private theorem root_orbit_large (r : Fin 4) (hr : r ≠ 3) :
    16 ≤ Nat.card (MulAction.orbit (sextetStabilizer standardSextet) (FarOrbit.rootLine r)) := by
  let r' : Fin 3 := ⟨r.val,by have := r.isLt; have hh : r.val ≠ 3 := fun hh => hr (Fin.ext hh); omega⟩
  let f : Fin 16 → MulAction.orbit (sextetStabilizer standardSextet) (FarOrbit.rootLine r) :=
    fun i => ⟨FarOrbit.entry (samples r' i),by
      refine ⟨(FarOrbit.exists_transport (samples r' i)).choose,?_⟩
      have he : (FarOrbit.row (samples r' i)).root = r := (samples_root r' i).trans (Fin.ext rfl)
      change ((FarOrbit.exists_transport (samples r' i)).choose : M24) • FarOrbit.rootLine r = _
      exact congrArg (fun r => ((FarOrbit.exists_transport (samples r' i)).choose : M24) • FarOrbit.rootLine r) he.symm⟩
  have hf : Function.Injective f := by
    intro i j he
    exact samples_injective r' (FarOrbit.entry_injective (congrArg Subtype.val he))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem orbit_card_smul (g : M24) (l : Line) (π : Plane) :
    Nat.card (MulAction.orbit (sextetStabilizer π) l) =
      Nat.card (MulAction.orbit (sextetStabilizer (g • π)) (g • l)) := by
  let tr (g : M24) (l : Line) (π : Plane)
      (m : MulAction.orbit (sextetStabilizer π) l) :
      MulAction.orbit (sextetStabilizer (g • π)) (g • l) := ⟨g • m.val,by
    obtain ⟨k,hk⟩ := m.property
    let k' : sextetStabilizer (g • π) := ⟨g * (k : M24) * g⁻¹,by
      change (g * (k : M24) * g⁻¹) • (g • π.parts) = g • π.parts
      rw [mul_smul,mul_smul,inv_smul_smul,k.property]⟩
    refine ⟨k',?_⟩
    change (g * (k : M24) * g⁻¹) • (g • l) = g • m.val
    rw [mul_smul,mul_smul,inv_smul_smul]
    exact congrArg (g • ·) hk⟩
  apply Nat.card_congr
  exact {
    toFun := tr g l π
    invFun := fun m => ⟨g⁻¹ • m.val,by
      obtain ⟨k,hk⟩ := m.property
      let k' : sextetStabilizer π := ⟨g⁻¹*(k : M24)*g,by
        have hp : (k : M24) • (g • π.parts) = g • π.parts := k.property
        change (g⁻¹*(k : M24)*g) • π.parts = π.parts
        rw [mul_smul,mul_smul,hp,inv_smul_smul]⟩
      refine ⟨k',?_⟩
      change (g⁻¹*(k : M24)*g) • l = g⁻¹ • m.val
      rw [mul_smul,mul_smul]
      exact congrArg (g⁻¹ • ·) hk⟩
    left_inv := fun m => Subtype.ext (inv_smul_smul g m.val)
    right_inv := fun m => Subtype.ext (smul_inv_smul g m.val) }

/-- The original index fifteen forces genuine trio–sextet incidence.
The existing exhaustive forest excludes the three nonincident roots, each
of which already has sixteen distinct checked orbit members. -/
theorem incident_of_index (l : Line) (π : Plane)
    (hi : (trioStabilizer l).relIndex (sextetStabilizer π) = 15) : Incident l π := by
  obtain ⟨g,hg⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
  have hg' : g • standardSextet = π := plane_parts_injective hg
  obtain ⟨i,hi'⟩ := FarOrbit.entry_surjective (g⁻¹ • l)
  have hcard : Nat.card (MulAction.orbit (sextetStabilizer standardSextet) (FarOrbit.entry i)) = 15 := by
    rw [hi',orbit_card_smul g _ standardSextet,hg',smul_inv_smul,orbit_card,hi]
  let k := (FarOrbit.exists_transport i).choose
  have hk : (k : M24) • standardSextet = standardSextet := plane_parts_injective k.property
  have hc : Nat.card (MulAction.orbit (sextetStabilizer standardSextet)
      (FarOrbit.rootLine (FarOrbit.row i).root)) = 15 := by
    rw [orbit_card_smul (k : M24),hk]
    exact hcard
  have hr : (FarOrbit.row i).root = 3 := by
    by_contra hn
    have hh := root_orbit_large _ hn
    omega
  have hroot : Incident (FarOrbit.rootLine (FarOrbit.row i).root) standardSextet := by
    rw [hr]; exact FarOrbit.seed_three_incident_standard
  have he : Incident (FarOrbit.entry i) standardSextet :=
    incident_transport (k : M24) rfl k.property.symm hroot
  have hh : Incident (g • FarOrbit.entry i) π := incident_transport g rfl hg.symm he
  have hl : g • FarOrbit.entry i = l := by rw [hi',smul_inv_smul]
  rwa [hl] at hh

private theorem incident_orbit_bound (l : Line) (π : Plane) (hl : Incident l π) :
    Nat.card (MulAction.orbit (sextetStabilizer π) l) ≤ 15 := by
  classical
  let e : Fin 6 ≃ {A // A ∈ π.parts} :=
    (Fintype.equivFinOfCardEq (by simpa using π.card)).symm
  have hc : Nat.card {m : Line // Incident m π} = 15 := by
    rw [Nat.card_congr (residueEquiv π e),Nat.card_eq_fintype_card]
    decide
  rw [←hc]
  let f : MulAction.orbit (sextetStabilizer π) l → {m : Line // Incident m π} :=
    fun m => ⟨m.val,by
      obtain ⟨k,hk⟩ := m.property
      exact incident_transport (k : M24) (congrArg Trio.parts hk).symm k.property.symm hl⟩
  apply Nat.card_le_card_of_injective f
  intro x y he
  apply Subtype.ext
  exact congrArg (fun q : {m : Line // Incident m π} => q.val) he

private theorem incident_root (i : Fin 3795) (hi : Incident (FarOrbit.entry i) standardSextet) :
    (FarOrbit.row i).root = 3 := by
  have hc := incident_orbit_bound _ _ hi
  let k := (FarOrbit.exists_transport i).choose
  have hk : (k : M24) • standardSextet = standardSextet := plane_parts_injective k.property
  have he := orbit_card_smul (k : M24) (FarOrbit.rootLine (FarOrbit.row i).root) standardSextet
  rw [hk] at he
  by_contra hn
  have hb := root_orbit_large _ hn
  change Nat.card (MulAction.orbit (sextetStabilizer standardSextet) (FarOrbit.rootLine (FarOrbit.row i).root)) =
    Nat.card (MulAction.orbit (sextetStabilizer standardSextet) (FarOrbit.entry i)) at he
  omega

private theorem standard_incident_transitive (l m : Line)
    (hl : Incident l standardSextet) (hm : Incident m standardSextet) :
    ∃ k : sextetStabilizer standardSextet, (k : M24) • l = m := by
  obtain ⟨i,rfl⟩ := FarOrbit.entry_surjective l
  obtain ⟨j,rfl⟩ := FarOrbit.entry_surjective m
  let a := (FarOrbit.exists_transport i).choose
  let b := (FarOrbit.exists_transport j).choose
  have hi := incident_root i hl
  have hj := incident_root j hm
  refine ⟨b*a⁻¹,?_⟩
  change ((b : M24)*(a : M24)⁻¹) • ((a : M24) • FarOrbit.rootLine (FarOrbit.row i).root) =
    (b : M24) • FarOrbit.rootLine (FarOrbit.row j).root
  simp only [hi,hj,mul_smul,inv_smul_smul]

/-- Actual native flags are conjugate under a single M₂₄ permutation. -/
theorem flag_transitive (l m : Line) (π σ : Plane) (hl : Incident l π) (hm : Incident m σ) :
    ∃ g : M24, g • l.parts = m.parts ∧ g • π.parts = σ.parts := by
  obtain ⟨a,ha⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator π
  obtain ⟨b,hb⟩ := MathieuCode.SextetLayers.CoordinateTransport.exists_sextet_conjugator σ
  have hl' : Incident (a⁻¹ • l) standardSextet :=
    incident_transport a⁻¹ rfl (by rw [←ha,inv_smul_smul]) hl
  have hm' : Incident (b⁻¹ • m) standardSextet :=
    incident_transport b⁻¹ rfl (by rw [←hb,inv_smul_smul]) hm
  obtain ⟨k,hk⟩ := standard_incident_transitive _ _ hl' hm'
  refine ⟨b*(k : M24)*a⁻¹,?_,?_⟩
  · have hh := congrArg Trio.parts hk
    change (k : M24) • (a⁻¹ • l.parts) = b⁻¹ • m.parts at hh
    rw [mul_smul,mul_smul,hh,smul_inv_smul]
  · rw [←ha,mul_smul,mul_smul,inv_smul_smul,k.property,hb]
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeFlags
