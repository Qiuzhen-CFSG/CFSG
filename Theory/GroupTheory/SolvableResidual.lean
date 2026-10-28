module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.Order.Minimal

/-!
# The solvable residual of a finite group

The solvable residual is the intersection of the derived series. In a finite
group the series stabilizes, so this intersection is perfect and its quotient
is solvable. Every perfect subgroup lies in the residual. Derived-series
functoriality gives transport under surjective homomorphisms and monotonicity
for subgroups of a common ambient group.

This is the terminal derived subgroup, not the solvable radical.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition A.3.3(3)–(4), pp. 42–43 (1 March 2004 manuscript).
-/

@[expose] public section
namespace Subgroup
variable (G : Type*) [Group G]

/-- The intersection of the derived series, also called the terminal derived subgroup. -/
def solvableResidual : Subgroup G := ⨅ n : ℕ, derivedSeries G n

/-- The solvable residual is characteristic, even without finiteness. -/
instance solvableResidual_characteristic : (solvableResidual G).Characteristic := by
  unfold solvableResidual
  infer_instance

variable {G} {D : Type*} [Group D]

/-- The residual lies in every term of the derived series. -/
theorem solvableResidual_le_derivedSeries (n : ℕ) :
    solvableResidual G ≤ derivedSeries G n := iInf_le _ n

/-- Every perfect subgroup lies in the solvable residual. -/
theorem le_solvableResidual_of_isPerfect (H : Subgroup G) [Group.IsPerfect H] :
    H ≤ solvableResidual G := by
  apply le_iInf
  intro n
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← H.commutator_eq_self]
    exact commutator_mono ih ih

/-- Homomorphisms carry the residual into the residual. -/
theorem map_solvableResidual_le (f : G →* D) :
    (solvableResidual G).map f ≤ solvableResidual D := by
  apply le_iInf
  intro n
  exact (map_mono (solvableResidual_le_derivedSeries n)).trans
    (map_derivedSeries_le_derivedSeries f n)

/-- In a finite group the residual is a term of the derived series. -/
theorem exists_derivedSeries_eq_solvableResidual [Finite G] :
    ∃ n : ℕ, derivedSeries G n = solvableResidual G := by
  obtain ⟨H, ⟨n, rfl⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun K : Subgroup G => ∃ n : ℕ, derivedSeries G n = K)
    ⟨⊤, 0, derivedSeries_zero G⟩
  have hp : Group.IsPerfect (derivedSeries G n) := by
    rw [isPerfect_iff]
    exact le_antisymm (derivedSeries G n).commutator_le_self
      (hmin ⟨n + 1, derivedSeries_succ G n⟩ (derivedSeries G n).commutator_le_self)
  exact ⟨n, le_antisymm (le_solvableResidual_of_isPerfect _) (solvableResidual_le_derivedSeries n)⟩

/-- The residual of a finite group is perfect. -/
instance solvableResidual_isPerfect [Finite G] : Group.IsPerfect (solvableResidual G) := by
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := G)
  rw [isPerfect_iff]
  apply le_antisymm (solvableResidual G).commutator_le_self
  simpa only [derivedSeries_succ, hn] using (solvableResidual_le_derivedSeries (G := G) (n + 1))

/-- Surjections of finite groups carry the residual onto the residual. -/
theorem map_solvableResidual_eq [Finite G] (f : G →* D) (hf : Function.Surjective f) :
    (solvableResidual G).map f = solvableResidual D := by
  apply le_antisymm (map_solvableResidual_le f)
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := G)
  rw [← hn, map_derivedSeries_eq hf]
  exact solvableResidual_le_derivedSeries n

/-- The quotient of a finite group by its residual is solvable. -/
instance solvableResidual_quotient_isSolvable [Finite G] :
    Group.IsSolvable (G ⧸ solvableResidual G) := by
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := G)
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective (solvableResidual G)), hn]
  exact (map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])

/-- A solvable group has trivial residual. -/
theorem solvableResidual_eq_bot [Group.IsSolvable G] : solvableResidual G = ⊥ := by
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := G)
  exact le_bot_iff.mp (hn ▸ solvableResidual_le_derivedSeries n)

/-- The residual lies in every normal subgroup with solvable quotient. -/
theorem solvableResidual_le_of_solvable_quotient
    (N : Subgroup G) [N.Normal] [Group.IsSolvable (G ⧸ N)] : solvableResidual G ≤ N := by
  have h := map_solvableResidual_le (QuotientGroup.mk' N)
  rw [solvableResidual_eq_bot (G := G ⧸ N), le_bot_iff, map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  exact h

/-- A perfect subgroup contained in a subgroup lies in its solvable residual. -/
theorem le_map_solvableResidual_of_isPerfect (P H : Subgroup G)
    [Group.IsPerfect P] (h : P ≤ H) : P ≤ (solvableResidual H).map H.subtype := by
  let : Group.IsPerfect (P.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe h).symm.toMonoidHom)
      (subgroupOfEquivOfLe h).symm.surjective
  simpa only [map_subgroupOf_eq_of_le h] using
    (map_mono (f := H.subtype) (le_solvableResidual_of_isPerfect (P.subgroupOf H)))

/-- Monotonicity of subgroup residuals inside a common ambient group. -/
theorem map_solvableResidual_mono {H K : Subgroup G} (h : H ≤ K) :
    (solvableResidual H).map H.subtype ≤ (solvableResidual K).map K.subtype := by
  have hm := map_mono (f := K.subtype) (map_solvableResidual_le (inclusion h))
  simpa only [map_map, subtype_comp_inclusion] using hm

/-- The finite derived series is eventually equal to the solvable residual. -/
theorem exists_derivedSeries_stable [Finite G] :
    ∃ n : ℕ, ∀ m ≥ n, derivedSeries G m = solvableResidual G := by
  obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := G)
  exact ⟨n, fun m hm => le_antisymm
    ((derivedSeries_antitone G hm).trans hn.le) (solvableResidual_le_derivedSeries m)⟩

/-- A perfect group is its own solvable residual. -/
@[simp] theorem solvableResidual_eq_top [Group.IsPerfect G] : solvableResidual G = ⊤ := by
  exact top_unique (le_solvableResidual_of_isPerfect ⊤)

/-- The residual of a preimage maps onto the residual of the subgroup. -/
theorem map_solvableResidual_comap [Finite G] (f : G →* D)
    (hf : Function.Surjective f) (K : Subgroup D) :
    ((solvableResidual (K.comap f)).map (K.comap f).subtype).map f =
      (solvableResidual K).map K.subtype := by
  have he := map_solvableResidual_eq (f.subgroupComap K)
    (f.subgroupComap_surjective_of_surjective K hf)
  have hm := congrArg (map K.subtype) he
  have hcomp : K.subtype.comp (f.subgroupComap K) = f.comp (K.comap f).subtype := by
    ext x
    rfl
  simpa only [map_map, hcomp] using hm

end Subgroup
