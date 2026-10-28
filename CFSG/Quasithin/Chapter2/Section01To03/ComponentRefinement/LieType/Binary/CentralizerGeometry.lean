module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The binary transvection's centralizer flag

A nonzero rank-one transvection fixes a hyperplane pointwise and has an image
line inside that hyperplane. Over the field of order two, stabilizing this line
and hyperplane forces both the defining vector and the defining functional to
be fixed. Their common stabilizer is therefore exactly the transvection's
centralizer. We prove this identity in the actual transported PSL action,
including the dimensions and incidence of the two subspaces.

In the local setup, N_S(L) fixes the involution projection by uniqueness. Its
centralizer flag is invariant under N_S(L), and adjoining all of S to its
stabilizer stays inside M. For degrees four and five these are the flags of
types {1,3} and {1,4} in the graph-action cases of Aschbacher–Smith 2.3.9(7),
combined manuscript of 1 March 2004, printed pp.525–526.

The rank-one coordinates are explicit inputs here. Constructing them from
Sylow centrality, analyzing the other parabolics and bounding the proper
overgroups of this centralizer remain separate obligations.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup
variable {n : ℕ}
private theorem binary_scalar {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem fixes_of_stabilizes_line (g : BinaryLinear.GL (Vector n))
    {w : Vector n} (hw : w ≠ 0)
    (hg : g ∈ BinaryLinear.parabolic (Submodule.span (ZMod 2) {w})) : g w = w := by
  have hgw := (hg w).mpr (Submodule.subset_span (Set.mem_singleton w))
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hgw
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at ha
    exact hw (g.map_eq_zero_iff.mp ha.symm)
  simpa [binary_scalar ha0] using ha.symm

private theorem fixes_functional_of_stabilizes_ker (g : BinaryLinear.GL (Vector n))
    (f : Vector n →ₗ[ZMod 2] ZMod 2)
    (hg : g ∈ BinaryLinear.parabolic f.ker) : ∀ v, f (g v) = f v := by
  intro v
  have hzero : f (g v) = 0 ↔ f v = 0 := hg v
  by_cases hv : f v = 0
  · exact (hzero.mpr hv).trans hv.symm
  · rw [binary_scalar hv, binary_scalar (mt hzero.mp hv)]

private theorem centralizer_transvection {w : Vector n} (hw : w ≠ 0)
    {f : Vector n →ₗ[ZMod 2] ZMod 2} (hf : f ≠ 0) (hfw : f w = 0) :
    centralizer ({BinaryLinear.transvection w f hfw} : Set (BinaryLinear.GL (Vector n))) =
      BinaryLinear.parabolic (Submodule.span (ZMod 2) {w}) ⊓
        BinaryLinear.parabolic f.ker := by
  ext g
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hc (v : Vector n) : f (g v) • w = f v • g w := by
      have hv := congrArg (fun a : BinaryLinear.GL (Vector n) => a v) hg
      change g (v + f v • w) = g v + f (g v) • w at hv
      simpa only [map_add, map_smul, add_right_inj] using hv.symm
    obtain ⟨v₀, hv₀⟩ := LinearMap.surjective hf (1 : ZMod 2)
    have hh := hc v₀
    rw [hv₀, one_smul] at hh
    have hg0 : f (g v₀) ≠ 0 := by
      intro hz
      rw [hz, zero_smul] at hh
      exact hw (g.map_eq_zero_iff.mp hh.symm)
    have hgw : g w = w := by simpa [binary_scalar hg0] using hh.symm
    have hfg (v : Vector n) : f (g v) = f v := by
      have hv := hc v
      rw [hgw] at hv
      exact (smul_left_injective (ZMod 2) hw) hv
    refine ⟨?_, ?_⟩
    · intro v
      constructor
      · rintro hv
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
        apply Submodule.mem_span_singleton.mpr
        exact ⟨a, g.injective (by rw [map_smul, hgw]; exact ha)⟩
      · rintro hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
        rw [map_smul, hgw]
        exact Submodule.smul_mem _ a (Submodule.subset_span (Set.mem_singleton w))
    · intro v
      change f (g v) = 0 ↔ f v = 0
      rw [hfg]
  · rintro ⟨hl, hk⟩
    have hgw := fixes_of_stabilizes_line g hw hl
    have hfg := fixes_functional_of_stabilizes_ker g f hk
    apply LinearEquiv.ext
    intro v
    change g (v + f v • w) = g v + f (g v) • w
    rw [map_add, map_smul, hgw, hfg]

variable {G : Type*} [Group G] {L : Subgroup G} [NeZero n]

/-- Actual rank-one coordinates for the given component element. The action
is multiplication in the supplied PSL model, not an abstract family label. -/
structure TransvectionCoordinates (e : L ≃* PSL n) (t : L) where
  vector : Vector n
  functional : Vector n →ₗ[ZMod 2] ZMod 2
  vector_ne_zero : vector ≠ 0
  functional_ne_zero : functional ≠ 0
  incident : functional vector = 0
  action : ∀ v, linearModel e t v = v + functional v • vector

variable {e : L ≃* PSL n} {t : L}

noncomputable def TransvectionCoordinates.line (c : TransvectionCoordinates e t) : Space n :=
  Submodule.span (ZMod 2) {c.vector}

def TransvectionCoordinates.hyperplane (c : TransvectionCoordinates e t) : Space n :=
  c.functional.ker

theorem TransvectionCoordinates.line_finrank (c : TransvectionCoordinates e t) :
    Module.finrank (ZMod 2) c.line = 1 := finrank_span_singleton c.vector_ne_zero

theorem TransvectionCoordinates.hyperplane_finrank (c : TransvectionCoordinates e t) :
    Module.finrank (ZMod 2) c.hyperplane + 1 = n := by
  change Module.finrank (ZMod 2) c.functional.ker + 1 = n
  exact (Module.Dual.finrank_ker_add_one_of_ne_zero c.functional_ne_zero).trans
    (Module.finrank_fin_fun (ZMod 2))

theorem TransvectionCoordinates.line_le_hyperplane (c : TransvectionCoordinates e t) :
    c.line ≤ c.hyperplane := by
  apply Submodule.span_le.mpr
  rintro v rfl
  exact c.incident

/-- The incident image-line/fixed-hyperplane flag of the transvection. -/
noncomputable def TransvectionCoordinates.flag (c : TransvectionCoordinates e t)
    (hn : 2 ≤ n) : Flag n where
  spaces := {c.line, c.hyperplane}
  nonempty := by simp
  proper := by
    intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · refine ⟨?_, ?_⟩
      · exact mt Submodule.span_singleton_eq_bot.mp c.vector_ne_zero
      · intro he
        have hh := c.line_finrank
        rw [he, finrank_top, Module.finrank_fin_fun] at hh
        omega
    · refine ⟨?_, ?_⟩
      · intro he
        have hh := c.hyperplane_finrank
        rw [he, finrank_bot] at hh
        omega
      · exact mt LinearMap.ker_eq_top.mp c.functional_ne_zero
  chain := by
    intro W hW W' hW'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW hW'
    rcases hW with rfl | rfl <;> rcases hW' with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl c.line_le_hyperplane
    · exact Or.inr c.line_le_hyperplane
    · exact Or.inl le_rfl

theorem TransvectionCoordinates.flag_types (c : TransvectionCoordinates e t)
    (hn : 2 ≤ n) : (c.flag hn).types = {1, n - 1} := by
  have hh : Module.finrank (ZMod 2) c.hyperplane = n - 1 := by
    have := c.hyperplane_finrank
    omega
  simp [Flag.types, flag, c.line_finrank, hh]

/-- Over the binary field, stabilizing the image line and fixed hyperplane
forces commutation with the transvection. -/
theorem TransvectionCoordinates.centralizer_eq (c : TransvectionCoordinates e t) :
    centralizer ({t} : Set L) = subspaceStabilizer e c.line ⊓
      subspaceStabilizer e c.hyperplane := by
  have he : linearModel e t = BinaryLinear.transvection c.vector c.functional c.incident :=
    LinearEquiv.ext c.action
  have hc := centralizer_transvection c.vector_ne_zero c.functional_ne_zero c.incident
  ext x
  rw [mem_centralizer_singleton_iff]
  change x * t = t * x ↔ linearModel e x ∈
    BinaryLinear.parabolic c.line ⊓ BinaryLinear.parabolic c.hyperplane
  change x * t = t * x ↔ linearModel e x ∈
    BinaryLinear.parabolic (Submodule.span (ZMod 2) {c.vector}) ⊓
      BinaryLinear.parabolic c.functional.ker
  rw [← hc, mem_centralizer_singleton_iff, ← he]
  exact ⟨fun h => by simpa only [map_mul] using congrArg (linearModel e) h,
    fun h => (linearModel e).injective (by simpa only [map_mul] using h)⟩

theorem TransvectionCoordinates.centralizer_eq_flag (c : TransvectionCoordinates e t)
    (hn : 2 ≤ n) : centralizer ({t} : Set L) = flagStabilizer e (c.flag hn) := by
  rw [c.centralizer_eq]
  ext x
  simp only [mem_inf, mem_flagStabilizer, flag, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, mem_subspaceStabilizer]


theorem TransvectionCoordinates.ambientFlagStabilizer_eq (c : TransvectionCoordinates e t)
    (hn : 2 ≤ n) : ambientFlagStabilizer e (c.flag hn) =
      L ⊓ centralizer ({(t : G)} : Set G) := by
  change (flagStabilizer e (c.flag hn)).map L.subtype = _
  rw [← c.centralizer_eq_flag hn]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))⟩
  · rintro ⟨hx, hxt⟩
    exact ⟨⟨x, hx⟩, mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp hxt)), rfl⟩

variable {H M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The centralizer flag and all of S generate a subgroup already in M.
Thus this flag cannot be the escaping overgroup in the pair argument. -/
theorem TransvectionCoordinates.flagOvergroup_le (c : TransvectionCoordinates e t)
    (hn : 2 ≤ n) (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t) :
    flagOvergroup e (c.flag hn) ((S : Subgroup H).map H.subtype) ≤ M := by
  apply sup_le _ h.sylow_le
  rw [c.ambientFlagStabilizer_eq hn]
  exact (projection_centralizer_le_intersection ht h.centralizer_le).trans inf_le_right

/-- Only N_S(L) is used to prove invariance of the centralizer flag. -/
theorem TransvectionCoordinates.flag_invariant (c : TransvectionCoordinates e t)
    (hn : 2 ≤ n) (h : LocalSetup H L M S z) (ht : IsConjugationProjection L z t) :
    FlagInvariant e ((S : Subgroup H).map H.subtype) (c.flag hn) := by
  intro s hs
  rw [c.ambientFlagStabilizer_eq hn]
  apply inf_normalizer_le_normalizer_inf
  refine ⟨hs.2, le_normalizer ?_⟩
  exact mem_centralizer_singleton_iff.mpr
    (projection_centralizes_normalizer h e ht hs.1 hs.2)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
