module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Basic
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Geometry
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The Sylow marking of a pure vector

A binary linear Sylow subgroup fixes a nonzero vector and contains the
radical of its line. The radical fixes precisely that line, so the common
fixed space is one-dimensional. The normal intersection with the inner
automorphisms transfers this statement to the given Sylow of Aut(GL_n(2)).
The summand normalizer is exactly the inner subgroup; hence its Sylow
intersection is the full Sylow centralizer of every nonzero fixed vector.

Source: Aschbacher–Smith, H.9.1(3), printed pp.389–390. No adapted
nonsingular-pair conclusion is used.
-/

@[expose] public section
namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear
open BinaryLinear.OuterCyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A Sylow of a nonzero binary space fixes exactly one line. -/
theorem linear_sylow_fixed_line [Finite V] [FiniteDimensional (ZMod 2) V]
    (hV : 0 < Module.finrank (ZMod 2) V) (S : Sylow 2 (BinaryLinear.GL V)) :
    ∃ x : V, x ≠ 0 ∧ BinaryLinear.fixedSpace (S : Subgroup (BinaryLinear.GL V)) =
      Submodule.span (ZMod 2) {x} := by
  have hcard : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (fixedSpace_ne_bot hcard S.isPGroup')
  let W := Submodule.span (ZMod 2) {x}
  have hSW : (S : Subgroup (BinaryLinear.GL V)) ≤ parabolic W := by
    rw [parabolic_line_eq hx0]
    exact fun g hg => hx g hg
  have hRS : radical W ≤ (S : Subgroup (BinaryLinear.GL V)) := by
    have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (radical_two W)
      (hSW.trans (parabolic_le_normalizer W))) le_sup_left
    exact he ▸ le_sup_right
  refine ⟨x,hx0, le_antisymm ?_ ?_⟩
  · intro v hv
    exact (mem_iff_fixed_radical (mt Submodule.span_singleton_eq_bot.mp hx0) v).mpr
      (fun g hg => hv g (hRS hg))
  · exact Submodule.span_le.mpr (by simpa using hx)

/-- The marked natural summand of the coordinate module. -/
def naturalSummand (n : ℕ) : Submodule (ZMod 2) (CoordinateSpace n) :=
  (⊤ : Submodule (ZMod 2) (OuterCyclic.Space n)).prod ⊥

@[simp] theorem mem_naturalSummand {n : ℕ} (v : CoordinateSpace n) :
    v ∈ naturalSummand n ↔ v.2 = 0 := by simp [naturalSummand]

/-- Its actual setwise stabilizer in the automorphism group. -/
def summandNormalizer {n : ℕ} (d : CoordinateAction n) : Subgroup (MulAut (LinearGroup n)) :=
  (parabolic (naturalSummand n)).comap (AdaptedPair.linearAction d)

/-- In degrees four and five the natural summand normalizer is precisely the inner group. -/
theorem summandNormalizer_eq_inner {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n) :
    summandNormalizer d = MulAut.innerSubgroup (LinearGroup n) := by
  apply le_antisymm
  · intro a ha
    obtain ⟨g,rfl | rfl⟩ := inner_graph hn a
    · exact ⟨g,rfl⟩
    · let x : OuterCyclic.Space n := fun _ => 1
      have hx : x ≠ 0 := by
        intro he
        have hh := congrFun he ⟨0, by omega⟩
        exact one_ne_zero hh
      have hp : (x, (0 : Module.Dual (ZMod 2) (OuterCyclic.Space n))) ∈ naturalSummand n := by simp
      have hz := (ha (x,0)).mpr hp
      have hs : (d.representation (graphLinear n * MulAut.conj g) (x,0)).2 = 0 :=
        (mem_naturalSummand _).mp hz
      have hf := graph_inner_pure d g x
      have he : AdaptedPair.linearAction d (graphLinear n * MulAut.conj g) (x,0) = 0 :=
        Prod.ext hf hs
      have hh := (AdaptedPair.linearAction d (graphLinear n * MulAut.conj g)).map_eq_zero_iff.mp he
      exact False.elim (hx (congrArg Prod.fst hh))
  · rintro a ⟨g,rfl⟩ v
    change d.representation (MulAut.conj g) v ∈ naturalSummand n ↔ v ∈ naturalSummand n
    rw [d.on_inner, naturalDualRepresentation_apply, mem_naturalSummand, mem_naturalSummand]
    exact g.symm.dualMap.map_eq_zero_iff

/-- T₁=N_T(X), as an ambient subgroup. -/
def sylowSummandNormalizer {n : ℕ} (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) : Subgroup (MulAut (LinearGroup n)) :=
  (T : Subgroup (MulAut (LinearGroup n))) ⊓ summandNormalizer d

/-- The actual fixed subspace in the marked natural summand. -/
def naturalFixedSpace {n : ℕ} (d : CoordinateAction n) (H : Subgroup (MulAut (LinearGroup n))) :
    Submodule (ZMod 2) (OuterCyclic.Space n) where
  carrier := {x | ∀ a ∈ H, d.representation a (x,0) = (x,0)}
  zero_mem' := by
    intro a ha
    exact (d.representation a).map_zero
  add_mem' := by
    intro x y hx hy a ha
    have he : (x+y, (0 : Module.Dual (ZMod 2) (OuterCyclic.Space n))) = (x,0)+(y,0) := by simp
    rw [he, map_add, hx a ha, hy a ha]
  smul_mem' := by
    intro c x hx a ha
    have he : (c • x, (0 : Module.Dual (ZMod 2) (OuterCyclic.Space n))) = c • (x,0) := by simp
    rw [he, map_smul, hx a ha]

/-- The conjugation map is an actual isomorphism onto the inner automorphisms. -/
noncomputable def linearEquivInner {n : ℕ} (d : CoordinateAction n) :
    LinearGroup n ≃* MulAut.innerSubgroup (LinearGroup n) :=
  MonoidHom.ofInjective (inner_injective d)

@[simp] theorem linearEquivInner_val {n : ℕ} (d : CoordinateAction n) (g : LinearGroup n) :
    (linearEquivInner d g).val = MulAut.conj g := rfl


private instance linear_finite (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : OuterCyclic.Space n → OuterCyclic.Space n))
    DFunLike.coe_injective

private instance automorphism_finite (n : ℕ) : Finite (MulAut (LinearGroup n)) :=
  Finite.of_injective (fun a : MulAut (LinearGroup n) => (a : LinearGroup n → LinearGroup n))
    DFunLike.coe_injective

/-- T₁ is the embedded image of an actual Sylow subgroup of the natural linear group. -/
theorem exists_linear_sylow {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) :
    ∃ S : Sylow 2 (LinearGroup n),
      (S : Subgroup (LinearGroup n)).map MulAut.conj = sylowSummandNormalizer d T := by
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal (MulAut.innerSubgroup (LinearGroup n))
  let e := linearEquivInner d
  let S := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨S, ?_⟩
  have he : (MulAut.conj : LinearGroup n →* MulAut (LinearGroup n)).comp e.symm.toMonoidHom =
      (MulAut.innerSubgroup (LinearGroup n)).subtype := by
    apply MonoidHom.ext
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply a)
  change ((P : Subgroup _).map e.symm.toMonoidHom).map MulAut.conj = _
  rw [Subgroup.map_map, he, hP, sylowSummandNormalizer, summandNormalizer_eq_inner hn d]

/-- Comparison of actual natural fixed spaces under the inner embedding. -/
theorem naturalFixedSpace_map_conj {n : ℕ} (d : CoordinateAction n)
    (S : Subgroup (LinearGroup n)) :
    naturalFixedSpace d (S.map MulAut.conj) = BinaryLinear.fixedSpace S := by
  ext x
  constructor
  · intro hx g hg
    have he := hx (MulAut.conj g) (Subgroup.mem_map.mpr ⟨g,hg,rfl⟩)
    rw [d.on_inner, naturalDualRepresentation_apply] at he
    exact congrArg Prod.fst he
  · intro hx a ha
    obtain ⟨g,hg,rfl⟩ := ha
    rw [d.on_inner, naturalDualRepresentation_apply, hx g hg, map_zero]

/-- The given T₁ fixes precisely one natural line. -/
theorem sylow_fixed_line {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) :
    ∃ x : OuterCyclic.Space n, x ≠ 0 ∧
      naturalFixedSpace d (sylowSummandNormalizer d T) = Submodule.span (ZMod 2) {x} := by
  obtain ⟨S,hS⟩ := exists_linear_sylow hn d T
  obtain ⟨x,hx,he⟩ := linear_sylow_fixed_line (V := OuterCyclic.Space n) (by
    simpa only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] using (show 0 < n by omega)) S
  refine ⟨x,hx,?_⟩
  rw [← hS, naturalFixedSpace_map_conj, he]

/-- The source fixed-space dimension is a conclusion for every actual Sylow T. -/
theorem sylow_fixed_finrank {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) :
    Module.finrank (ZMod 2) (naturalFixedSpace d (sylowSummandNormalizer d T)) = 1 := by
  obtain ⟨x,hx,he⟩ := sylow_fixed_line hn d T
  rw [he, finrank_span_singleton hx]

/-- Every nonzero fixed vector has T-centralizer exactly T₁. -/
theorem sylow_centralizer_eq {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) {x : OuterCyclic.Space n} (hx : x ≠ 0)
    (hfixed : x ∈ naturalFixedSpace d (sylowSummandNormalizer d T)) :
    (T : Subgroup (MulAut (LinearGroup n))) ⊓ fullStabilizer d (x,0) =
      sylowSummandNormalizer d T := by
  apply le_antisymm
  · intro a ha
    refine ⟨ha.1, ?_⟩
    rw [summandNormalizer_eq_inner hn d]
    exact pure_fullStabilizer_le_inner hn d hx ha.2
  · intro a ha
    exact ⟨ha.1, hfixed a ha⟩

/-- The centralizer of a nonzero fixed vector is Sylow in its full stabilizer. -/
theorem sylow_centralizer_isSylow {n : ℕ} (hn : n = 4 ∨ n = 5) (d : CoordinateAction n)
    (T : Sylow 2 (MulAut (LinearGroup n))) {x : OuterCyclic.Space n} (hx : x ≠ 0)
    (hfixed : x ∈ naturalFixedSpace d (sylowSummandNormalizer d T)) :
    ∃ P : Sylow 2 (fullStabilizer d (x,0)),
      (P : Subgroup (fullStabilizer d (x,0))).map (fullStabilizer d (x,0)).subtype =
        sylowSummandNormalizer d T := by
  obtain ⟨S,hS⟩ := exists_linear_sylow hn d T
  have hSP : (S : Subgroup (LinearGroup n)) ≤ pointStabilizer x := by
    intro g hg
    have he := hfixed (MulAut.conj g) (hS ▸ Subgroup.mem_map.mpr ⟨g,hg,rfl⟩)
    rw [d.on_inner, naturalDualRepresentation_apply] at he
    exact congrArg Prod.fst he
  let Q := S.subtype hSP
  let e := fullEquivPoint hn d hx
  let P := Q.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨P, ?_⟩
  have he : (fullStabilizer d (x,0)).subtype.comp e.symm.toMonoidHom =
      (MulAut.conj : LinearGroup n →* MulAut (LinearGroup n)).comp (pointStabilizer x).subtype := by
    apply MonoidHom.ext
    intro g
    have hh := innerEquivPoint_conj d x
      ((MulEquiv.subgroupCongr (pure_fullStabilizer_eq_innerStabilizer hn d hx)) (e.symm g))
    have hh' : MulAut.conj (e (e.symm g)).val = (e.symm g).val := hh
    rw [e.apply_symm_apply] at hh'
    exact hh'.symm
  change ((Q : Subgroup (pointStabilizer x)).map e.symm.toMonoidHom).map _ = _
  rw [Subgroup.map_map, he, ← Subgroup.map_map]
  change (((S : Subgroup (LinearGroup n)).subgroupOf (pointStabilizer x)).map
    (pointStabilizer x).subtype).map MulAut.conj = _
  rw [Subgroup.map_subgroupOf_eq_of_le hSP, hS]

end BinaryNaturalDual.VectorStabilizers.Pure
