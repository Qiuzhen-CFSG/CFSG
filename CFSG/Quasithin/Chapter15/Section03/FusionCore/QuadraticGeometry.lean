module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ElementFusion
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import CFSG.Quasithin.Chapter12.Section01
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# Singular intersections and the weak-closure rank

The quadratic form lives on the binary vector space of the actual elementary
abelian subgroup `V`. Fusion control and full-centralizer containment force
intersections with conjugates outside `N_G(V)` to be totally singular. The
same argument controls normalizers of subgroups containing a nonsingular
vector. Nondegeneracy bounds singular subgroups by order four, so every
centralizer-escape subgroup has corank at least two. Applying this to the
actual infimum defining `ChapterE.globalR` proves `r(G,V) > 1`.

`NaturalOrthogonalAction` records a full conjugation action on this quadratic
space, not merely an abstract isomorphism of the actor with a wreath product.
Its full-image condition quantifies over actual linear isometries, and the
singular plane fixes the plus type. Extracting the finite orbit and Sylow
calculations from that action remains a separate obligation.

These are conditional local implications for 15.3.46(2), (3), and (5), with
fusion and nonsingular centralizer bounds supplied by the preceding argument.
They do not assert the `W₀` centralization in clause (4).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1141.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore

variable {G : Type*} [Group G] {V M : Subgroup G} [IsElementaryAbelian 2 V]

/-- Total singularity in the actual quadratic space on `V`. -/
def IsTotallySingular (Q : QuadraticForm (ZMod 2) (Additive V))
    (U : Subgroup G) : Prop :=
  U ≤ V ∧ ∀ u : V, (u : G) ∈ U → Q (Additive.ofMul u) = 0

/-- A genuine full natural orthogonal action, on the given subgroup of `G`.
The image condition is surjectivity onto actual linear isometries. -/
structure NaturalOrthogonalAction (M V : Subgroup G) [IsElementaryAbelian 2 V] where
  normalizes : M ≤ normalizer (V : Set G)
  form : QuadraticForm (ZMod 2) (Additive V)
  nondegenerate : form.polarBilin.Nondegenerate
  dimension : Module.finrank (ZMod 2) (Additive V) = 4
  plusType : ∃ U : Submodule (ZMod 2) (Additive V),
    Module.finrank (ZMod 2) U = 2 ∧ ∀ u ∈ U, form u = 0
  preserves : ∀ (m : M) (v : V),
    form (Additive.ofMul ⟨MulAut.conj (m : G) v,
      (normalizes m.property v).mp v.property⟩) = form (Additive.ofMul v)
  full : ∀ e : form.IsometryEquiv form, ∃ m : M, ∀ v : V,
    MulAut.conj (m : G) v = ((e (Additive.ofMul v)).toMul : G)

/-- Transport a full-centralizer containment along a local orbit. -/
theorem centralizer_le_of_conjugateBy {x y : G}
    (hxy : ConjugateBy M x y) (hx : centralizer ({x} : Set G) ≤ M) :
    centralizer ({y} : Set G) ≤ M := by
  obtain ⟨m, hm, rfl⟩ := hxy
  intro c hc
  have hc' : MulAut.conj m⁻¹ c ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg (MulAut.conj m⁻¹) (mem_centralizer_singleton_iff.mp hc)
    simpa [MulAut.conj_apply, mul_assoc] using h
  have hmem := M.mul_mem (M.mul_mem hm (hx hc')) (M.inv_mem hm)
  simpa [MulAut.conj_apply, mul_assoc] using hmem

/-- A conjugate outside the normalizer has totally singular intersection
with `V`, using fusion control and the nonsingular centralizer bounds. -/
theorem totallySingular_intersection_of_fusion
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hM : M = normalizer (V : Set G))
    (hfusion : ∀ x ∈ V, ∀ a : G, MulAut.conj a x ∈ V →
      ConjugateBy M x (MulAut.conj a x))
    (hcentral : ∀ v : V, Q (Additive.ofMul v) ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ M)
    (g : G) (hg : g ∉ M) :
    IsTotallySingular Q (V ⊓ V.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨inf_le_left, ?_⟩
  intro v hv
  by_contra hq
  have heq := conjugate_eq_of_fusion_of_centralizer_le hM (v : G) g
    (hfusion v v.property) (hcentral v hq) hv.2
  exact hg (hM ▸ mem_normalizer_iff_map_conj_eq.mpr heq)

/-- The normalizer of a subgroup containing a nonsingular vector lies in
`M`. No ambient normality of that subgroup is assumed. -/
theorem normalizer_le_of_not_totallySingular
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hM : M = normalizer (V : Set G))
    (hfusion : ∀ x ∈ V, ∀ a : G, MulAut.conj a x ∈ V →
      ConjugateBy M x (MulAut.conj a x))
    (hcentral : ∀ v : V, Q (Additive.ofMul v) ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ M)
    {U : Subgroup G} (hUV : U ≤ V) (hU : ¬ IsTotallySingular Q U) :
    normalizer (U : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  apply hU
  refine ⟨hUV, ?_⟩
  intro u hu
  have hUg : U.map (MulAut.conj g).toMonoidHom = U :=
    mem_normalizer_iff_map_conj_eq.mp hg
  have hug : (u : G) ∈ V.map (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.map_mono hUV)
    rwa [hUg]
  exact (totallySingular_intersection_of_fusion Q hM hfusion hcentral g hgM).2 u
    ⟨u.property, hug⟩

/-- The second assertion of 15.3.46(2), also valid at the endpoints. -/
theorem totallySingular_of_normalizer_escape
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hM : M = normalizer (V : Set G))
    (hfusion : ∀ x ∈ V, ∀ a : G, MulAut.conj a x ∈ V →
      ConjugateBy M x (MulAut.conj a x))
    (hcentral : ∀ v : V, Q (Additive.ofMul v) ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ M)
    {U : Subgroup G} (hUV : U ≤ V) (hU : ¬ normalizer (U : Set G) ≤ M) :
    IsTotallySingular Q U := by
  by_contra h
  exact hU (normalizer_le_of_not_totallySingular Q hM hfusion hcentral hUV h)

/-- The polar-form dimension bound excludes singular hyperplanes in the
four-dimensional space. -/
theorem card_le_four_of_totallySingular [Finite G]
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank (ZMod 2) (Additive V) = 4)
    {U : Subgroup G} (hUV : U ≤ V) (hU : IsTotallySingular Q U) :
    Nat.card U ≤ 4 := by
  let W : Submodule (ZMod 2) (Additive V) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (U.subgroupOf V))
  have hsing : ∀ u ∈ W, Q u = 0 := fun u hu => hU.2 u.toMul hu
  have hbound := Chapter12.Section01.twice_finrank_le_of_totally_singular Q hQ W hsing
  rw [hdim] at hbound
  have hrank : Module.finrank (ZMod 2) W ≤ 2 := by omega
  have hc : Nat.card U = Nat.card W :=
    (Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv).symm
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hrank).trans_eq (by norm_num)

/-- The actual E.3.3 minimum exceeds one. The quadratic argument is applied
to every centralizer-escape subgroup in the defining infimum. -/
theorem one_lt_globalR [Finite G]
    (Q : QuadraticForm (ZMod 2) (Additive V))
    (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank (ZMod 2) (Additive V) = 4)
    (hM : M = normalizer (V : Set G))
    (hcentral : ∀ v : V, Q (Additive.ofMul v) ≠ 0 →
      centralizer ({(v : G)} : Set G) ≤ M) :
    1 < ChapterE.globalR V := by
  have hVcard : Nat.card V = 16 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod, hdim] at h
    exact h
  have htwo : (2 : ℕ∞) ≤ ChapterE.globalR V := by
    apply le_iInf
    intro U
    apply le_iInf
    rintro ⟨hUV, hescape⟩
    have hsing : IsTotallySingular Q U := by
      refine ⟨hUV, ?_⟩
      intro u hu
      by_contra hq
      apply hescape
      rw [← hM]
      exact (centralizer_le (Set.singleton_subset_iff.mpr hu)).trans (hcentral u hq)
    have hcard := card_le_four_of_totallySingular Q hQ hdim hUV hsing
    have hmul : Nat.card U * U.relIndex V = 16 := by
      have h := (U.subgroupOf V).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe hUV).toEquiv, hVcard] at h
      exact h
    have hindex : 4 ≤ U.relIndex V := by nlinarith
    have hlog : 2 ≤ ChapterE.subgroupCorank V U :=
      Nat.le_log_of_pow_le (by decide) hindex
    exact_mod_cast hlog
  exact lt_of_lt_of_le (by norm_num) htwo

end CFSG.Quasithin.Chapter15.Section03.FusionCore
