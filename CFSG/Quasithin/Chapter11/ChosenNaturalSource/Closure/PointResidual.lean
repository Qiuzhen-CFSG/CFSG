module

public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.ConjugateSpanSylow
public import CFSG.Quasithin.Chapter11.Section04To05.Conjugacy

/-!
# Point residuals in the final natural-module intersection argument

The point residual is the embedded solvable residual of C_L(u), and its
point closure is its normal closure under C_G(u). These constructions retain
the actual ambient embeddings. Equivariance and normality give the equality
of point closures for two conjugate modules containing the same nonidentity
point. Generation by point residuals then forces any larger intersection to
normalize L, where the preceding TI result applies.

This is the group-theoretic part of 11.5.2 and 11.5.3(1). The natural-module
point-generation assertion remains an explicit premise, as does the earlier
TI assertion. No weak-closure or terminal abelianness conclusion is assumed.
Source: Aschbacher--Smith, combined manuscript, printed p.779.
Conjugation here is x ↦ g*x*g⁻¹, inverse to the source exponent convention.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open Subgroup
variable {G : Type*} [Group G]

/-- The solvable residual of a subgroup, embedded in the common ambient group. -/
def residualIn (A : Subgroup G) : Subgroup G := (solvableResidual A).map A.subtype

/-- The source point stabilizer's terminal derived subgroup, not its two-residual. -/
def pointResidual (L : Subgroup G) (u : G) : Subgroup G :=
  residualIn (L ⊓ centralizer ({u} : Set G))

/-- Normal closure of the actual point residual under the point centralizer. -/
def pointClosure (L : Subgroup G) (u : G) : Subgroup G :=
  conjugateSpanBy (pointResidual L u) (centralizer ({u} : Set G))

theorem residualIn_le (A : Subgroup G) : residualIn A ≤ A := map_subtype_le _

theorem pointResidual_le_closure (L : Subgroup G) (u : G) :
    pointResidual L u ≤ pointClosure L u := le_conjugateSpanBy _ _

theorem centralizer_normalizes_pointClosure (L : Subgroup G) (u : G) :
    centralizer ({u} : Set G) ≤ normalizer (pointClosure L u : Set G) :=
  le_normalizer_conjugateSpanBy _ _

private theorem map_centralizer_point (e : G ≃* G) (u : G) :
    (centralizer ({u} : Set G)).map (e : G →* G) = centralizer ({e u} : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e y * e u = e u * e y
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hy)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hx

variable [Finite G]

theorem residualIn_map (A : Subgroup G) (e : G ≃* G) :
    (residualIn A).map (e : G →* G) = residualIn (A.map (e : G →* G)) := by
  let f := e.subgroupMap A
  have hf := map_solvableResidual_eq (f : A →* A.map (e : G →* G)) f.surjective
  have hm := congrArg (Subgroup.map (A.map (e : G →* G)).subtype) hf
  have hc : (A.map (e : G →* G)).subtype.comp (f : A →* A.map (e : G →* G)) =
      (e : G →* G).comp A.subtype := rfl
  simpa only [residualIn, map_map, hc] using hm

/-- Point residuals transport through the literal conjugation map. -/
theorem pointResidual_map (L : Subgroup G) (u : G) (e : G ≃* G) :
    (pointResidual L u).map (e : G →* G) = pointResidual (L.map (e : G →* G)) (e u) := by
  rw [pointResidual, residualIn_map, map_inf _ _ _ e.injective,
    map_centralizer_point, pointResidual]

/-- Equivariance of the point closure, including its indexing centralizer. -/
theorem pointClosure_map (L : Subgroup G) (u : G) (e : G ≃* G) :
    (pointClosure L u).map (e : G →* G) = pointClosure (L.map (e : G →* G)) (e u) := by
  rw [pointClosure, map_conjugateSpanBy, pointResidual_map, map_centralizer_point,
    pointClosure]

/-- The normality step of 11.5.2(2). -/
theorem pointClosure_conjugate_of_centralizes (L : Subgroup G) (u g : G)
    (hg : g ∈ centralizer ({u} : Set G)) :
    pointClosure (L.map (MulAut.conj g : G →* G)) u = pointClosure L u := by
  have hu : (MulAut.conj g) u = u := by
    simpa only [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using
      mem_centralizer_singleton_iff.mp hg
  have h := pointClosure_map L u (MulAut.conj g)
  rw [hu, mem_normalizer_iff_map_conj_eq.mp
    (centralizer_normalizes_pointClosure L u hg)] at h
  exact h.symm

omit [Finite G] in
private theorem map_conj_mul (A : Subgroup G) (g l : G) :
    A.map (MulAut.conj (g * l) : G →* G) =
      (A.map (MulAut.conj l : G →* G)).map (MulAut.conj g : G →* G) := by
  rw [map_map]
  congr 1
  ext x
  change (g * l) * x * (g * l)⁻¹ = g * (l * x * l⁻¹) * g⁻¹
  group

/-- Transitivity adjusts the conjugator while preserving both L and V.
This is the point-closure version of the two clauses of 11.5.2. -/
theorem pointClosure_eq_of_common_point (L V : Subgroup G)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (u g : G) (hu : u ∈ V) (hu1 : u ≠ 1)
    (hug : u ∈ V.map (MulAut.conj g : G →* G)) :
    pointClosure (L.map (MulAut.conj g : G →* G)) u = pointClosure L u := by
  obtain ⟨v, hv, hgv⟩ := hug
  have hv1 : v ≠ 1 := by
    intro he
    exact hu1 (by simpa [he] using hgv.symm)
  obtain ⟨l, hl, hlu⟩ := htrans u hu hu1 v hv hv1
  have hc : g * l ∈ centralizer ({u} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he : (MulAut.conj (g * l)) u = u := by
      change (MulAut.conj g) v = u at hgv
      simpa only [map_mul, MulAut.mul_apply, hlu] using hgv
    simpa only [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] using he
  have hL : L.map (MulAut.conj (g * l) : G →* G) =
      L.map (MulAut.conj g : G →* G) := by
    rw [map_conj_mul, mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hl)]
  simpa only [hL] using pointClosure_conjugate_of_centralizes L u (g * l) hc

/-- If the point closure at z lies in L, transitivity gives that containment
at every nonidentity point of V. In 11.5.3 the initial containment is K=L₁≤L. -/
theorem pointClosure_le_of_transitive (L V : Subgroup G) (z : G)
    (hz : z ∈ V) (hz1 : z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : pointClosure L z ≤ L) (u : G) (hu : u ∈ V) (hu1 : u ≠ 1) :
    pointClosure L u ≤ L := by
  obtain ⟨l, hl, hlu⟩ := htrans z hz hz1 u hu hu1
  have hL := mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer hl)
  have he := pointClosure_map L z (MulAut.conj l)
  rw [hL, hlu] at he
  rw [← he]
  exact (map_mono hK).trans hL.le

/-- The source's local generation assertion, isolated from the ambient
closure argument. Its generators are actual point-stabilizer residuals. -/
def PointGeneration (L V V₁ : Subgroup G) : Prop :=
  ∀ A : Subgroup G, A ≤ V →
    (∀ l ∈ L, ¬ A ≤ V₁.map (MulAut.conj l : G →* G)) →
      L ≤ ⨆ u : {u : G // u ∈ A ∧ u ≠ 1}, pointResidual L u.val

/-- The intersection assertion of 11.5.3(1), conditional on the preceding
TI result and the natural-module point generation, with K=L₁ supplying hK. -/
theorem line_intersections_of_pointGeneration (L V V₁ : Subgroup G) (z : G)
    (hz : z ∈ V) (hz1 : z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hK : pointClosure L z ≤ L) (hgen : PointGeneration L V V₁)
    (hTI : ∀ g ∈ normalizer (L : Set G), V ⊓ V.map (MulAut.conj g : G →* G) ≠ ⊥ →
      V.map (MulAut.conj g : G →* G) = V)
    (g : G) (hg : g ∉ normalizer (V : Set G)) :
    ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
      V₁.map (MulAut.conj l : G →* G) := by
  classical
  by_contra hn
  have havoid : ∀ l ∈ L, ¬ V ⊓ V.map (MulAut.conj g : G →* G) ≤
      V₁.map (MulAut.conj l : G →* G) := by simpa only [not_exists, not_and] using hn
  have hne : V ⊓ V.map (MulAut.conj g : G →* G) ≠ ⊥ := by
    intro he
    exact havoid 1 L.one_mem (he ▸ bot_le)
  have hle : L ≤ L.map (MulAut.conj g : G →* G) := by
    apply (hgen _ inf_le_left havoid).trans
    apply iSup_le
    rintro ⟨u, hu, hu1⟩
    apply (pointResidual_le_closure L u).trans
    rw [← pointClosure_eq_of_common_point L V htrans u g hu.1 hu1 hu.2]
    obtain ⟨v, hv, hgv⟩ := hu.2
    have hv1 : v ≠ 1 := by
      intro he
      exact hu1 (by simpa [he] using hgv.symm)
    rw [← hgv]
    change pointClosure (L.map (MulAut.conj g : G →* G)) ((MulAut.conj g) v) ≤ _
    rw [← pointClosure_map]
    exact map_mono (pointClosure_le_of_transitive L V z hz hz1 htrans hK v hv hv1)
  have heq : L.map (MulAut.conj g : G →* G) = L :=
    (eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])).symm
  exact hg (mem_normalizer_iff_map_conj_eq.mpr
    (hTI g (mem_normalizer_iff_map_conj_eq.mpr heq) hne))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
