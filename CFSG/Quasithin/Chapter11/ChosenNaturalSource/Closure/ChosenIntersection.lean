module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Corank
public import Theory.ElementaryAbelian.BinaryRankDifference

/-!
# Point intersections on the original Chapter12 choice

These applications use the original chosen V and the inverse image of the
specified line in D's actual fixed-space quotient. The source K is the
normal closure of the solvable residual L₁ in N_G(V₁).

The preceding transitivity, TI and Kz=K conclusions are explicit. Two local
inputs still require the marked natural-module calculation: the point
stabilizer residual at z is L₁, and residuals at points outside a field line
generate L. Under K=L₁ these give the intersection and actual global-r bound
of 11.5.3(1--2). This does not prove 11.5.3(3), 11.5.7 or 11.5.8.
Source: Aschbacher--Smith, combined manuscript, printed p.779.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open Subgroup ChapterE
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Source 11.5.2(1) on the actual chosen module, from 11.4.1 transitivity. -/
theorem conjugate_through_z
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (g : G) (hg : E.z ∈ V.map (MulAut.conj g : G →* G)) :
    ∃ c ∈ centralizer ({E.z} : Set G),
      V.map (MulAut.conj c : G →* G) = V.map (MulAut.conj g : G →* G) :=
  conjugate_containing_mem_centralizer_orbit L V D.normalizes htrans (E.V₁_le hz) hz1 g hg

/-- Source 11.5.2(2) after the literal point-stabilizer residual has been
identified; conjugation has the inverse direction to source exponent notation. -/
theorem pointClosure_conjugate_at_z
    (hres : pointResidual L E.z = E.L₁) (hK : E.Kz = E.K)
    (g : G) (hg : g ∈ centralizer ({E.z} : Set G)) :
    pointClosure (L.map (MulAut.conj g : G →* G)) E.z = E.K := by
  rw [pointClosure_conjugate_of_centralizes L E.z g hg, E.pointClosure_eq_K hres hK]

/-- The two intersection consequences on the original chosen quotient flag.
PointGeneration remains the precise local-model input, rather than an assumed
intersection or centralizer conclusion. -/
theorem intersection_and_corank
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (htrans : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v)
    (hres : pointResidual L E.z = E.L₁) (hK : E.Kz = E.K)
    (hgen : PointGeneration L V E.V₁)
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g : G →* G) = ⊥ ∨ V.map (MulAut.conj g : G →* G) = V)
    (hKL : E.K = E.L₁) :
    (∀ g : G, g ∉ normalizer (V : Set G) →
      ∃ l ∈ L, V ⊓ V.map (MulAut.conj g : G →* G) ≤
        E.V₁.map (MulAut.conj l : G →* G)) ∧
      (subgroupCorank V E.V₁ : ℕ∞) ≤ globalR V := by
  have hpoint : pointClosure L E.z ≤ L := by
    rw [E.pointClosure_eq_K hres hK, hKL]
    exact E.L₁_le
  have hbound := line_intersections_of_pointGeneration L V E.V₁ E.z
    (E.V₁_le hz) hz1 htrans hpoint hgen
    (fun g hg hne => (hTI g hg).resolve_left hne)
  exact ⟨hbound, globalR_ge_of_line_intersections L V E.V₁ D.normalizes hbound⟩

/-- A field line has the expected binary codimension: choosing m=2n or m=3n
gives exactly the two values in 11.5.3. The cardinal inputs refer to the
original subgroup and the actual quotient preimage, not a replacement module. -/
theorem line_corank_of_cardinalities {m : ℕ}
    (hV : Nat.card V = 2 ^ (m + E.input.field.degree))
    (hline : Nat.card E.V₁ = 2 ^ E.input.field.degree) :
    subgroupCorank V E.V₁ = m := by
  let := D.elementary
  unfold subgroupCorank
  rw [← log_card_sub_log_card_eq_log_relIndex V E.V₁ E.V₁_le,
    hV, hline, Nat.log_pow Nat.one_lt_two, Nat.log_pow Nat.one_lt_two]
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
