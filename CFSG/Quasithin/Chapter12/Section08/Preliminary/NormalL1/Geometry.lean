module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Geometry.Generation
public import Theory.GroupTheory.TINormalizerControl
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.FixedOrderGeneration

/-!
# Geometry of the normal-L₁ branch

Relative normality of L₁ in G₁ makes the Gᵢ-conjugate span equal the
N_L(Vᵢ)-conjugate span. Generation therefore gives Gᵢ≤N_G(L)=M.
The earlier TI property inside M gives Gᵢ≤M_V, and the genuine 12.8.3
transitivity gives uniqueness. A plane in an intersection of conjugates
then proves the prime-rank bound, retaining right conjugation throughout.

`normal_geometry_of_linear_generation` assembles all these deductions,
including the ambient product factorization and the lift through O₂(L).
The concrete linear point-residual generation is an explicit premise here;
`Geometry.Assembly.normal_geometry` discharges it using the structural
calculation in `Geometry.LinearGeneration`. The earlier-source assembly
retains the 12.2.5–6 and 12.8.3 inputs.

Source: Aschbacher–Smith, Lemma 12.8.5(2), printed p.850 (PDF p.867),
and Notation 12.2.5 / Lemma 12.2.6, printed pp.796–797.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
open Subgroup
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {V L M : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- Relative normality in G₁ compares its conjugate span with the natural parabolic span. -/
theorem normalizer_span_eq (F : InvariantFlag T V n) (d : NaturalAction L V)
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal) (i : ℕ) (hi : 1 ≤ i) :
    conjugateSpanBy (F.Li L 1) (F.Gi i) =
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) := by
  apply conjugateSpanBy_eq_of_action_image (F.Vi i) _ _ _ inf_le_right
  · exact ((centralizer_le (F.monotone hi)).trans (centralizer_le_normalizer _)).trans
      ((normal_subgroupOf_iff_le_normalizer
        ((F.Li_le L 1).trans inf_le_right)).mp hL1)
  · exact normalizer_action_image d (F.Vi i) (F.le_seed i)

omit [Finite G] in
/-- The span comparison forces Gᵢ to normalize the original L. -/
theorem normalizer_le_M_of_generation (F : InvariantFlag T V n)
    (d : NaturalAction L V) (hM : M = normalizer (L : Set G))
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal) (i : ℕ) (hi : 1 ≤ i)
    (hgen : conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L) : F.Gi i ≤ M := by
  rw [hM, ← hgen, ← normalizer_span_eq F d hL1 i hi]
  exact le_normalizer_conjugateSpanBy _ _

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- The earlier TI property inside M controls the seed normalizer. -/
theorem normalizer_le_seedNormalizer (F : InvariantFlag T V n)
    (hTI : ∀ g ∈ M, V ⊓ conjugate V g = ⊥ ∨ conjugate V g = V)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) (hGi : F.Gi i ≤ M) :
    F.Gi i ≤ seedNormalizer M V := by
  have hne : F.Vi i ≠ ⊥ := by
    intro he
    have hc := F.card i hin
    rw [he, Nat.card_unique] at hc
    have hp : 2 ≤ 2 ^ i := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ i := pow_le_pow_right' (by decide) hi
    omega
  have hTI' : ∀ g ∈ M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V := by
    intro g hg
    simpa only [conjugate, inv_inv] using hTI g⁻¹ (M.inv_mem hg)
  exact le_inf hGi (fun g hg =>
    inf_normalizer_le_of_trivial_intersections hTI' hne (F.le_seed i) ⟨hGi hg, hg⟩)

omit [Finite G] [IsElementaryAbelian 2 V] in
/-- Source 12.8.3(3) turns normalizer control into uniqueness of the ambient conjugate. -/
theorem unique_conjugate_of_normalizer_le (F : InvariantFlag T V n)
    (i : ℕ) (hGi : F.Gi i ≤ seedNormalizer M V)
    (htrans : ∀ g : G, F.Vi i ≤ conjugate V g →
      ∃ k ∈ F.Gi i, conjugate V g = conjugate V k) :
    ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V := by
  intro g hg
  obtain ⟨k, hk, he⟩ := htrans g hg
  exact he.trans ((conjugate_eq_iff V k).mpr (hGi hk).2)

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem conjugate_mul (A : Subgroup G) (g h : G) :
    conjugate A (g * h) = conjugate (conjugate A g) h := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Plane transitivity and uniqueness give the literal ambient rank bound. -/
theorem intersection_rank_le_one (F : InvariantFlag T V n)
    (hLV : L ≤ normalizer (V : Set G))
    (hNV : normalizer (V : Set G) ≤ M)
    (hplanes : ∀ A : Subgroup G, A ≤ V → Nat.card A = 4 →
      ∃ l ∈ L, conjugate A l = F.Vi 2)
    (hunique : ∀ g : G, F.Vi 2 ≤ conjugate V g → conjugate V g = V)
    (g : G) (hg : g ∉ seedNormalizer M V) :
    primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 := by
  let I := V ⊓ conjugate V g
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.of_le (show I ≤ V from inf_le_left)
  apply IsElementaryAbelian.primeRank_le_of_card_le
  change Nat.card I ≤ 2 ^ 1
  by_contra hc
  have hcard : 4 ≤ Nat.card I := by
    obtain ⟨r, hr⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
    have hr2 : 2 ≤ r := by
      by_contra h
      have : r = 0 ∨ r = 1 := by omega
      rcases this with h | h <;> simp [hr, h] at hc
    rw [hr]
    exact pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) hr2
  obtain ⟨A, hAI, _, hAc, _⟩ :=
    IsElementaryAbelian.exists_two_power_subgroup_mem I (n := 2) (by decide) hcard 1 I.one_mem
  obtain ⟨l, hl, hAl⟩ := hplanes A (hAI.trans inf_le_left) hAc
  have hcontain : F.Vi 2 ≤ conjugate V (g * l) := by
    rw [conjugate_mul, ← hAl]
    exact map_mono (hAI.trans inf_le_right)
  have he : conjugate V g = V := by
    have h := congrArg (fun A : Subgroup G => conjugate A l⁻¹) (hunique (g * l) hcontain)
    rw [← conjugate_mul, mul_inv_cancel_right] at h
    simpa only [(conjugate_eq_iff V l⁻¹).mpr ((normalizer (V : Set G)).inv_mem (hLV hl))] using h
  have hnorm := (conjugate_eq_iff V g).mp he
  exact hg ⟨hNV hnorm, hnorm⟩

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry

namespace CFSG.Quasithin.Chapter12.Section08.NormalGeometry
open Subgroup
open scoped IsMulCommutative Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {V L M : Subgroup G} {n : ℕ} [IsElementaryAbelian 2 V]

/-- The complete geometric argument of 12.8.5(2), conditional only on the
remaining concrete linear generation and the named earlier source inputs.
`hTI` and `hNV` are 12.2.6 and Notation 12.2.5(2); `hplanes` and `htrans`
are 12.8.3(2,3). The assembly owner must prove `hlinear`, not retain it as
a hypothesis of the final source theorem. -/
theorem normal_geometry_of_linear_generation (F : InvariantFlag T V n)
    (d : NaturalAction L V) (hn : 2 < n)
    (hL : pResidual 2 L = ⊤) (hM : M = normalizer (L : Set G))
    (hL1 : ((F.Li L 1).subgroupOf F.H).Normal)
    (hTI : ∀ g ∈ M, V ⊓ conjugate V g = ⊥ ∨ conjugate V g = V)
    (hNV : normalizer (V : Set G) ≤ M)
    (hplanes : ∀ A : Subgroup G, A ≤ V → Nat.card A = 4 →
      ∃ l ∈ L, conjugate A l = F.Vi 2)
    (htrans : ∀ i, 1 < i → i < n → ∀ g : G, F.Vi i ≤ conjugate V g →
      ∃ k ∈ F.Gi i, conjugate V g = conjugate V k)
    (hlinear : ∀ i, 1 < i → i < n → conjugateSpanBy
      ((pResidual 2 (BinaryLinear.parabolic (space (V := V) (F.Vi 1)))).map
        (BinaryLinear.parabolic (space (V := V) (F.Vi 1))).subtype)
      (BinaryLinear.parabolic (space (V := V) (F.Vi i))) = ⊤) :
    (∀ i, 1 < i → i < n →
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L ∧
      (F.Gi i : Set G) = (centralizer (F.Vi i : Set G) : Set G) *
        (L ⊓ F.Gi i : Subgroup G) ∧
      F.Gi i ≤ M ∧ F.Gi i ≤ seedNormalizer M V ∧
      ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V) ∧
    ∀ g : G, g ∉ seedNormalizer M V →
      primeRank 2 (V ⊓ conjugate V g : Subgroup G) ≤ 1 := by
  have hgeo (i : ℕ) (hi : 1 < i) (hin : i < n) :
      conjugateSpanBy (F.Li L 1) (L ⊓ F.Gi i) = L ∧
      (F.Gi i : Set G) = (centralizer (F.Vi i : Set G) : Set G) *
        (L ⊓ F.Gi i : Subgroup G) ∧
      F.Gi i ≤ M ∧ F.Gi i ≤ seedNormalizer M V ∧
      ∀ g : G, F.Vi i ≤ conjugate V g → conjugate V g = V := by
    have hgen := flag_generation_of_linear F d hL i (hlinear i hi hin)
    have hGi := normalizer_le_M_of_generation F d hM hL1 i hi.le hgen
    have hseed := normalizer_le_seedNormalizer F hTI i hi.le hin.le hGi
    exact ⟨hgen, normalizer_factorization d (F.Vi i) (F.le_seed i), hGi, hseed,
      unique_conjugate_of_normalizer_le F i hseed (htrans i hi hin)⟩
  refine ⟨hgeo, ?_⟩
  exact intersection_rank_le_one F (natural_normalizes d) hNV hplanes
    (hgeo 2 (by decide) hn).2.2.2.2

end CFSG.Quasithin.Chapter12.Section08.NormalGeometry
