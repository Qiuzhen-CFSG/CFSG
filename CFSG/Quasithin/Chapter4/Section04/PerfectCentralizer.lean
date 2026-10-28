module

public import Theory.GroupAction.PerfectFixedCover
public import Theory.GroupTheory.ConjugateSpanOrder
public import CFSG.Quasithin.Chapter4.Defs
public import Theory.GroupAction.SubgroupConjugation

/-!
# Perfect centralizer covering and generation in suitable odd locals

The first theorem proves the finite-group content of Aschbacher--Smith
Lemma 4.4.5 (combined manuscript, 1 March 2004, printed p.620): a perfect
M₊ is the product of C_{M₊}(B)^∞ and O₂(M₊) when the odd-order actor B
centralizes M₊/O₂(M₊). The section centralizer includes normalization,
and infinity denotes the solvable residual, not the two-residual.

The second theorem applies that factorization to the actual conjugate
span of C_{V₀}(T) in the proof of Theorem 4.4.14, printed p.625. It proves
that V₀ and [V₀,M₊] centralize B. The source's R₂ and fixed-seed hypotheses
are retained as the precise containment and generation inputs used here.
The 4.2.1 setup, component alternatives in 4.4.3, and 4.4.13 are still
required for the complete source theorem.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

/-- Lemma 4.4.5 from its finite-group inputs. Perfectness of M₊ is supplied
by the earlier pushing-up setup; no classification conclusion is assumed. -/
theorem perfect_centralizer_cover (X B : Subgroup G) [Group.IsPerfect X]
    (hB : B ≤ sectionCentralizer X) (hodd : Odd (Nat.card B)) :
    (X : Set G) =
      ((solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
        (X ⊓ centralizer (B : Set G)).subtype : Set G) * (X.pCoreIn 2 : Set G) := by
  have hnorm : B ≤ normalizer (X : Set G) :=
    hB.trans (commutatorPreimage_le _ _ _)
  have hcore : normalizer (X : Set G) ≤ normalizer (X.pCoreIn 2 : Set G) :=
    by
      apply le_normalizer_iff.mpr
      intro g hg x hx
      obtain ⟨y, hy, rfl⟩ := hx
      let a := X.normalizerMonoidHom ⟨g, hg⟩
      have ha : a y ∈ pCore 2 X := characteristic_iff_le_comap.mp inferInstance a hy
      exact ⟨a y, ha, rfl⟩
  have hcomm : ⁅B, X⁆ ≤ X.pCoreIn 2 :=
    (commutator_mono hB le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hcore)
  let _ : MulDistribMulAction B X := conjMulDistribMulActionOfLeNormalizer B X hnorm
  let _ : IsInvariant B X (pCore 2 X) := isInvariant_of_characteristic _
  let _ : Group.IsNilpotent (pCore 2 X) := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
  have hcop : Nat.Coprime (Nat.card B) (Nat.card (pCore 2 X)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
    rw [hn]
    exact (Nat.coprime_two_right.mpr hodd).pow_right n
  have htriv (b : B) (x : X) : x⁻¹ * (b • x) ∈ pCore 2 X := by
    have hh : ⁅(x : G)⁻¹, (b : G)⁆ ∈ X.pCoreIn 2 := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator (X.inv_mem x.property) b.property)
    obtain ⟨q, hq, he⟩ := hh
    have heq : q = x⁻¹ * (b • x) := by
      apply Subtype.ext
      change (q : G) = (x : G)⁻¹ * ((b : G) * (x : G) * (b : G)⁻¹)
      simpa only [Subgroup.subtype_apply, commutatorElement_def, inv_inv, mul_assoc] using he
    exact heq ▸ hq
  let C₀ := FixedPoints.subgroup B X
  let C := X ⊓ centralizer (B : Set G)
  have hfixed (x : C₀) : (x.val : G) ∈ centralizer (B : Set G) := by
    apply mem_centralizer_iff.mpr
    intro b hb
    have hh := congrArg (fun x : X => (x : G)) (x.property (⟨b, hb⟩ : B))
    change b * (x.val : G) * b⁻¹ = x.val at hh
    have hh' := congrArg (fun z : G => z * b) hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh'
  let f : C₀ →* C := (X.subtype.comp C₀.subtype).codRestrict C
    (fun x => ⟨x.val.property, hfixed x⟩)
  have hcover := Theory.GroupAction.solvableResidual_fixedPoints_mul_eq_univ (A := B) (pCore 2 X) inferInstance hcop htriv
  apply Set.Subset.antisymm
  · intro x hx
    have hm : (⟨x, hx⟩ : X) ∈
        ((solvableResidual C₀).map C₀.subtype : Set X) * (pCore 2 X : Set X) := by
      rw [hcover]
      trivial
    obtain ⟨r, ⟨r₀, hr₀, rfl⟩, q, hq, he⟩ := hm
    refine ⟨r₀.val.val, ⟨f r₀, ?_, rfl⟩, q.val, ⟨q, hq, rfl⟩, ?_⟩
    · exact map_solvableResidual_le f (mem_map_of_mem f hr₀)
    · exact congrArg Subtype.val he
  · rintro _ ⟨r, ⟨r₀, _, rfl⟩, q, hq, rfl⟩
    exact X.mul_mem r₀.property.1 (pCoreIn_le 2 X hq)

end CFSG.Quasithin.Chapter4.Section04

namespace CFSG.Quasithin.Chapter4.Section04
variable {G : Type*} [Group G] [Finite G]

/-- The generation step in the proof of 4.4.14, on the original subgroups. -/
theorem centralization_in_4_4_14 (X B V₀ T : Subgroup G) [Group.IsPerfect X]
    (hB : B ≤ sectionCentralizer X) (hodd : Odd (Nat.card B))
    (hcore : X.pCoreIn 2 ≤ centralizer (V₀ : Set G))
    (hseed : V₀ ⊓ centralizer (T : Set G) ≤ centralizer (B : Set G))
    (hgen : V₀ = conjugateSpanBy (V₀ ⊓ centralizer (T : Set G)) X) :
    V₀ ≤ centralizer (B : Set G) ∧ ⁅V₀, X⁆ ≤ centralizer (B : Set G) := by
  let Z := V₀ ⊓ centralizer (T : Set G)
  let C := X ⊓ centralizer (B : Set G)
  let L := (solvableResidual C).map C.subtype
  have hLX : L ≤ X := (map_subtype_le _).trans inf_le_left
  have hLB : L ≤ centralizer (B : Set G) := (map_subtype_le _).trans inf_le_right
  have hcover : (X : Set G) = (L : Set G) * (X.pCoreIn 2 : Set G) :=
    perfect_centralizer_cover X B hB hodd
  have hspan : ConjugateSpanLE Z X L := by
    intro x hx
    have hx' : x ∈ (X : Set G) := hx
    rw [hcover] at hx'
    obtain ⟨l, hl, q, hq, he⟩ := hx'
    refine ⟨l, ⟨hLX hl, hl⟩, q, ⟨pCoreIn_le 2 X hq, ?_⟩, he⟩
    exact hgen ▸ hcore hq
  have hV : V₀ ≤ centralizer (B : Set G) := by
    rw [hgen]
    exact hspan.span_le.trans
      (conjugateSpanBy_le hseed (hLB.trans (centralizer (B : Set G)).le_normalizer))
  refine ⟨hV, le_trans ?_ hV⟩
  apply le_normalizer_iff_commutator_le_left.mp
  rw [hgen]
  exact le_normalizer_conjugateSpanBy Z X

end CFSG.Quasithin.Chapter4.Section04
