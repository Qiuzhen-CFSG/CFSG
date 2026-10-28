module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.Covering
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Decomposition control between the two B.1.10 inductions

We work with a supplied B.1.9 `Decomposition`, not an assertion that the
source theorem already holds. A quasisimple or order-three subgroup K of J
lies in the image of the intrinsic two-residual O²(J). Each coordinate
projection of O²(J) lies in O²(Gᵢ). The actual model Gᵢ ≃ S₃ gives order six,
while the inclusion-compatible odd-core model gives |O(Gᵢ)| = 3. Thus
Gᵢ/O(Gᵢ) has order two and O²(Gᵢ) lies in the cyclic odd core.

Consequently these coordinates commute with each Fᵢ. The residual direct
factor commutes with all the Gᵢ, as expressed by the product coordinates.
The single-coordinate formulas for `groupProduct` and `oddProduct` transport
this to [K,F] = 1 in G. Surjectivity and the multiplication formula for
`fittingProduct` give F(G) = F ∨ E for the literal E = C_F(G)(J*).
Hence [F(G),K] ≠ 1 forces [E,K] ≠ 1.

`bestOffender_decomposition_control` supplies both facts for the B.1.10
consumer, deriving K ≤ J from K = [K,A] and the actual best offender A.
Its noncentrality conclusion is the premise of the existing
`MovedFactors.centralizer_reduction`; final source assembly retains the
construction of the B.1.9 decomposition and the induction hypothesis.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.1.9(1–2)
and the middle paragraph of B.1.10, printed pp.71–72 (PDF pp.82–83).
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
universe u v
variable {G : Type u} {V : Type v} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem factor_twoResidual_top [Finite G] (K : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) : pResidual 2 K = ⊤ := by
  rcases hK with hK | hK
  · let : IsQuasisimple K := hK
    apply (pResidual_eq_top_iff 2 K).mpr
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  · apply top_unique
    intro k _
    apply mem_pResidual_of_orderOf_coprime
    apply (show Nat.Coprime 2 3 by decide).of_dvd_right
    simpa only [hK] using orderOf_dvd_natCard k

/-- The source containment uses the residual intrinsic to J and its subtype map. -/
theorem factor_le_offender_twoResidual [Finite G] (K : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) (hKJ : K ≤ offenderSubgroup ρ) :
    K ≤ (pResidual 2 (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype := by
  intro k hk
  refine ⟨⟨k, hKJ hk⟩, ?_, rfl⟩
  exact map_pResidual_le 2 (inclusion hKJ)
    (mem_map.mpr ⟨⟨k, hk⟩, by rw [factor_twoResidual_top K hK]; trivial, rfl⟩)

private theorem oddCore_card (d : Decomposition ρ) (i : Fin d.count) :
    Nat.card (pPrimeCore 2 (d.factor i)) = 3 := by
  have he := (pPrimeCore 2 (d.factor i)).equivMapOfInjective
    (d.factor i).subtype (d.factor i).subtype_injective
  calc
    Nat.card (pPrimeCore 2 (d.factor i)) =
        Nat.card ((pPrimeCore 2 (d.factor i)).map (d.factor i).subtype) :=
      Nat.card_congr he.toEquiv
    _ = Nat.card (d.oddFactor i) := by rw [d.oddFactor_eq i]
    _ = 3 := by
      rw [Nat.card_congr (d.oddFactorModel i).toEquiv]
      simp

private theorem factor_twoResidual_le_oddCore (d : Decomposition ρ) (i : Fin d.count) :
    pResidual 2 (d.factor i) ≤ pPrimeCore 2 (d.factor i) := by
  apply sInf_le
  refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
  have hc : Nat.card (d.factor i) = 6 := by
    rw [Nat.card_congr (d.factorModel i).toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hq := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 (d.factor i))
  rw [hc, oddCore_card ρ d i] at hq
  omega

private theorem fittingMoved_le_of_oddFactors (d : Decomposition ρ) (C : Subgroup G)
    (hC : ∀ i, d.oddFactor i ≤ C) : fittingMoved ρ ≤ C := by
  intro f hf
  obtain ⟨x, hx⟩ := d.oddProduct.surjective ⟨f, hf⟩
  let φ := (fittingMoved ρ).subtype.comp d.oddProduct.toMonoidHom
  have hm : x ∈ C.comap φ := by
    apply pi_mem_of_mulSingle_mem
    intro i
    change (d.oddProduct (Pi.mulSingle i (x i)) : G) ∈ C
    rw [d.oddProduct_single]
    exact hC i (x i).property
  change (d.oddProduct x : G) ∈ C at hm
  simpa only [hx] using hm

private theorem offender_twoResidual_centralizes_oddFactor (d : Decomposition ρ)
    (i : Fin d.count) :
    (pResidual 2 (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype ≤
      centralizer (d.oddFactor i : Set G) := by
  classical
  rintro _ ⟨k, hk, rfl⟩ y hy
  rw [d.oddFactor_eq i] at hy
  obtain ⟨a, ha, rfl⟩ := hy
  let π : offenderSubgroup ρ →* d.factor i :=
    (Pi.evalMonoidHom (fun j => d.factor j) i).comp
      ((MonoidHom.fst _ _).comp d.groupProduct.symm.toMonoidHom)
  let z := d.groupProduct.symm k
  have hz : z.1 i ∈ pPrimeCore 2 (d.factor i) :=
    factor_twoResidual_le_oddCore ρ d i
      (map_pResidual_le 2 π (mem_map.mpr ⟨k, hk, rfl⟩))
  let : IsCyclic (pPrimeCore 2 (d.factor i)) :=
    isCyclic_of_prime_card (oddCore_card ρ d i)
  have hc : a * z.1 i = z.1 i * a :=
    (pPrimeCore 2 (d.factor i)).le_centralizer hz a ha
  have he : (Pi.mulSingle i a, 1) * z = z * (Pi.mulSingle i a, 1) := by
    apply Prod.ext
    · funext j
      by_cases hji : j = i
      · subst j
        simpa only [Prod.fst_mul, Pi.mul_apply, Pi.mulSingle_eq_same] using hc
      · simp [Pi.mulSingle_eq_of_ne hji]
    · simp
  have hh := congrArg (fun t => (d.groupProduct t : G)) he
  simpa only [map_mul, Subgroup.coe_mul, Subgroup.subtype_apply, d.groupProduct_single,
    z, d.groupProduct.apply_symm_apply] using hh

/-- B.1.9(1–2) makes the intrinsic two-residual of J centralize F. -/
theorem offender_twoResidual_centralizes_fittingMoved (d : Decomposition ρ) :
    (pResidual 2 (offenderSubgroup ρ)).map (offenderSubgroup ρ).subtype ≤
      centralizer (fittingMoved ρ : Set G) := by
  apply le_centralizer_iff.mpr
  apply fittingMoved_le_of_oddFactors ρ d
  intro i
  exact le_centralizer_iff.mp (offender_twoResidual_centralizes_oddFactor ρ d i)

/-- Every quasisimple or cubic subgroup of J centralizes F. -/
theorem factor_centralizes_fittingMoved [Finite G] (d : Decomposition ρ) (K : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) (hKJ : K ≤ offenderSubgroup ρ) :
    K ≤ centralizer (fittingMoved ρ : Set G) :=
  (factor_le_offender_twoResidual ρ K hK hKJ).trans
    (offender_twoResidual_centralizes_fittingMoved ρ d)

/-- F(G) is the join of the two literal factors in the supplied decomposition. -/
theorem fitting_eq_sup_centralizer (d : Decomposition ρ) :
    fittingSubgroup G = fittingMoved ρ ⊔
      (fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨f, c⟩, he⟩ := d.fittingProduct.surjective ⟨g, hg⟩
    have hm := d.fittingProduct_apply f c
    rw [he] at hm
    change g = (f : G) * (c : G) at hm
    rw [hm]
    exact mul_mem (mem_sup_left f.property) (mem_sup_right c.property)
  · exact sup_le ((fittingMoved_le ρ).trans inf_le_left) inf_le_left

/-- A failure to centralize F(G) must occur on the literal E = C_F(G)(J*). -/
theorem fitting_centralizer_commutator_ne_bot [Finite G] (d : Decomposition ρ) (K : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) (hKJ : K ≤ offenderSubgroup ρ)
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥) :
    ⁅fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G), K⁆ ≠ ⊥ := by
  intro hz
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rw [fitting_eq_sup_centralizer ρ d]
  exact sup_le (le_centralizer_iff.mp (factor_centralizes_fittingMoved ρ d K hK hKJ))
    (commutator_eq_bot_iff_le_centralizer.mp hz)

/-- The B.1.10 application discharges K ≤ J from the actual best offender. -/
theorem bestOffender_decomposition_control [Finite G] (d : Decomposition ρ) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsBestOffender ρ A) (hKA : K = ⁅K, A⁆)
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥) :
    K ≤ centralizer (fittingMoved ρ : Set G) ∧
      ⁅fittingSubgroup G ⊓ centralizer (minimalGenerated ρ : Set G), K⁆ ≠ ⊥ := by
  have hKJ := moved_by_best_le ρ hA hKA
  exact ⟨factor_centralizes_fittingMoved ρ d K hK hKJ,
    fitting_centralizer_commutator_ne_bot ρ d K hK hKJ hne⟩

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
