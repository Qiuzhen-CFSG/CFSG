module

public import CFSG.Quasithin.ChapterF.Section06.Basic
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Source implications for the cyclic three-core branch

This file contains the source-faithful reductions which precede the model
recognition in Lemma F.6.17.  The component extraction is kept separate from
the later Theorem B/Dickson input: it only uses the definition of the
generalized Fitting subgroup and the inclusion of the Fitting subgroup in the
odd core.  The internal product lemma records the actual subgroup embeddings,
so a later recognition theorem can transport its local actions without
replacing an internal product by an abstract order calculation.  The last
lemma is the small congruence calculation used after the local D24 step.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
§F.6, printed pp.308--309 (1 March 2004 manuscript).
-/

open Subgroup
open Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.ChapterF

variable {G : Type*} [Group G]

/-- The exact local data needed to turn the source equality
`L = K × D` into an actual internal product.  `K` and `D` are subgroups of the
ambient group; no abstract replacement of either factor is made. -/
public structure InternalCyclicFactorData where
  L : Subgroup G
  K : Subgroup G
  D : Subgroup G
  hL : L = K ⊔ D
  hdisjoint : Disjoint K D
  hcomm : K ≤ centralizer (D : Set G)
  hDcard : Nat.card D = 3

/-- The internal product and the cyclic order-three factor supplied by the
source local calculation.  The first equivalence is oriented so that the
source subgroup `L` is the domain, while the multiplication formula records
both actual embeddings. -/
public theorem InternalCyclicFactorData.exists_factor_equiv
    (d : InternalCyclicFactorData (G := G)) :
    Nonempty (d.L ≃* d.K × d.D) ∧
      Nonempty (d.D ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨e, he⟩ := Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    d.K d.D d.hdisjoint d.hcomm
  have eL : (d.L : Type _) ≃* (d.K ⊔ d.D : Subgroup G) :=
    MulEquiv.subgroupCongr d.hL
  have eL' : d.L ≃* d.K × d.D := eL.trans e.symm
  refine ⟨⟨eL'⟩, ?_⟩
  exact ⟨mulEquivOfPrimeCardEq d.hDcard (by simp)⟩

/-- If the generalized Fitting subgroup is not contained in the cyclic
three-core, while the Fitting subgroup is contained in that core, then an
actual component escapes the core.  This is the first source implication in
the proof of F.6.17; it is independent of the later component catalogue. -/
public theorem exists_component_of_sup_not_le_primeCore
    (P : Subgroup G → Prop) (F E : Subgroup G)
    (hE : E = sSup {K : Subgroup G | P K})
    (hF : F ≤ pCore 3 G)
    (hnot : ¬ F ⊔ E ≤ pCore 3 G) :
    ∃ K : Subgroup G, P K ∧ ¬ K ≤ pCore 3 G := by
  by_contra h
  push Not at h
  apply hnot
  apply sup_le hF
  rw [hE]
  apply sSup_le
  intro K hK
  exact h K hK

/- The source-facing instance of the preceding lattice argument.  Keeping
the actual `generalizedFitting` definition visible here prevents a later
recognition theorem from silently replacing `F*(G)` by an abstract carrier. -/
public theorem exists_component_of_generalizedFitting_not_le_primeCore
    [Finite G] (hfit : fittingSubgroup G ≤ pCore 3 G)
    (hnot : ¬ generalizedFitting G ≤ pCore 3 G) :
    ∃ K : Subgroup G, IsComponent G K ∧ ¬ K ≤ pCore 3 G := by
  by_contra h
  push Not at h
  apply hnot
  rw [generalizedFitting]
  apply sup_le hfit
  apply sSup_le
  intro K hK
  exact h K hK

/-- The two embedded two-residuals of a genuine Goldschmidt triple cannot
coincide.  This is the final contradiction in the `F*(G) = O₃(G)` branch of
the source proof: the residual-supplement identities would make both local
generators equal, and the common generator would be a two-group, contrary to
its actual symmetric-three quotient. -/
public theorem IsGoldschmidtTriple.embedded_twoResidual_ne
    {G₁ G₂ : Subgroup G} [Finite G] (h : IsGoldschmidtTriple G₁ G₂) :
    (pResidual 2 G₁).map G₁.subtype ≠
      (pResidual 2 G₂).map G₂.subtype := by
  intro he
  have hg₁ := h.left_residual_sup_intersection
  have hg₂ := h.right_residual_sup_intersection
  rw [← he] at hg₂
  have heq : G₁ = G₂ := hg₁.symm.trans hg₂
  obtain ⟨T, hT⟩ := h.intersection_sylow
  have hTG : G₁ = (T : Subgroup G) := by
    calc
      G₁ = G₁ ⊓ G₂ := by rw [heq, inf_idem]
      _ = (T : Subgroup G) := hT
  have hP : IsPGroup 2 G₁ := hTG ▸ T.isPGroup'
  obtain ⟨e⟩ := h.quotient_left
  have hQ : IsPGroup 2 (G₁ ⧸ pCore 2 G₁) := hP.to_quotient _
  have hQ' : IsPGroup 2 (Equiv.Perm (Fin 3)) := hQ.of_equiv e
  obtain ⟨n, hn⟩ := hQ'.exists_card_eq
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hcard] at hn
  have hthree : 3 ∣ 2 ^ n := by
    rw [← hn]
    norm_num
  have hcop : Nat.Coprime 3 (2 ^ n) := (by decide : Nat.Coprime 3 2).pow_right n
  have hone := Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hthree
  norm_num at hone

/-- The source congruence step.  The first disjunct says that the odd field
parameter is `1 mod 4`, the second that it is `-1 mod 4`; the corresponding
three-divisibility condition is retained explicitly.  Together with
`q = ±3 (mod 8)` this gives `q = ±11 (mod 24)`. -/
public theorem primePower_mod24_of_source_congruences (q : ℕ)
    (h8 : q % 8 = 3 ∨ q % 8 = 5)
    (h3 : (q % 4 = 1 ∧ q % 3 = 1) ∨ (q % 4 = 3 ∧ q % 3 = 2)) :
    q % 24 = 11 ∨ q % 24 = 13 := by
  omega

end CFSG.Quasithin.ChapterF
