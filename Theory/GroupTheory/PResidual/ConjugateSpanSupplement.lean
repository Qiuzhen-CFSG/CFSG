module
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Generating a p-perfect subgroup with a p-group supplement

If XQ=Y, Q is a p-group contained in C, and C normalizes the p-perfect
Y, then the C-conjugates of X generate Y. Their span is normal in Y,
and the quotient is a p-group image of Q, so p-perfectness kills it.

Source application: the cubic residual Y₂ and C_M(V) in the full-module
comparison of Aschbacher--Smith 15.2.5, printed p.1108.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A p-group supplement inside the actor suffices for conjugate generation. -/
theorem conjugateSpan_eq_of_pPerfect_supplement
    {p : ℕ} [Fact p.Prime] (Y X C Q : Subgroup G)
    (hp : IsPPerfect p Y) (hQ : IsPGroup p Q)
    (hs : X ⊔ Q = Y) (hQC : Q ≤ C)
    (hCY : C ≤ normalizer (Y : Set G)) : conjugateSpanBy X C = Y := by
  let L := conjugateSpanBy X C
  have hXY : X ≤ Y := le_sup_left.trans_eq hs
  have hQY : Q ≤ Y := le_sup_right.trans_eq hs
  have hLY : L ≤ Y := conjugateSpanBy_le hXY hCY
  have hYL : Y ≤ normalizer (L : Set G) := by
    rw [←hs]
    exact sup_le ((le_conjugateSpanBy X C).trans L.le_normalizer)
      (hQC.trans (le_normalizer_conjugateSpanBy X C))
  let A := L.subgroupOf Y
  let : A.Normal := normal_subgroupOf_of_le_normalizer hYL
  have htop : (⊤ : Subgroup Y) ≤ A ⊔ Q.subgroupOf Y := by
    have hh : (X ⊔ Q).subgroupOf Y = ⊤ := by rw [hs,subgroupOf_self]
    rw [←hh,subgroupOf_sup hXY hQY]
    exact sup_le_sup (comap_mono (le_conjugateSpanBy X C)) le_rfl
  have hpTop : IsPPerfect p (⊤ : Subgroup Y) := hp.of_surjective
    (Subgroup.topEquiv (G := Y)).symm.toMonoidHom (Subgroup.topEquiv (G := Y)).symm.surjective
  have htopA := le_normal_of_isPPerfect_of_le_sup_pGroup (⊤ : Subgroup Y) A
    (Q.subgroupOf Y) hpTop hQ.comap_subtype htop
  apply le_antisymm hLY
  intro y hy
  exact htopA (show (⟨y,hy⟩ : Y) ∈ (⊤ : Subgroup Y) from mem_top _)

end Subgroup
