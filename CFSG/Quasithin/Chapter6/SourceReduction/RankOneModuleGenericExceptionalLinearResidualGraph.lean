module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericCartan
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterE.Section02.Structure.LinearThree.Source
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.UniqueMaximalQuotient

/-!
# The actual diagram actor on the exceptional linear residual

Unique maximality above the original Sylow subgroup survives the quotient
by O₂(H). The embedded O²(H) then has its actual PSL₃(4) quotient as a normal
subgroup. Sylow conjugacy aligns its intersection with the standard unipotent
group; if every Sylow actor preserved the two parabolic types, both parabolics
would lie in the unique maximal subgroup, contradicting their generation.

The resulting witness keeps the quotient isomorphism and both conjugation
identities. Its transport to G uses the literal inclusion H → G. It proves
the diagram clause needed in 5.1.10(3), without assuming either maximality
in L(G,T) or nonfaithfulness. Those further assertions need the independent
embedding and FSU exclusions in 5.1.12 and 3.2.5,8,9.

Source: Aschbacher–Smith, E.2.2(2b), 5.1.10(3) and the opening of 5.1.14,
printed pp.215–216,634,638 (refs/quasithin.pdf).
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree.OuterExtensions
open Matrix.PSL3Even.MinimalParabolicWitness
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric

/-- A literal Sylow actor, lifted on K and marked on K/O₂(K), which moves
an actual parabolic conjugacy class of PSL₃(4). -/
@[expose] def HasLinearFourGraphAction {G : Type*} [Group G]
    (S K : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ e : (K ⧸ pCore 2 K) ≃* PSL(3,F),
      ∃ t ∈ S, ∃ a : MulAut K, ∃ b : MulAut PSL(3,F),
        (∀ k : K, (a k : G) = t * k * t⁻¹) ∧
        (∀ k : K, e (QuotientGroup.mk' (pCore 2 K) (a k)) =
          b (e (QuotientGroup.mk' (pCore 2 K) k))) ∧ b ∉ diagramTrivial F

private theorem graph_of_unique {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (K : Subgroup X) [K.Normal]
    (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup X) ⊤)
    (hlinear : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    HasLinearFourGraphAction (S : Subgroup X) K := by
  obtain ⟨F, hF, hfin, hc, ⟨e⟩⟩ := hlinear
  let q := QuotientGroup.mk' (pCore 2 X)
  let J := K.map q
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  let j := (inferInstance : K.Normal).isSubnormal.quotientCoreImageEquiv 2
  let e₀ := j.symm.trans e
  have hJQ : J ⊔ (Q : Subgroup (X ⧸ pCore 2 X)) = ⊤ := by
    change K.map q ⊔ (S : Subgroup X).map q = ⊤
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hQ := hasUniqueMaximalOver_map_of_surjective q (QuotientGroup.mk'_surjective _)
    (show q.ker ≤ (S : Subgroup X) by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S) hu
  obtain ⟨g, hg⟩ := ChapterE.Structure.LinearThree.exists_alignment F (n := 2)
    (by decide) hc J e₀ Q
  let e₁ := e₀.trans (MulAut.conj g)
  obtain ⟨M, hM, _⟩ := hQ.2
  obtain ⟨⟨t, ht, hswap⟩, _⟩ := diagram_and_borel F J e₁ (n := 2) (by decide) hc
    (Q : Subgroup (X ⧸ pCore 2 X)) M hJQ hg hQ ⟨hM.1, hM.2.isCoatom⟩
  obtain ⟨s, hs, rfl⟩ := ht
  let a : MulAut K := MulAut.conjNormal s
  let e₂ := j.trans e₁
  refine ⟨F, hF, hfin, hc, e₂, s, hs, a, modelAction F J e₁ (q s), ?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k
    change e₂ (QuotientGroup.mk' (pCore 2 K) (a k)) =
      e₁ (MulAut.conjNormal (q s) (e₁.symm (e₂ (QuotientGroup.mk' (pCore 2 K) k))))
    change e₁ (j (QuotientGroup.mk' (pCore 2 K) (a k))) =
      e₁ (MulAut.conjNormal (q s) (e₁.symm (e₁ (j (QuotientGroup.mk' (pCore 2 K) k)))))
    rw [e₁.symm_apply_apply]
    apply congrArg e₁
    apply Subtype.ext
    change q (s * k * s⁻¹) = q s * q k * (q s)⁻¹
    simp only [map_mul, map_inv]
  · intro hd
    apply hswap
    change modelAction F J e₁ (q s) ∈ (diagramAction F (n := 2) (by decide) hc).ker
    rwa [diagramAction_ker]

/-- Injective ambient transport preserves both original conjugation identities. -/
theorem HasLinearFourGraphAction.map {G G' : Type*} [Group G] [Group G']
    {S K : Subgroup G} (h : HasLinearFourGraphAction S K)
    (f : G →* G') (hf : Function.Injective f) :
    HasLinearFourGraphAction (S.map f) (K.map f) := by
  obtain ⟨F, hF, hfin, hc, e, t, ht, a, b, ha, hb, hd⟩ := h
  let i := K.equivMapOfInjective f hf
  let j := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map f)) i (pCore_map_iso 2 i)
  refine ⟨F, hF, hfin, hc, j.symm.trans e, f t, mem_map_of_mem f ht,
    MulAut.congr i a, b, ?_, ?_, hd⟩
  · intro k'
    obtain ⟨k, rfl⟩ := i.surjective k'
    change f (a (i.symm (i k))) = f t * (i k : G') * (f t)⁻¹
    rw [i.symm_apply_apply]
    change f (a k : G) = f t * f k * (f t)⁻¹
    rw [ha]
    simp only [map_mul, map_inv]
  · intro k'
    obtain ⟨k, rfl⟩ := i.surjective k'
    change e (j.symm (QuotientGroup.mk' _ (i (a (i.symm (i k)))))) =
      b (e (j.symm (QuotientGroup.mk' _ (i k))))
    rw [i.symm_apply_apply]
    change e (j.symm (j (QuotientGroup.mk' _ (a k)))) =
      b (e (j.symm (j (QuotientGroup.mk' _ k))))
    simpa only [j.symm_apply_apply] using hb k

/-- The original H* and linear residual quotient force nontrivial diagram action.
No assertion about maximal local components or FSU modules is used. -/
theorem linear_residual_graph_action {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {M H : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    HasLinearFourGraphAction (T : Subgroup G) (residual H) := by
  let S := T.subtype hH.1.1.2
  obtain ⟨B, ⟨hB, hTB⟩, hm⟩ := Chapter3.HStar.unique_maximal_subgroup T hTM hH
  have hSB : (S : Subgroup H) ≤ B := by
    intro s hs
    obtain ⟨b, hb, he⟩ := hTB hs
    exact H.subtype_injective he ▸ hb
  have hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤ := by
    refine ⟨hSB.trans_lt hB.lt_top, B, ⟨hSB, hB.covBy_top⟩, ?_⟩
    intro C hC
    apply hm C
    refine ⟨hC.2.isCoatom, ?_⟩
    intro t ht
    exact ⟨⟨t, hH.1.1.2 ht⟩, hC.1 ht, rfl⟩
  have hg := (graph_of_unique S (pResidual 2 H) (pResidual_sup_sylow_eq_top S)
    hu hlinear).map H.subtype H.subtype_injective
  change HasLinearFourGraphAction (((T : Subgroup G).subgroupOf H).map H.subtype)
    (residual H) at hg
  rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hg

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
