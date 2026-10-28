module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus


/-!
# Constructing every G.9.3 application hypothesis

In a minimal normal join of two distinct components, neither component can
be normal. Some conjugate of the first is therefore different from it.
A third component contained in their join would commute with the entire
join, contradicting perfectness. Consequently an actual ambient element
interchanges the components. Its linear operator intertwines the two
restrictions, providing the required quasiequivalence.

Together with the original-actor degree and noncentrality reductions, this
constructs `ComponentHypothesis`. The last construction uses the actual
centralizer as the SQTK cover of `H/O₂(H)`, with its canonical projection.
No classification alternative or exclusion is assumed or asserted here.

Source: Aschbacher–Smith, 15.3.58, printed p.1149, applying G.9.1 and G.9.3,
printed pp.351–354. The component commutation theorem is the general group
calculus used in this source application.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
open Subgroup Representation Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09
open scoped IsMulCommutative
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {K : Subgroup H}

private theorem pair_conjugate (hK : ComponentData ρ K)
    {L L₂ : Subgroup H} (hL : IsComponent H L) (hL₂ : IsComponent H L₂)
    (hsL : IsSimpleGroup L) (hne : L ≠ L₂) (he : K = L ⊔ L₂) :
    ∃ g : H, L.map (MulAut.conj g).toMonoidHom = L₂ := by
  classical
  let : K.Normal := hK.normal
  let : IsSimpleGroup L := hsL
  have hLbot : L ≠ ⊥ := (nontrivial_iff_ne_bot L).mp inferInstance
  have hn : ¬ L.Normal := by
    intro hn
    have hLK : L ≤ K := he ▸ le_sup_left
    have heq : L = K := (hK.minimal L hn hLK).resolve_left hLbot
    exact hne (hL₂.eq_of_le hL (by rw [heq, he]; exact le_sup_right)).symm
  obtain ⟨g, hg⟩ : ∃ g : H, L.map (MulAut.conj g).toMonoidHom ≠ L := by
    by_contra! h
    exact hn (normal_iff_map_conj_eq.mpr h)
  refine ⟨g, ?_⟩
  let M := L.map (MulAut.conj g).toMonoidHom
  have hM : IsComponent H M := hL.map_conj g
  by_contra hM₂
  have hMK : M ≤ K := by
    exact (map_mono (show L ≤ K from he ▸ le_sup_left)).trans
      (Subgroup.Normal.map_conj_eq K g).le
  have hc : ⁅K, M⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [he]
    exact sup_le
      (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hg.symm))
      (commutator_eq_bot_iff_le_centralizer.mp (hL₂.commutator_eq_bot_of_ne hM (Ne.symm hM₂)))
  have hb : ⁅M, M⁆ = ⊥ := le_bot_iff.mp ((commutator_mono hMK le_rfl).trans hc.le)
  let : IsQuasisimple M := hM.2
  rw [commutator_eq_self] at hb
  let : Nontrivial M := ((MulAut.conj g).subgroupMap L).symm.toEquiv.nontrivial
  exact (nontrivial_iff_ne_bot M).mp inferInstance hb

private theorem conjugate_quasiequivalent (L : Subgroup H) (g : H) :
    Quasiequivalent (ρ.comp L.subtype)
      (ρ.comp (L.map (MulAut.conj g).toMonoidHom).subtype) := by
  refine ⟨(MulAut.conj g).subgroupMap L,
    LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g), ?_⟩
  intro l w
  change ρ g (ρ (l : H) w) = ρ (g * l * g⁻¹) (ρ g w)
  simp [map_mul, Module.End.mul_apply]

private theorem quasiequivalent_symm {D M : Type*} [Group D]
    [AddCommGroup M] [Module (ZMod 2) M]
    {σ : Representation (ZMod 2) D M} (h : Quasiequivalent ρ σ) :
    Quasiequivalent σ ρ := by
  obtain ⟨e, f, hf⟩ := h
  refine ⟨e.symm, f.symm, ?_⟩
  intro d w
  apply f.injective
  simpa using (hf (e.symm d) (f.symm w)).symm

universe u

/-- All application hypotheses of G.9.3, with the original elementary actor.
Minimal normality supplies conjugacy and hence equivalence of the two
component restrictions; no model classification is assumed. -/
theorem SourceData.componentHypothesis
    {H : Type u} [Group H] [Finite H]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
    {v : H} {s : ℕ} {C : GroupClass.{u}}
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (hcover : Nonempty (SQTKCover C H)) :
    ∃ L : Subgroup H, ComponentHypothesis C ρ X L K (s + 1) := by
  obtain ⟨L, hL, hsL, _, he | ⟨L₂, hL₂, _, _, hne, _, he⟩⟩ := hK.factors
  · refine ⟨L, { h.setup with
      quotient := hcover
      component := hL
      noncentral := ?_
      normal_H := hK.normal
      irreducible := hK.irreducible
      components := Or.inl he }⟩
    exact he ▸ h.actor_noncentral hK
  · obtain ⟨g, hg⟩ := pair_conjugate hK hL hL₂ hsL hne he
    have hq : Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) := by
      rw [← hg]
      exact conjugate_quasiequivalent L g
    by_cases hc : ⁅L, X⁆ = ⊥
    · refine ⟨L₂, { h.setup with
        quotient := hcover
        component := hL₂
        noncentral := ?_
        normal_H := hK.normal
        irreducible := hK.irreducible
        components := Or.inr ⟨L, hL, by rw [he, sup_comm],
          Or.inl (quasiequivalent_symm hq)⟩ }⟩
      intro hc₂
      apply h.actor_noncentral hK
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [he]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hc)
        (commutator_eq_bot_iff_le_centralizer.mp hc₂)
    · exact ⟨L, { h.setup with
        quotient := hcover
        component := hL
        noncentral := hc
        normal_H := hK.normal
        irreducible := hK.irreducible
        components := Or.inr ⟨L₂, hL₂, he, Or.inl hq⟩ }⟩

/-- The original centralizer is an actual SQTK cover of its literal two-core
quotient. No closure of quasithinness under quotients is presumed. -/
def actorSQTKCover {G : Type u} [Group G] [Finite G]
    (C : GroupClass.{u}) (Z : Subgroup G)
    (h : IsSQTK C (centralizerH Z)) : SQTKCover C (ActorQuotient Z) where
  Cover := centralizerH Z
  sqtk := h
  projection := QuotientGroup.mk' (pCore 2 (centralizerH Z))
  surjective := QuotientGroup.mk'_surjective _

/-- The complete G.9.3 input for the faithful action on the literal `U/Z`,
including the quotient presentation from the original centralizer. -/
theorem source_componentHypothesis {G : Type u} [Group G] [Finite G]
    (C : GroupClass.{u}) (Z ZS : Subgroup G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    {X K : Subgroup (ActorQuotient Z)} {T : Sylow 2 (ActorQuotient Z)}
    {v : ActorQuotient Z} {s : ℕ}
    (h : SourceData (actorRepresentation Z ZS hkernel) X T v s)
    (hK : ComponentData (actorRepresentation Z ZS hkernel) K)
    (hcover : IsSQTK C (centralizerH Z)) :
    ∃ L : Subgroup (ActorQuotient Z),
      ComponentHypothesis C (actorRepresentation Z ZS hkernel) X L K (s + 1) :=
  h.componentHypothesis hK ⟨actorSQTKCover C Z hcover⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
