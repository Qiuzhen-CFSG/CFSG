module

public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Isomorphism transport for short groups and blocks

All clauses of C.1.7 are preserved by an actual group isomorphism. In particular,
the p-core commutator U and its intersection with the center transport as
subgroups; mapping normal subgroups in both directions preserves the full
irreducibility interval. Subnormality transports under the ambient isomorphism,
so images of blocks are blocks.

This supports the application of C.1.9 to conjugates inside the local overgroup
in the proof of 1.3.8. Source: Aschbacher–Smith, combined manuscript of
1 March 2004, C.1.7–9, printed p.123, and proof of 1.3.8, printed p.514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC

section Transport
variable {A B : Type*} [Group A] [Group B]

private theorem fitting_map_le (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

private theorem fitting_map (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom = fittingSubgroup B := by
  apply le_antisymm (fitting_map_le e)
  have h := map_mono (f := e.toMonoidHom) (fitting_map_le e.symm)
  simpa [map_map] using h

private theorem layer_map_le (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom ≤ componentLayer B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro N hN
  exact map_le_iff_le_comap.mp (le_sSup (hN.map_equiv e))

private theorem layer_map (e : A ≃* B) :
    (componentLayer A).map e.toMonoidHom = componentLayer B := by
  apply le_antisymm (layer_map_le e)
  have h := map_mono (f := e.toMonoidHom) (layer_map_le e.symm)
  simpa [map_map] using h

private theorem generalizedFitting_map (e : A ≃* B) :
    (generalizedFitting A).map e.toMonoidHom = generalizedFitting B := by
  rw [generalizedFitting, generalizedFitting, Subgroup.map_sup, fitting_map, layer_map]

private theorem blockU_map (e : A ≃* B) :
    (blockU A).map e.toMonoidHom = blockU B := by
  rw [blockU, map_commutator, pCore_map_iso,
    map_top_of_surjective _ e.surjective, blockU]

private theorem center_map (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.centerCongr e ⟨x, hx⟩).property
  · intro x hx
    exact ⟨e.symm x, (Subgroup.centerCongr e).symm ⟨x, hx⟩ |>.property,
      e.apply_symm_apply x⟩

private theorem blockU_inf_center_map (e : A ≃* B) :
    (blockU A ⊓ center A).map e.toMonoidHom = blockU B ⊓ center B := by
  rw [map_inf _ _ _ e.injective, blockU_map, center_map]

private theorem irreducible_of_equiv (e : A ≃* B) (h : BlockModuleIrreducible A) :
    BlockModuleIrreducible B := by
  constructor
  · rw [← blockU_inf_center_map e, ← blockU_map e]
    exact (map_lt_map_iff_of_injective e.injective).mpr h.1
  · intro N hN hlo hhi
    have hN' := hN.map e.symm.toMonoidHom e.symm.surjective
    have hlo' : blockU A ⊓ center A ≤ N.map e.symm.toMonoidHom := by
      rw [← blockU_inf_center_map e.symm]
      exact map_mono hlo
    have hhi' : N.map e.symm.toMonoidHom ≤ blockU A := by
      rw [← blockU_map e.symm]
      exact map_mono hhi
    rcases h.2 _ hN' hlo' hhi' with hn | hn
    · left
      have hm := congrArg (Subgroup.map e.toMonoidHom) hn
      rw [blockU_inf_center_map] at hm
      simpa [map_map] using hm
    · right
      have hm := congrArg (Subgroup.map e.toMonoidHom) hn
      rw [blockU_map] at hm
      simpa [map_map] using hm

/-- Every structural clause defining a short group transports under isomorphism. -/
theorem IsShort.of_mulEquiv (h : IsShort A) (e : A ≃* B) : IsShort B := by
  let := h.finite
  let := h.elementary
  refine {
    finite := Finite.of_equiv A e.toEquiv
    twoPerfect := h.twoPerfect.of_surjective e.toMonoidHom e.surjective
    fitting := ?_
    elementary := ?_
    central := ?_
    quotient := ?_
    irreducible := irreducible_of_equiv e h.irreducible }
  · rw [← generalizedFitting_map e, h.fitting, pCore_map_iso]
  · rw [← blockU_map e]
    exact IsElementaryAbelian.map e.toMonoidHom
  · rw [← blockU_map e, ← pCore_map_iso 2 e]
    rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨y, hy, rfl⟩
    exact (map_mul e y x).symm.trans
      ((congrArg e (mem_centralizer_iff.mp (h.central hx) y hy)).trans (map_mul e x y))
  · let eqv := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    rcases h.quotient with hq | hq
    · let := hq
      exact Or.inl (IsQuasisimple.of_mulEquiv eqv)
    · exact Or.inr ((Nat.card_congr eqv.toEquiv).symm.trans hq)

/-- An ambient isomorphism transports both shortness and relative subnormality. -/
theorem IsBlock.map_equiv {G H : Type*} [Group G] [Group H]
    {K : Subgroup G} (h : IsBlock K) (e : G ≃* H) :
    IsBlock (K.map e.toMonoidHom) := by
  let := h.finite
  exact ⟨Finite.of_equiv G e.toEquiv, h.short.of_mulEquiv (e.subgroupMap K),
    h.subnormal.map e.surjective⟩

end Transport

end CFSG.Quasithin.ChapterC
