module

public import Theory.Mathieu.M22.ValueBoundParabolics

/-!
# Transport of the Mathieu local pair

An isomorphism transports each overgroup, its intersection with the normal
subgroup, and its intrinsic two-core quotient. Conjugating one fixed pair
therefore gives a pair over any prescribed Sylow subgroup.

This is the transport step for Aschbacher–Smith E.4.3(2), printed pp. 241–242;
it assumes an actual initial pair and does not construct the model geometry.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22ValueBound
open Subgroup
variable {G K : Type*} [Group G] [Group K]

noncomputable def coreQuotientEquiv (e : G ≃* K) :
    (G ⧸ pCore 2 G) ≃* (K ⧸ pCore 2 K) :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

noncomputable def InnerCompatiblePair.map [Finite G] (e : G ≃* K)
    {T : Sylow 2 G} {L : Subgroup G} (d : InnerCompatiblePair T L) :
    InnerCompatiblePair (T.mapSurjective (f := e.toMonoidHom) e.surjective) (L.map e.toMonoidHom) where
  first := d.first.map e.toMonoidHom
  second := d.second.map e.toMonoidHom
  sylow_le_first := Subgroup.map_mono d.sylow_le_first
  sylow_le_second := Subgroup.map_mono d.sylow_le_second
  generate := by
    rw [← Subgroup.map_sup, d.generate, Subgroup.map_top_of_surjective _ e.surjective]
  firstQuotient := (coreQuotientEquiv (e.subgroupMap d.first).symm).trans d.firstQuotient
  secondQuotient := (coreQuotientEquiv (e.subgroupMap d.second).symm).trans d.secondQuotient
  firstInnerQuotient := (coreQuotientEquiv
    ((MulEquiv.subgroupCongr (Subgroup.map_inf d.first L e.toMonoidHom e.injective).symm).trans
      (e.subgroupMap (d.first ⊓ L)).symm)).trans d.firstInnerQuotient
  secondInnerQuotient := (coreQuotientEquiv
    ((MulEquiv.subgroupCongr (Subgroup.map_inf d.second L e.toMonoidHom e.injective).symm).trans
      (e.subgroupMap (d.second ⊓ L)).symm)).trans d.secondInnerQuotient

theorem nonempty_innerCompatiblePair_of_equiv [Finite G]
    (e : G ≃* K) (T : Sylow 2 G) (L : Subgroup G)
    (h : Nonempty (InnerCompatiblePair (T.mapSurjective (f := e.toMonoidHom) e.surjective)
      (L.map e.toMonoidHom))) : Nonempty (InnerCompatiblePair T L) := by
  let : Finite K := Finite.of_equiv G e.toEquiv
  obtain ⟨d⟩ := h
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext x
    exact e.symm_apply_apply x
  have ht : (T.mapSurjective (f := e.toMonoidHom) e.surjective).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective = T := by
    apply Sylow.ext
    change ((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom = _
    rw [Subgroup.map_map, he, Subgroup.map_id]
  have hl : (L.map e.toMonoidHom).map e.symm.toMonoidHom = L := by
    rw [Subgroup.map_map, he, Subgroup.map_id]
  exact ⟨ht ▸ hl ▸ d.map e.symm⟩

theorem nonempty_innerCompatiblePair_of_sylow [Finite G]
    (T U : Sylow 2 G) (L : Subgroup G) [L.Normal]
    (d : InnerCompatiblePair U L) : Nonempty (InnerCompatiblePair T L) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U T
  have ht : U.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective = T := by
    exact hg
  have hl : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.normal_iff_map_conj_eq.mp inferInstance g
  exact ⟨ht ▸ hl ▸ d.map (MulAut.conj g)⟩

end Sporadic.Mathieu.M22ValueBound
