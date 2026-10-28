module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.Source
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric.FullAction

/-!
# Original paired symmetric-five Thompson and Baumann images

The actual stable offender family and prescribed Sylow exchange activate both
natural factors. The class-sum section lifts their fixed vectors, so Baumann
fixes those lifts; the paired pointwise-fixer theorem then identifies its image
with the same product of transposition four-groups. This lower source theorem
serves both C.1.28 block selection and the original E.2.3 application.

Source: Aschbacher–Smith B.6.10, C.1.24 and E.2.3, pp.117,130–131,216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.SymmetricFive.Paired
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction BinaryPermutation
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
theorem thompson_of_source_model
    (T : Sylow 2 G)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    ∃ a b : Equiv.Perm (Fin 5), (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
            c.action.groupEquiv.symm.toMonoidHom) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  apply ChapterC.SymmetricFive.Paired.source_thompson_images T U q hq hker
    (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hJ Y le_rfl d c
  obtain ⟨t,h₁,h₂⟩ := hexchange
  have hm₁ := congrArg (map Y.subtype) h₁
  have hm₂ := congrArg (map Y.subtype) h₂
  have hc : Y.subtype.comp (MulAut.conjNormal (t:H)).toMonoidHom =
      (MulAut.conj (t:H)).toMonoidHom.comp Y.subtype := by ext; rfl
  rw [map_map,hc,←map_map] at hm₁ hm₂
  refine ⟨t,?_,?_⟩
  · rw [←map_map,c.first_eq,←map_map,c.second_eq]
    exact hm₁
  · rw [←map_map,c.second_eq,←map_map,c.first_eq]
    exact hm₂

omit [Finite G] in
private theorem thompson_le_baumann (R : Subgroup G) :
    elementaryAbelianMaxJ R ≤ baumann R := by
  apply le_inf (sSup_le fun _ hB => hB.1)
  apply le_centralizer_iff.mpr
  intro x hx
  exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2

theorem thompson_baumann_of_source_model
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (baumann (T : Subgroup G)).map q ∧
    ∃ a b : Equiv.Perm (Fin 5), (baumann (T : Subgroup G)).map q =
      (((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
        ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
          ((offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype.comp
            c.action.groupEquiv.symm.toMonoidHom) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  let e := c.action.groupEquiv
  let j := Y.subtype.comp e.symm.toMonoidHom
  let σ := α.comp j
  have he (g : FiveCentralExtension.Sym × FiveCentralExtension.Sym) (v : Additive U) :
      c.symmetricCoreMap (σ g v) = FivePair.action g (c.symmetricCoreMap v) := by
    simpa only [σ,j,e,α,Y,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply] using c.symmetricCoreMap_action (e.symm g) v
  have hk (v : Additive U) (hv : c.symmetricCoreMap v = 0)
      (g : FiveCentralExtension.Sym × FiveCentralExtension.Sym) : σ g v = v := by
    have hfix : v ∈ Representation.invariants (α.comp Y.subtype) := by
      rw [←c.symmetricCoreMap_ker]
      exact hv
    exact hfix (e.symm g)
  obtain ⟨s,hs,hse⟩ := FivePair.exists_section σ c.symmetricCoreMap
    c.symmetricCoreMap_surjective he hk
  obtain ⟨hcoreY,ρ,hfaith,hfull,hnat⟩ := c.source_full_faithful_action T hP U hU hJ q hq hker d
  obtain ⟨a,b,ha⟩ := thompson_of_source_model T U hU hJ q hq hker d c hexchange
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let E := U ⊓ centralizer (J : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ U from inf_le_left)
  have hUT : U ≤ T := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
  have hEa : E ≤ omegaOneCenterAmbient J :=
    elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G) E
      (inf_le_left.trans hUT) inf_le_right
  have hupper : (baumann (T : Subgroup G)).map q ≤ J.map q := by
    rw [show J.map q = _ from ha]
    rintro x ⟨g,hg,rfl⟩
    apply ChapterC.SymmetricFive.Paired.source_mem_transposition_product Y (α.comp Y.subtype)
      d c hcoreY ρ hfaith hnat (q g) a b
    intro v hv
    let w := s v
    have hwfix : w ∈ fixedSpace α (J.map q) := by
      intro z
      have hz := (SetLike.ext_iff.mp ha z.val).mp z.property
      obtain ⟨k,hk,hkz⟩ := hz
      change α z.val (s v) = s v
      rw [←hkz]
      change σ k (s v) = s v
      rw [←hse]
      exact congrArg s (hv ⟨k,hk⟩)
    have hwE : (w.toMul : G) ∈ E :=
      ⟨w.toMul.property, (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker J w).mp hwfix⟩
    have hgfix : g ∈ centralizer (omegaOneCenterAmbient J : Set G) := hg.2
    have hcomm := mem_centralizer_iff.mp hgfix _ (hEa hwE)
    have hwg : α (q g) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply, ←hcomm, mul_inv_cancel_right]
    have hh := congrArg c.symmetricCoreMap hwg
    change c.symmetricCoreMap (α (q g) (s v)) = c.symmetricCoreMap (s v) at hh
    rw [hfull,hs] at hh
    exact hh
  have heq : J.map q = (baumann (T : Subgroup G)).map q :=
    le_antisymm (map_mono (thompson_le_baumann _)) hupper
  exact ⟨heq,a,b,heq.symm.trans ha⟩
end CFSG.Quasithin.ChapterC.SymmetricFive.Paired
