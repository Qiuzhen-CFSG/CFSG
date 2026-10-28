module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveModules
public import Theory.Representation.BinaryPermutation.FiveCentralExtension.WholeQuotient
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ThompsonImage
/-!
# The original whole S₅ quotient and global Thompson image

The actual alternating moved subgroup is natural. The central three-cycle
sum extends its natural coordinates to the whole original module with exactly
the residual-fixed kernel. Its Thompson four-group and residual A₅ generate
S₅, so the original global Thompson image and offender image are both the
whole centralizer quotient. The original quotient kernel remains unchanged.

Source: Aschbacher–Smith E.2.3(1),(3), printed pp.216–217.
-/
public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.QuasisimpleSource
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary
theorem quasisimple_five_whole_quotient
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    ∃ p : G →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
      ∃ hk : p.ker = centralizer (U : Set G),
      ∃ f : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
        Function.Surjective f ∧
        (∀ g v, f (NormalElementaryQuotient.representation U p hp hk g v) =
          BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
        f.ker = fixedSpace (NormalElementaryQuotient.representation U p hp hk)
          ((pResidual 2 G).map p) := by
  let W := (⁅U,pResidual 2 G⁆ : Subgroup G)
  obtain ⟨p,hp,hkW,fW,heW⟩ :=
    quasisimple_five_source_natural_module T hP U hU hJ q hq hker hqs s e
  have hk : p.ker = centralizer (U : Set G) := hkW.trans (hU.centralizer_moved_eq U)
  let α := NormalElementaryQuotient.representation U p hp hk
  let β := NormalElementaryQuotient.representation W p hp hkW
  let i₀ : Additive W →ₗ[ZMod 2] Additive U :=
    (Subgroup.inclusion (commutator_le_left U (pResidual 2 G))).toAdditive.toZModLinearMap 2
  let i := i₀.comp fW.symm.toLinearMap
  have hi : Function.Injective i := by
    intro a b hab
    apply fW.symm.injective
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun v : Additive U => (v.toMul:G)) hab
  have he (g : Equiv.Perm (Fin 5)) (v : BinaryPermutation.core (Fin 5)) :
      i (BinaryPermutation.coreRepresentation (Fin 5) g v) = α g (i v) := by
    have hs : fW.symm (BinaryPermutation.coreRepresentation (Fin 5) g v) = β g (fW.symm v) := by
      apply fW.injective
      rw [fW.apply_symm_apply,heW,fW.apply_symm_apply]
    change i₀ (fW.symm _) = α g (i₀ (fW.symm v))
    rw [hs]
    obtain ⟨x,rfl⟩ := hp g
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((β (p x) (fW.symm v)).toMul:G) = ((α (p x) (i₀ (fW.symm v))).toMul:G)
    rw [NormalElementaryQuotient.representation_apply,NormalElementaryQuotient.representation_apply]
    rfl
  have him : (pResidual 2 G).map p = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 p hp,Equiv.Perm.twoResidual_eq_alternating]
  have hr : i.range = subspaceCommutator α ⊤ (alternatingGroup (Fin 5)) := by
    rw [←him,←NormalElementaryQuotient.commutatorSpace_eq U p hp hk]
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      exact (fW.symm w).toMul.property
    · intro hv
      let w : Additive W := Additive.ofMul ⟨v.toMul,hv⟩
      refine ⟨fW w,?_⟩
      change i₀ (fW.symm (fW w)) = v
      rw [fW.symm_apply_apply]
      rfl
  obtain ⟨f,hf,hef,hkf⟩ := BinaryPermutation.FiveCentralExtension.exists_quotient_of_natural_moved α i hi he hr
  exact ⟨p,hp,hk,f,hf,hef,by rwa [←him] at hkf⟩
theorem quasisimple_five_global_thompson_image
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5))) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = Y ∧ Y = ⊤ := by
  let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
  let J := elementaryAbelianMaxJ (⊤ : Subgroup G)
  obtain ⟨p,hp,hk,f,hf,he,hfk⟩ := quasisimple_five_whole_quotient T hP U hU hJ q hq hker hqs s e
  have hcon := ChapterC.SymmetricFive.source_natural_quotient_conclusions T hP U hU p hp hk f hf he hJ hfk
  obtain ⟨a,ha⟩ := hcon.2.2.1
  have hJT : (elementaryAbelianMaxJ (T : Subgroup G)).map p =
      (ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom := hcon.1.trans ha
  have hres : (pResidual 2 G).map p = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 p hp,Equiv.Perm.twoResidual_eq_alternating]
  have hJp : J.map p = ⊤ := by
    apply top_unique
    rw [←ChapterC.SymmetricFive.Paired.alternating_sup_transposition a,←hres,←hJT]
    exact sup_le (map_mono (residual_le_thompson T hP U hU hJ).1)
      (map_mono (elementaryAbelianMaxJ_sylow_le_top T))
  have hcover : J ⊔ q.ker = ⊤ := by
    have hh := congrArg (comap p) hJp
    simpa only [comap_map_eq,comap_top,hk,←hker] using hh
  have hJq : J.map q = ⊤ := by
    have hh := congrArg (map q) hcover
    have hz : q.ker.map q = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    simpa only [Subgroup.map_sup,hz,sup_bot_eq,map_top_of_surjective q hq] using hh
  have hY : Y = ⊤ := by
    apply top_unique
    rw [←hJq]
    exact global_thompson_image_le_offender T U q hq hker
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T))
  exact ⟨hJq.trans hY.symm,hY⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
