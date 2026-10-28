module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.NaturalCoreModels.SourceWitnesses.AutomorphismFixers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.LinearModels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Actor

/-!
# The full literal star centralizer in the natural cases

The normal simple star component is self-centralizing: its centralizer embeds
in the two-group quotient, while the full star group has trivial two-core.
Conjugation therefore embeds the full star group into the automorphism group
of the same marked SL₃(2). The source residual contains the marked radical
transvection and cubic rotation, whose common automorphism fixer is trivial.
This proves the full star centralizer without extending constituent action data.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
open CentralCover CentralCover.LinearModels LinearThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass} {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
  {ρ : Representation (ZMod 2) SL V}

private theorem component_self_centralizing (s : SourceData κ d c)
    (e : d.starImage I c.L ≃* SL) :
    centralizer (d.starImage I c.L : Set (d.Star I)) = ⊥ := by
  let := EightGeometry.NaturalModule.Recognition.starComponent_normal d c s.normal
  let C := centralizer (d.starImage I c.L : Set (d.Star I))
  let f := (QuotientGroup.mk' (d.starImage I c.L)).comp C.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxL : (x : d.Star I) ∈ d.starImage I c.L :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hze : e ⟨x, hxL⟩ ∈ center SL := by
      rw [mem_center_iff]
      intro a
      obtain ⟨y, rfl⟩ := e.surjective a
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (x.property y y.property))
    rw [Matrix.PSL3Two.center_eq_bot] at hze
    have hx1 : (⟨x, hxL⟩ : d.starImage I c.L) = 1 :=
      e.map_eq_one_iff.mp (mem_bot.mp hze)
    exact Subtype.ext (congrArg (fun y : d.starImage I c.L => (y : d.Star I)) hx1)
  have hp : IsPGroup 2 (d.Star I ⧸ d.starImage I c.L) :=
    MarkedMS.Constituents.SourceReduction.star_component_two_quotient d c s.normal
      s.generated s.sylow s.sylow_eq
  have hC : C ≤ pCore 2 (d.Star I) := le_sSup ⟨inferInstance, hp.of_injective f hf⟩
  exact eq_bot_iff.mpr (hC.trans_eq (d.star_twoCore_eq_bot ⟨s.sylow, s.sylow_eq⟩
    (d.Z_le_S (d.action.le_sylow d.T d.sylow_le (localModule_le d.T d.sylow_le)))))

/-- Both marked elements detect the centralizer in the entire original star quotient. -/
theorem star_centralizer_eq_bot (s : SourceData κ d c)
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    {f : FullCenter c.L ρ} (m : MarkedModel f d.Yplus) :
    centralizer (d.starImage I d.Yplus : Set (d.Star I)) = ⊥ := by
  let K := d.starImage I c.L
  let := EightGeometry.NaturalModule.Recognition.starComponent_normal d c s.normal
  let q := coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq
  let e : K ≃* SL := q.symm.trans m.model.quotientIso
  let a : d.Star I →* MulAut SL :=
    (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal
  have ha : Function.Injective a := (MulAut.congr e).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot K
      (component_self_centralizing s e))
  have hmark (l : c.L) : m.model.actorMap l = e (componentMap d c l) := by
    change m.model.quotientIso (QuotientGroup.mk' (pCore 2 c.L) l) =
      m.model.quotientIso (q.symm (componentMap d c l))
    rw [← coreQuotientEquivStar_apply d c s.normal s.sylow s.sylow_eq]
    exact congrArg m.model.quotientIso (q.symm_apply_apply _).symm
  apply eq_bot_iff.mpr
  intro x hx
  have hfix : ∀ b ∈ (d.Yplus.subgroupOf c.L).map m.model.actorMap, a x b = b := by
    rintro b ⟨l, hl, rfl⟩
    rw [hmark]
    change e (MulAut.conjNormal x (e.symm (e (componentMap d c l)))) = _
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    have hcomm := mem_centralizer_iff.mp hx
      (d.starMap I ⟨l, component_le c l.property⟩)
      (show d.starMap I ⟨l, component_le c l.property⟩ ∈ d.starImage I d.Yplus from
        mem_map_of_mem _ hl)
    change x * d.starMap I ⟨l, component_le c l.property⟩ * x⁻¹ = _
    rw [← hcomm, mul_inv_cancel_right]
    rfl
  have hx1 : a x = 1 := automorphism_eq_one_of_fixed_marked_matrices (a x)
    (hfix _ m.transvection_mem) (hfix _ m.rotation_mem)
  exact mem_bot.mpr (ha (hx1.trans a.map_one.symm))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.NaturalCoreModels.SourceWitnesses
