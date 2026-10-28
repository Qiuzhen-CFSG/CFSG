module
public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Actor
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PlaneAction
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.PlaneCoreSource

/-!
# The cubic action and kernel of the source plane actor

The native syntheme action is transported through the original local quotient.
Its image has order three and its kernel is a two-group identified with the
centralizer of V₂, retaining the literal source action.
Source: Aschbacher--Smith13.5.4 and13.5.6, printed pp.916–917.
-/
@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)

private theorem localMap_fixes_iff (l:L) (W:Subgroup G)(hWV:W≤V) :
    (∀w∈image d W,naturalRepresentation (Fin 6) (localMap d l) w=w) ↔
      l.val∈centralizer (W:Set G) := by
  constructor
  · intro hf
    apply mem_centralizer_iff.mpr
    intro w hw
    let wV:V:=⟨w,hWV hw⟩
    have he:=d.conjugation l wV
    have hfix:=hf (d.coordinate wV).toAdd ((mem_image d W _).mpr ⟨wV,hw,rfl⟩)
    have hh:=congrArg Subtype.val (d.coordinate.injective (he.trans hfix))
    change l.val*w*l.val⁻¹=w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hc w hw
    obtain ⟨v,hv,rfl⟩:=(mem_image d W w).mp hw
    have hh:=mem_centralizer_iff.mp hc v.val hv
    have he:V.normalizerMonoidHom ⟨l.val,d.normalizes_V (mem_sup_left l.property)⟩ v=v:=by
      apply Subtype.ext
      change l.val*v.val*l.val⁻¹=v.val
      rw [←hh,mul_inv_cancel_right]
    exact (d.conjugation l v).symm.trans (congrArg (fun v:V=>(d.coordinate v).toAdd) he)

private theorem conjugate_fixes (a g:Equiv.Perm (Fin 6)) :
    (∀v∈canonicalPlane,naturalRepresentation (Fin 6) (a⁻¹*g*a) v=v) ↔
      (∀v∈move a canonicalPlane,naturalRepresentation (Fin 6) g v=v) := by
  let ρ:=naturalRepresentation (Fin 6)
  constructor
  · intro h v hv
    obtain ⟨w,hw,rfl⟩:=hv
    have hh:=congrArg (ρ a) (h w hw)
    simpa only [map_mul,Module.End.mul_apply,ρ,(naturalRepresentation (Fin 6)).self_inv_apply] using hh
  · intro h v hv
    have hh:=congrArg (ρ a⁻¹) (h (ρ a v) (Submodule.mem_map_of_mem hv))
    simpa only [map_mul,Module.End.mul_apply,ρ,(naturalRepresentation (Fin 6)).inv_self_apply] using hh

include d in
/-- The original plane parabolic has its actual S₃ quotient and two-group
kernel; trivial quotient action is exactly centralization of V₂. -/
theorem exists_planeLocal_quotient (hb:ChapterC.IsAlternatingBlock L 6) :
    ∃q:planeLocal (L:=L) (V₂:=V₂)→*Equiv.Perm (Fin 3),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      ∀g,q g=1 ↔ g.val∈centralizer (V₂:Set G) := by
  obtain ⟨a,_,ha⟩:=QuadraticSource.source_even_flag d
  let f:=planeLocalMap d
  let c:Equiv.Perm (Fin 6)→*Equiv.Perm (Fin 6):=(MulAut.conj a.val⁻¹).toMonoidHom
  have hf:f.range=L2.map (MulAut.conj a.val).toMonoidHom:=by
    rw [planeLocalMap_range d,planeLocal_image d,ha,flagStabilizer_move,flagStabilizer_plane,
      L2,Subgroup.map_inf _ _ _ (MulAut.conj a.val).injective,conjugate_alternating]
  have hcf:(c.comp f).range=L2:=by
    rw [MonoidHom.range_comp,hf,map_map]
    have he:c.comp (MulAut.conj a.val).toMonoidHom=MonoidHom.id _:=by
      apply MonoidHom.ext
      intro x
      change a.val⁻¹*(a.val*x*a.val⁻¹)*(a.val⁻¹)⁻¹=x
      group
    rw [he,Subgroup.map_id]
  let α:planeLocal (L:=L) (V₂:=V₂)→*a6SynthemeStabilizer:={
    toFun:=fun g=>⟨⟨c (f g), (hcf ▸ (show c (f g)∈(c.comp f).range from ⟨g,rfl⟩)).2⟩,
      (hcf ▸ (show c (f g)∈(c.comp f).range from ⟨g,rfl⟩)).1⟩
    map_one':=by apply Subtype.ext; apply Subtype.ext; exact map_one (c.comp f)
    map_mul':=by intros; apply Subtype.ext; apply Subtype.ext; exact map_mul (c.comp f) _ _ }
  have hα:Function.Surjective α:=by
    intro y
    have hy:y.val.val∈(c.comp f).range:=hcf ▸ (show y.val.val∈L2 from ⟨y.property,y.val.property⟩)
    obtain ⟨g,hg⟩:=hy
    exact ⟨g,Subtype.ext (Subtype.ext hg)⟩
  have hkα:IsPGroup 2 α.ker:=by
    apply ((localMap_kernel_two d hb).comap_of_injective (inclusion (show planeLocal (L:=L) (V₂:=V₂)≤L from inf_le_left))
      (inclusion_injective _)).to_le
    intro g hg
    have hh: c (f g)=1:=congrArg (fun y:a6SynthemeStabilizer=>y.val.val) hg
    have hh': f g=1 := (MulAut.conj a.val⁻¹).injective (hh.trans (map_one c).symm)
    exact hh'
  let q:=a6SynthemeQuotientHom.comp α
  refine ⟨q,a6SynthemeQuotientHom_surjective.comp hα,?_,?_⟩
  · have hk:IsPGroup 2 a6SynthemeQuotientHom.ker:=by rw [a6SynthemeQuotientHom_ker]; exact pCore_isPGroup
    exact hk.comap_of_ker_isPGroup α hkα
  · intro g
    change a6SynthemeQuotientHom (α g)=1 ↔ _
    rw [PlaneAction.even_syntheme_quotient_eq_one_iff]
    change (∀v∈canonicalPlane,naturalRepresentation (Fin 6) (a.val⁻¹*f g*a.val) v=v) ↔ _
    rw [conjugate_fixes,←ha]
    exact localMap_fixes_iff d (inclusion (show planeLocal (L:=L) (V₂:=V₂)≤L from inf_le_left) g)
      V₂ (d.plane_le_seed.trans d.seed_le)

end CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks
