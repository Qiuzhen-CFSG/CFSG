module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedComplement
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.WreathReflection

/-!
# The genuine source complement reflection

The two original marked involutions are distinct: q²=u, while z=u s₅²
and s₅²≠1. Transporting this fact through the endpoint equivalence fixes
their actual type in the J.3 wreath complement. The marked wreath argument
then gives C_R(u)=I and conjugation u↦zu by every element of R outside I.
The complement is the one constructed to contain the literal sourceI.
Source: Aschbacher--Smith, paragraph preceding J.4.8, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Subgroup
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.FiveNormalizer
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.RootRelations

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

private theorem model_marks : modelU^2=1 ∧ modelU≠1 ∧ modelU≠modelZ := by
  have hu2 : u^2=1 := by rw [← q_square,← pow_mul]; exact q_four
  have hu1 : u≠1 := q_square ▸ q_square_ne
  have huz : u≠LongRootPaths.z := by
    have hz : LongRootPaths.z=u*RootRelations.s^2 := by
      simp only [LongRootPaths.z,Tits.atlas1600R5_eq,map_mul,map_pow,u,Atlas.a,RootRelations.s]
    intro he
    have hh : RootRelations.s^2=1 := by
      have h := he.symm
      rw [hz] at h
      exact mul_left_cancel (h.trans (mul_one u).symm)
    exact s_square_ne hh
  exact ⟨Subtype.ext hu2,fun h => hu1 (congrArg Subtype.val h),
    fun h => huz (congrArg Subtype.val h)⟩

/-- The inverter constructed by the endpoint marking has the precise
noncentral involution type required by the actual wreath calculation. -/
theorem source_involution_marks (hz : (e modelZ : G)=c.z) :
    (sourceU e)^2=1 ∧ sourceU e≠1 ∧ sourceU e≠c.z := by
  let f := F.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := F.subtype_injective.comp e.injective
  have h := model_marks
  refine ⟨?_,?_,?_⟩
  · change (f modelU)^2=1
    rw [← map_pow,h.1,map_one]
  · intro he
    exact h.2.1 (hf (he.trans (map_one f).symm))
  · intro he
    exact h.2.2 (hf (he.trans hz.symm))

/-- The same chosen original R has exactly I as the inverter centralizer,
and all its outside elements induce the required source reflection. -/
theorem source_centralizer_and_reflection
    (hz : (e modelZ : G)=c.z) (R : Subgroup G)
    (hIR : sourceI e≤R)
    (hR : Nonempty (R ≃* RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))))
    (hzR : c.z∈(center R).map R.subtype) :
    R ⊓ centralizer ({sourceU e}:Set G)=sourceI e ∧
      ∀ r∈R, r∉sourceI e → r*sourceU e*r⁻¹=c.z*sourceU e := by
  obtain ⟨eR⟩ := hR
  obtain ⟨eI⟩ := sourceI_equiv e
  have hmarks := source_marks_mem c e hz
  let zR : R := ⟨c.z,hIR hmarks.1⟩
  let uR : R := ⟨sourceU e,hIR hmarks.2⟩
  have hzc : zR∈center R := by
    exact (mem_map_iff_mem R.subtype_injective).mp hzR
  obtain ⟨hu2,hu1,huz⟩ := source_involution_marks c e hz
  have hz2 : c.z^2=1 := by
    have ho := SourceCompletion.z_order c
    exact orderOf_eq_prime_iff.mp ho |>.1
  have hz1 : c.z≠1 := by
    have ho := SourceCompletion.z_order c
    exact orderOf_eq_prime_iff.mp ho |>.2
  obtain ⟨hc,hr⟩ := WreathReflection.centralizer_and_reflection eR ((sourceI e).subgroupOf R)
    ((subgroupOfEquivOfLe hIR).trans eI) zR uR hmarks.1 hmarks.2 hzc
    (Subtype.ext hz2) (fun h => hz1 (congrArg Subtype.val h))
    (Subtype.ext hu2) (fun h => hu1 (congrArg Subtype.val h))
    (fun h => huz (congrArg Subtype.val h))
  refine ⟨?_,?_⟩
  · ext x
    constructor
    · rintro ⟨hxR,hxc⟩
      have hx : (⟨x,hxR⟩:R)∈centralizer ({uR}:Set R) := by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.mp hxc)
      have hxI : (⟨x,hxR⟩:R)∈(sourceI e).subgroupOf R := hc ▸ hx
      exact hxI
    · intro hx
      refine ⟨hIR hx,?_⟩
      have hxc : (⟨x,hIR hx⟩:R)∈centralizer ({uR}:Set R) := hc.symm ▸ hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hxc))
  · intro r hrR hrI
    exact congrArg Subtype.val (hr ⟨r,hrR⟩ hrI)

/-- The genuine J.3 complement can be selected with its complete marked
centralizer and reflection behavior, using only the earlier endpoint marks. -/
theorem exists_source_reflection
    (hz : (e modelZ : G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    ∃ R : Subgroup G, sourceI e≤R ∧ R≤d.toTypeRuSetup.H ∧
      R≤normalizer (B5Image B5 : Set G) ∧ Nat.card R=32 ∧ CQ B5≤R ∧
      Disjoint (fiveOddPart B5) R ∧
      normalizer (B5Image B5 : Set G)=fiveOddPart B5⊔R ∧
      Nonempty (R≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
      c.z∈(center R).map R.subtype ∧
      R⊓centralizer ({sourceU e}:Set G)=sourceI e ∧
      ∀ r∈R, r∉sourceI e → r*sourceU e*r⁻¹=c.z*sourceU e := by
  obtain ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,heR,hzc⟩ :=
    exists_source_complement c B5 e hz hfive
  obtain ⟨hc,hr⟩ := source_centralizer_and_reflection c e hz R hIR heR hzc
  exact ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,heR,hzc,hc,hr⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
