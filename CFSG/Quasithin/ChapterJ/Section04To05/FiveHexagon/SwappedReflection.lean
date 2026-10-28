module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceAlignment
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedReflection

/-!
# The second original wreath reflection

The source pair conjugator preserving I transports the existing wreath
complement to C_G(u)∩N_G(C_P(u)), retaining that same I. Its marked wreath
structure gives C_Ru(z)=I and the second transvection z↦uz. The two actual
source actors normalize I, fix their indicated involutions, and their
triple product interchanges z and u exactly.

Source: Aschbacher–Smith, paragraph before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- The exchanged source pair has a wreath complement containing exactly
 the same I and carrying the second marked reflection. -/
theorem exists_source_swapped_reflection
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ R:Subgroup G, sourceI e≤R ∧
      R≤centralizer ({sourceU e}:Set G) ∧
      R≤normalizer (fixedFive B5 (sourceU e):Set G) ∧ Nat.card R=32 ∧
      Nonempty (R≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
      R⊓centralizer ({c.z}:Set G)=sourceI e ∧
      ∀ r∈R,r∉sourceI e → r*c.z*r⁻¹=sourceU e*c.z := by
  obtain ⟨g,hgu,hgA,hgI⟩ := source_pair_conjugacy_preserving_I c B5 e hz hfive hfusion
  obtain ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,heR,hzc⟩ := exists_source_complement c B5 e hz hfive
  let R' := R.conjBy g⁻¹
  have hIg : (sourceI e).conjBy g⁻¹=sourceI e := by
    have hh := conjBy_inv (sourceI e) g
    rwa [hgI] at hh
  have hIR' : sourceI e≤R' := by
    rw [← hIg]
    exact map_mono hIR
  have hR'32 : Nat.card R'=32 := (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hR32
  obtain ⟨eR⟩ := heR
  let eR' : R'≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)) :=
    (R.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm.trans eR
  have hzu : g⁻¹*c.z*(g⁻¹)⁻¹=sourceU e := by
    rw [← hgu]
    group
  have hR'c : R'≤centralizer ({sourceU e}:Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [← hzu]
    have hc := mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hRH hx)
    exact (map_mul (MulAut.conj g⁻¹) x c.z).symm.trans
      ((congrArg (MulAut.conj g⁻¹) hc).trans (map_mul (MulAut.conj g⁻¹) c.z x))
  have hR'n : R'≤normalizer (fixedFive B5 (sourceU e):Set G) := by
    have hh := (map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hRN).trans
      ((B5Image B5).le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change R'≤normalizer ((B5Image B5).conjBy g⁻¹:Set G) at hh
    rw [← hgA,conjBy_inv] at hh
    exact hh
  have hm := source_marks_mem c e hz
  let uR:R' := ⟨sourceU e,hIR' hm.2⟩
  let zR:R' := ⟨c.z,hIR' hm.1⟩
  have huc : uR∈center R' := by
    apply mem_center_iff.mpr
    intro r
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hR'c r.property))
  obtain ⟨eI⟩ := sourceI_equiv e
  obtain ⟨hu2,hu1,huz⟩ := source_involution_marks c e hz
  obtain ⟨hz1,hz2⟩ := c.z_involution_of_card d.card_Z
  have hc := WreathReflection.centralizer_and_reflection eR' ((sourceI e).subgroupOf R')
    ((subgroupOfEquivOfLe hIR').trans eI) uR zR hm.2 hm.1 huc
    (Subtype.ext hu2) (fun h => hu1 (congrArg Subtype.val h))
    (Subtype.ext hz2) (fun h => hz1 (congrArg Subtype.val h))
    (fun h => huz (congrArg Subtype.val h).symm)
  refine ⟨R',hIR',hR'c,hR'n,hR'32,⟨eR'⟩,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨hx,hxc⟩
      have hh : (⟨x,hx⟩:R')∈centralizer ({zR}:Set R') :=
        mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hxc))
      rw [hc.1] at hh
      exact hh
    · intro hx
      refine ⟨hIR' hx,?_⟩
      have hh : (⟨x,hIR' hx⟩:R')∈centralizer ({zR}:Set R') := hc.1.symm ▸ hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hh))
  · intro r hr hn
    exact congrArg Subtype.val (hc.2 ⟨r,hr⟩ hn)

private theorem complement_normalizes_I (R:Subgroup G) (hIR:sourceI e≤R)
    (hR:Nonempty (R≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2)))) :
    R≤normalizer (sourceI e:Set G) := by
  intro r hr
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply sourceI_weakly_closed_in_complement e R hIR hR
  have hh := map_mono (f:=(MulAut.conj r).toMonoidHom) hIR
  have he := mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr)
  exact hh.trans_eq he

private theorem exists_outside_I (R:Subgroup G) (hR:Nat.card R=32) :
    ∃r∈R,r∉sourceI e := by
  by_contra! hh
  have hc := Subgroup.card_le_of_le (show R≤sourceI e from hh)
  rw [hR,sourceI_card e] at hc
  omega

/-- Both source transvections normalize the same original I. Their
centers are the distinct marked involutions z and u. -/
theorem exists_source_two_transvections
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ r s:G, r∈normalizer (sourceI e:Set G) ∧ s∈normalizer (sourceI e:Set G) ∧
      r*c.z*r⁻¹=c.z ∧ r*sourceU e*r⁻¹=c.z*sourceU e ∧
      s*sourceU e*s⁻¹=sourceU e ∧ s*c.z*s⁻¹=sourceU e*c.z ∧
      r∈normalizer (B5Image B5:Set G) ∧ s∈normalizer (fixedFive B5 (sourceU e):Set G) := by
  obtain ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,heR,hzc,hcu,hr⟩ :=
    exists_source_reflection c B5 e hz hfive
  obtain ⟨S,hIS,hSc,hSn,hS32,heS,hcz,hs⟩ :=
    exists_source_swapped_reflection c B5 e hz hfive hfusion
  obtain ⟨r,hrR,hrI⟩ := exists_outside_I e R hR32
  obtain ⟨s,hsS,hsI⟩ := exists_outside_I e S hS32
  refine ⟨r,s,complement_normalizes_I e R hIR heR hrR,
    complement_normalizes_I e S hIS heS hsS,?_,hr r hrR hrI,?_,hs s hsS hsI,hRN hrR,hSn hsS⟩
  · exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hRH hrR))
  · exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hSc hsS))

/-- The generated source reflections contain an actor interchanging the
marked involutions exactly, while preserving their original I. -/
theorem exists_source_mark_swap
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ a:G,a∈normalizer (sourceI e:Set G) ∧
      a*c.z*a⁻¹=sourceU e ∧ a*sourceU e*a⁻¹=c.z := by
  obtain ⟨r,s,hr,hs,hrz,hru,hsu,hsz,_⟩ :=
    exists_source_two_transvections c B5 e hz hfive hfusion
  have hz2 := (c.z_involution_of_card d.card_Z).2
  have hu2 := (source_involution_marks c e hz).1
  have hzu : Commute c.z (sourceU e) := by
    have hu := (source_inverter c B5 e hz hfive).1
    exact (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)).symm
  refine ⟨r*s*r,mul_mem (mul_mem hr hs) hr,?_,?_⟩
  · calc
      _ = r*(s*(r*c.z*r⁻¹)*s⁻¹)*r⁻¹ := by group
      _ = r*(sourceU e*c.z)*r⁻¹ := by rw [hrz,hsz]
      _ = (r*sourceU e*r⁻¹)*(r*c.z*r⁻¹) := by group
      _ = (c.z*sourceU e)*c.z := by rw [hru,hrz]
      _ = sourceU e := by rw [hzu.eq,mul_assoc,← pow_two,hz2,mul_one]
  · calc
      _ = r*(s*(r*sourceU e*r⁻¹)*s⁻¹)*r⁻¹ := by group
      _ = r*(s*(c.z*sourceU e)*s⁻¹)*r⁻¹ := by rw [hru]
      _ = r*((s*c.z*s⁻¹)*(s*sourceU e*s⁻¹))*r⁻¹ := by group
      _ = r*((sourceU e*c.z)*sourceU e)*r⁻¹ := by rw [hsz,hsu]
      _ = r*c.z*r⁻¹ := by
        have hc : (sourceU e*c.z)*sourceU e=c.z := by
          rw [← hzu.eq,mul_assoc,← pow_two,hu2,mul_one]
        rw [hc]
      _ = c.z := hrz

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
