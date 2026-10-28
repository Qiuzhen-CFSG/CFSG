module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.LineKernel
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Scalar
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceReflections

/-!
# The actual opposite SL₂(5) in the marked Iz centralizer

The second source reflection fixes u, exchanges z with zu and preserves
C_P(u). It therefore sends the next fixed five to the original B₅. Transport
the previously proved opposite SL₂(5) and its centralizing scalar through
that very reflection. The image contains B₅ and is normalized by the same I;
the transported scalar has order four inside I∩C_G(B₅), hence is exactly
the original Iz. Its generator squares to the original z.

This constructs the literal K and all its placements for the subsequent
whole-centralizer and complement-uniqueness argument; none is an input.
Source: Aschbacher–Smith, discussion before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

theorem base_eq_core_fixed (u:G) (hu:u∈d.toTypeRuSetup.H)
    (hfusion:IsConj u c.z) (hi:∀x∈B5Image B5,u*x*u⁻¹=x⁻¹) :
    coreAt (fixedFive B5 u)⊓centralizer ({c.z}:Set G)=B5Image B5 := by
  obtain ⟨g,hgu,hgA,hvH,hvclass,hvinv,hBmap⟩ := swapped_seed c B5 u hu hfusion hi
  have hP := (pair_core c B5 (fixedFive B5 u) u g hgu hgA).1
  apply map_injective (f:=(MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_inf _ _ _ (MulAut.conj g).injective,Theory.GroupTheory.map_centralizer_singleton]
  change (coreAt (fixedFive B5 u)).conjBy g ⊓ centralizer ({g*c.z*g⁻¹}:Set G)=
    (B5Image B5).conjBy g
  rw [hP,hBmap]

/-- The actual second source reflection sends the selected new five to B₅. -/
theorem nextFive_conj_reflection
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z)
    (s:G) (hsA:s∈normalizer (fixedFive B5 (sourceU e):Set G))
    (hsu:s*sourceU e*s⁻¹=sourceU e) (hsz:s*c.z*s⁻¹=sourceU e*c.z) :
    (nextFive c B5 (sourceU e)).conjBy s=B5Image B5 := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  have hzu : Commute c.z (sourceU e) :=
    (mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)).symm
  have hu2 := (source_involution_marks c e hz).1
  have hst : s*(c.z*sourceU e)*s⁻¹=c.z := by
    calc
      _ = (s*c.z*s⁻¹)*(s*sourceU e*s⁻¹) := by group
      _ = (sourceU e*c.z)*sourceU e := by rw [hsu,hsz]
      _ = c.z := by rw [← hzu.eq,mul_assoc,← pow_two,hu2,mul_one]
  change (coreAt (fixedFive B5 (sourceU e))⊓centralizer ({c.z*sourceU e}:Set G)).map
    (MulAut.conj s).toMonoidHom=B5Image B5
  have hmap : (fixedFive B5 (sourceU e)).map (MulAut.conj s).toMonoidHom=
      fixedFive B5 (sourceU e) := mem_normalizer_iff_map_conj_eq.mp hsA
  rw [map_inf _ _ _ (MulAut.conj s).injective,map_coreAt,hmap,
    Theory.GroupTheory.map_centralizer_singleton]
  change coreAt (fixedFive B5 (sourceU e))⊓centralizer ({s*(c.z*sourceU e)*s⁻¹}:Set G)=_
  rw [hst]
  exact base_eq_core_fixed c B5 (sourceU e) hu hfusion hi

/-- The actual opposite SL₂(5) at z contains the original B₅, is normalized
by the same I, and centralizes its specified Iz. -/
theorem exists_source_base_opposite
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hfusion : IsConj (sourceU e) c.z) :
    ∃ (K:Subgroup G) (s:G), K=(oppositePair c B5 (sourceU e)).conjBy s ∧
      s∈normalizer (sourceI e:Set G) ∧
      s*sourceU e*s⁻¹=sourceU e ∧ s*c.z*s⁻¹=sourceU e*c.z ∧
      B5Image B5≤K ∧ sourceI e≤normalizer (K:Set G) ∧
      K≤centralizer (sourceIz e:Set G) ∧
      Nonempty (K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      ∃ i:G,sourceIz e=zpowers i ∧ orderOf i=4 ∧ i^2=c.z := by
  obtain ⟨hu,hi⟩ := source_inverter c B5 e hz hfive
  obtain ⟨r,s,hr,hs,hrz,hru,hsu,hsz,hrB,hsA⟩ :=
    exists_source_two_transvections c B5 e hz hfive hfusion
  obtain ⟨i,hiI,hio,hisq,hiK,hisc⟩ := exists_source_scalar_four c B5 e hz hfive hfusion
  let a := MulAut.conj s
  let K := (oppositePair c B5 (sourceU e)).conjBy s
  let C := (zpowers i).conjBy s
  have hsI : (sourceI e).conjBy s=sourceI e := mem_normalizer_iff_map_conj_eq.mp hs
  have hBK : B5Image B5≤K := by
    rw [← nextFive_conj_reflection c B5 e hz hfive hfusion s hsA hsu hsz]
    exact map_mono le_sup_right
  have hCI : C≤sourceI e := by
    have hh := map_mono (f:=a.toMonoidHom) (zpowers_le.mpr hiI)
    change C≤(sourceI e).conjBy s at hh
    rwa [hsI] at hh
  have hCK : C≤centralizer (K:Set G) := by
    have hh := map_mono (f:=a.toMonoidHom) (zpowers_le.mpr hiK)
    rw [Theory.Quasithin.map_centralizer] at hh
    exact hh
  have hC4 : Nat.card C=4 := by
    change Nat.card ((zpowers i).map a.toMonoidHom)=4
    rw [card_map_of_injective a.injective,Nat.card_zpowers,hio]
  have hC : C=sourceIz e := eq_sourceIz_of_four c B5 e hz hfive hfusion C hC4 hCI
    (hCK.trans (centralizer_le hBK))
  have hIK : sourceI e≤normalizer (K:Set G) := by
    have hh := (map_mono (f:=a.toMonoidHom)
      (sourceI_normalizes_edge_and_opposite c B5 e hz hfive).2).trans
      ((oppositePair c B5 (sourceU e)).le_normalizer_map a.toMonoidHom)
    change (sourceI e).conjBy s≤normalizer (K:Set G) at hh
    rwa [hsI] at hh
  obtain ⟨hK⟩ := opposite_pair_equiv_SL2 c B5 (sourceU e) hu hfusion hi
  have hKi : Nonempty (K≃*Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :=
    ⟨((oppositePair c B5 (sourceU e)).equivMapOfInjective a.toMonoidHom a.injective).symm.trans hK⟩
  have hcz : a (c.z*sourceU e)=c.z := by
    rw [map_mul]
    change (s*c.z*s⁻¹)*(s*sourceU e*s⁻¹)=c.z
    rw [hsz,hsu]
    have hu2 := (source_involution_marks c e hz).1
    have hzu := mem_centralizer_singleton_iff.mp (c.H_eq_centralizer_z ▸ hu)
    rw [hzu,mul_assoc,← pow_two,hu2,mul_one]
  refine ⟨K,s,rfl,hs,hsu,hsz,hBK,hIK,?_,hKi,a i,?_,?_,?_⟩
  · exact le_centralizer_iff.mp (hC ▸ hCK)
  · rw [← hC]
    exact MonoidHom.map_zpowers a.toMonoidHom i
  · exact (a.orderOf_eq i).trans hio
  · rw [← map_pow,hisq,hcz]

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
