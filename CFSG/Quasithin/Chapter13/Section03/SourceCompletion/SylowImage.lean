module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointSource
/-!
# The original Sylow image in the binary unitary action

The induced image of the original Sylow is Sylow in the full action
image. After placing it in the native positive-root group, maximality
forces it to contain the entire derived Sylow. An inner conjugation of
the full G₂ model always supplies the required positive-root placement.

Source: the compatible Sylow marking in Notation13.3.3, printed p.885,
used by 13.3.18 on pp.894–895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G] {V:Subgroup G}

/-- Once the original Sylow image is placed in the binary positive roots,
it contains the entire actual derived Sylow. -/
theorem derived_sylow_le_induced_sylow (T:Sylow 2 G)
    (rho:Automizer V→*Atlas.G2.Model F)
    (hTN:(T:Subgroup G)≤normalizer (V:Set G))
    (hT:(inducedAutomizer V (T:Subgroup G)).map rho≤Atlas.G2.unipotent)
    (hd:commutator (Atlas.G2.Model F)≤rho.range) :
    Atlas.G2.unipotent⊓commutator (Atlas.G2.Model F)≤
      (inducedAutomizer V (T:Subgroup G)).map rho := by
  let N:=normalizer (V:Set G)
  let f:N→*Atlas.G2.Model F:=rho.comp V.normalizerMonoidHom.rangeRestrict
  let R:=f.range
  have hR:R=rho.range := by
    change (rho.comp V.normalizerMonoidHom.rangeRestrict).range=_
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr V.normalizerMonoidHom.rangeRestrict_surjective,
      ←MonoidHom.range_eq_map]
  let S:Sylow 2 R:=(T.subtype hTN).mapSurjective f.rangeRestrict_surjective
  have hS:(S:Subgroup R).map R.subtype=(inducedAutomizer V (T:Subgroup G)).map rho := by
    change (((T:Subgroup G).subgroupOf N).map f.rangeRestrict).map R.subtype=_
    rw [map_map]
    change ((T:Subgroup G).subgroupOf N).map f=_
    rw [inducedAutomizer,map_map]
  have hSU:(S:Subgroup R)≤Atlas.G2.unipotent.comap R.subtype := by
    intro s hs
    exact hT (hS ▸ mem_map_of_mem R.subtype hs)
  have hu:IsPGroup 2 (Atlas.G2.unipotent (K:=F)):=
    IsPGroup.of_card (n:=6) Atlas.G2.BinaryParabolicPair.card_unipotent_binary
  have he:Atlas.G2.unipotent.comap R.subtype=(S:Subgroup R):=
    S.is_maximal' hu.comap_subtype hSU
  intro g hg
  have hgR:g∈R:=hR.symm ▸ hd hg.2
  have hgS:(⟨g,hgR⟩:R)∈S := by
    change (⟨g,hgR⟩:R)∈(S:Subgroup R)
    rw [←he]
    exact hg.1
  rw [←hS]
  exact mem_map_of_mem R.subtype hgS

omit [Finite G] in
/-- The actual induced Sylow action admits a positive-root marking by an
inner automorphism of the full binary G₂ model. -/
theorem exists_sylow_image_marking (T:Sylow 2 G) (rho:Automizer V→*Atlas.G2.Model F) :
    ∃g:Atlas.G2.Model F,
      ((inducedAutomizer V (T:Subgroup G)).map rho).map (MulAut.conj g).toMonoidHom≤Atlas.G2.unipotent := by
  have hp:IsPGroup 2 ((inducedAutomizer V (T:Subgroup G)).map rho):=
    ((T.isPGroup'.comap_subtype).map V.normalizerMonoidHom.rangeRestrict).map rho
  obtain ⟨S,hS⟩:=hp.exists_le_sylow
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq (Atlas.G2.Model F) S Atlas.G2.BinaryParabolicPair.commonSylow
  refine ⟨g,?_⟩
  rw [←Atlas.G2.BinaryParabolicPair.commonSylow_eq,←hg,Sylow.coe_subgroup_smul]
  exact map_mono hS
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
