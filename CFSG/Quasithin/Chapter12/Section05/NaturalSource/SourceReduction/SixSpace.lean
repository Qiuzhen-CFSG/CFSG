module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.SourceReduction.PointIncidence

/-!
# The noncommuting conjugate and the original six-space

Conjugate the actual second module into T by an element of N(V). The
commutator and its inclusion in both original factors are transported by
that same conjugator. The exterior small-index calculation then identifies
both its commutator and its centralizer in V with V₆. Since z lies in V₆,
controlled point fusion and the original TI property inside M contradict
G₁ ≤ M. No point escape or noncommuting conjugate is assumed by the final
source assembly in Completion.

Source: Aschbacher--Smith, 12.4.4, printed p.813.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
include s

theorem noncommuting_pair_sylow_transport (g : G)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hle : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ n ∈ normalizer (V : Set G),
      V.map (MulAut.conj (n * g)).toMonoidHom ≤ (T : Subgroup G) ∧
      ⁅V,V.map (MulAut.conj (n * g)).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj (n * g)).toMonoidHom⁆ ≤
        V ⊓ V.map (MulAut.conj (n * g)).toMonoidHom := by
  let := D.elementary
  have hAN := le_normalizer_iff_commutator_le_left.mpr (hle.trans inf_le_left)
  obtain ⟨n,hn,hnT⟩ := offender_exists_normalizer_conjugate_le_sylow V T
    (le_sup_right.trans s.normalizes)
    ((IsElementaryAbelian.isPGroup 2 V).map (MulAut.conj g).toMonoidHom) hAN
  rw [offender_map_conj_map] at hnT
  have hnV : V.map (MulAut.conj n).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hn
  have he : (⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map
      (MulAut.conj n).toMonoidHom = ⁅V,V.map (MulAut.conj (n * g)).toMonoidHom⁆ := by
    rw [map_commutator,hnV,offender_map_conj_map]
  refine ⟨n,hn,hnT,?_,?_⟩
  · rw [←he]
    exact fun hb => hne ((map_eq_bot_iff_of_injective _ (MulAut.conj n).injective).mp hb)
  · have hm := map_mono (f := (MulAut.conj n).toMonoidHom) hle
    rwa [he,map_inf _ _ _ (MulAut.conj n).injective,hnV,offender_map_conj_map] at hm

theorem noncommuting_pair_six_space (g : G)
    (hT : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hs : let := D.elementary; globalS V = 3) :
    s.actorImage (V.map (MulAut.conj g).toMonoidHom) =
        SL5ExteriorSquare.parabolicResidualTwoCore 4 ∧
      V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) = s.marking.Vi 6 ∧
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = s.marking.Vi 6 := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ L ⊔ (T : Subgroup G) := hT.trans le_sup_right
  let _ := IsElementaryAbelian.subgroupOf (p := 2) hAH
  let _ : IsElementaryAbelian 2 (s.actorImage A) := IsElementaryAbelian.map _
  have hI : s.actorImage A ≠ ⊥ := by
    intro he
    have hf := s.subspace_fixedSpace hAH
    rw [he,BinaryOffender.fixedSpace_bot,s.marking.subspace_top] at hf
    exact hne (commutator_eq_bot_iff_le_centralizer.mpr (inf_eq_left.mp hf.symm))
  obtain ⟨hi,hf,hc,_⟩ := ExteriorGeometry.smallIndex_three_module_geometry
    (s.actorImage A) (s.actorImage_le_flag hT) hI (s.actorImage_smallIndex_three g hT hs)
  refine ⟨hi,?_,?_⟩
  · rw [←s.subspace_fixedSpace hAH,hf]
    rfl
  · rw [←s.subspace_commutator hAH,hc]
    rfl

theorem noncommuting_pair_contains_point (g : G)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hle : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom)
    (hs : let := D.elementary; globalS V = 3) :
    ∃ n ∈ normalizer (V : Set G),
      V.map (MulAut.conj (n * g)).toMonoidHom ≤ (T : Subgroup G) ∧
      ⁅V,V.map (MulAut.conj (n * g)).toMonoidHom⁆ ≠ ⊥ ∧
      s.marking.z ∈ V.map (MulAut.conj (n * g)).toMonoidHom := by
  obtain ⟨n,hn,hT,hne',hle'⟩ := s.noncommuting_pair_sylow_transport g hne hle
  have hc := (s.noncommuting_pair_six_space (n*g) hT hne' hs).2.2
  have hz : s.marking.z ∈ ⁅V,V.map (MulAut.conj (n*g)).toMonoidHom⁆ := by
    rw [hc]
    exact s.marking.V₁_le_V₆ s.marking.z_mem_V₁
  exact ⟨n,hn,hT,hne',(hle' hz).2⟩

theorem noncommuting_pair_excluded
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hpoint : s.marking.Gi 1 ≤ s.marking.M)
    (g : G)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hle : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) : False := by
  let := D.elementary
  obtain ⟨n,_,_,hn,hz⟩ := s.noncommuting_pair_contains_point g hne hle
    (s.exteriorFusion_from_source h structural).parameters.2.2
  have p := s.pointControl_from_source h structural
  obtain ⟨c,hc⟩ := exists_centralizer_conjugator_of_element_fusion
    (fun x hx => by
      obtain ⟨l,hl,he⟩ := p.fusion x hx
      exact ⟨l,D.normalizes hl,he.symm⟩) hz
  have hcG : (c : G) ∈ s.marking.Gi 1 := p.point_centralizer.symm ▸ c.property
  have he : V.map (MulAut.conj (n * g)).toMonoidHom = V := by
    rcases ((structural L h).2.2 V D).2.2.1 (c : G) (hpoint hcG) with hb | he
    · have hh : s.marking.z ∈ V ⊓ V.map (MulAut.conj (c : G)).toMonoidHom :=
        ⟨s.marking.z_mem,hc.symm ▸ hz⟩
      exact (s.marking.z_ne_one (mem_bot.mp (hb ▸ hh))).elim
    · exact hc.symm.trans he
  rw [he] at hn
  exact hn (commutator_self_eq_bot_iff.mpr inferInstance)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
