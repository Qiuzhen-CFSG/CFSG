module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.C27Geometry.SevenJoin
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Seven.Reconstruction.JoinSelection

/-!
# Shortness of the original fixed component

The original fixed Sylow lies in LᵤRᵤ. A nontrivial characteristic subgroup
of its Baumann subgroup, if normal in this join, would have a two-local
normalizer containing both K and T. Maximality of the original H would
then put Lᵤ in H, contrary to the source case.

The proved C.1.24 construction on the literal star module consequently
makes Lᵤ a short block. All fitting, quotient, Sylow, natural-action and
characteristic-subgroup premises are constructed from the original case.
The actual Rudvalis/D application is SevenSource; earlier source Data is
still supplied by its independent constructor.
Source: Aschbacher–Smith C.1.24(a), C.2.7 and14.7.68(2),
pp.130–131,145–147,1071–1072.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Chapter1.RadicalExclusions.ModelReduction
open FullSieve FullSieve.SourceInterface Nonquasisimple
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

theorem fixedComponent_no_normal_baumann (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (P : Sylow 2 (Lu ⊔ d.fixedCore u : Subgroup G))
    (hP : (P : Subgroup (Lu ⊔ d.fixedCore u : Subgroup G)).map
      (Lu ⊔ d.fixedCore u : Subgroup G).subtype = d.fixedSylow u)
    (D : Subgroup (ChapterB.baumann (P : Subgroup (Lu ⊔ d.fixedCore u : Subgroup G))))
    (hD : D.Characteristic) (hne : D ≠ ⊥) :
    ¬ (D.map (ChapterB.baumann (P : Subgroup (Lu ⊔ d.fixedCore u : Subgroup G))).subtype).Normal := by
  let J := Lu ⊔ d.fixedCore u
  let B := ChapterB.baumann (P : Subgroup J)
  let E := D.map B.subtype
  let Y := E.map J.subtype
  let := hD
  have hYne : Y ≠ ⊥ := by
    intro hh
    exact hne ((D.map_eq_bot_iff_of_injective B.subtype_injective).mp
      ((E.map_eq_bot_iff_of_injective J.subtype_injective).mp hh))
  have hYp : IsPGroup 2 Y :=
    (((P.isPGroup'.to_le (show B ≤ P from inf_le_left)).to_subgroup D).map B.subtype).map J.subtype
  have hSN : normalizer (d.fixedSylow u : Set G) ≤ normalizer (Y : Set G) := by
    let e : B ≃* ChapterB.baumann (d.fixedSylow u) :=
      (B.equivMapOfInjective J.subtype J.subtype_injective).trans
        (MulEquiv.subgroupCongr (by
          change ((P : Subgroup J) ⊓ centralizer
            (omegaOneCenterAmbient (Stellmacher.elementaryAbelianMaxJ (P : Subgroup J)) : Set J)).map
              J.subtype = _
          rw [Stellmacher.baumann_map_injective J.subtype J.subtype_injective,hP]
          rfl))
    let C := D.map e.toMonoidHom
    let : C.Characteristic := by
      apply characteristic_iff_le_comap.mpr
      intro a x hx
      obtain ⟨y,hy,rfl⟩ := hx
      refine ⟨(MulAut.congr e.symm a) y,
        characteristic_iff_le_comap.mp hD (MulAut.congr e.symm a) hy,?_⟩
      exact e.apply_symm_apply (a (e y))
    have hm : C.map (ChapterB.baumann (d.fixedSylow u)).subtype = Y := by
      change (D.map e.toMonoidHom).map (ChapterB.baumann (d.fixedSylow u)).subtype =
        (D.map B.subtype).map J.subtype
      rw [map_map,map_map]
      rfl
    rw [←hm]
    exact (Stellmacher.normalizer_le_normalizer_baumann (d.fixedSylow u)).trans
      (normalizer_le_normalizer_characteristic_image _ C)
  intro hn
  let : E.Normal := hn
  have hJN : J ≤ normalizer (Y : Set G) := by
    have hh := E.le_normalizer_map J.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hHN : F.H ≤ normalizer (Y : Set G) := by
    rw [d.residual_product]
    exact sup_le (h.larger.le.trans (le_sup_left.trans hJN))
      ((d.T_normalizes_fixedSylow u h.fixed).trans hSN)
  exact h.outside (le_sup_left.trans (hJN.trans
    (h.maximal.2 ⟨Y,hYne,hYp,rfl⟩ hHN)))


theorem fixedComponent_short_from_source (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : ChapterC.IsShort Lu := by
  let input := d.fixedComponent_C27_input Nonquasisimple.earlier1211_source u h
    d.point_mem_U_commutator_K
  let J := Lu ⊔ d.fixedCore u
  obtain ⟨P,hP⟩ := h.sylow.restrict (d.fixedSylow_le_component_radical_join u h) input.join_le
  have hR : d.fixedCore u ≤ d.fixedSylow u := by
    obtain ⟨S,hS⟩ := d.fixedSylow_isSylow_inter_H u h.member h.fixed
    exact (pCoreIn_le_sylow (F.H ⊓ d.fixedCentralizer u : Subgroup G) S).trans_eq hS
  have hprod : ∀ g : J, ∃ k ∈ Lu.subgroupOf J, ∃ t ∈ (P : Subgroup J), k*t=g := by
    intro g
    have hg : (g : G) ∈ (Lu : Set G) * (d.fixedCore u : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left Lu (d.fixedCore u) input.normalizes]
      exact g.property
    obtain ⟨k,hk,r,hr,he⟩ := hg
    let k' : J := ⟨k,mem_sup_left hk⟩
    let r' : J := ⟨r,mem_sup_right hr⟩
    refine ⟨k',hk,r',?_,Subtype.ext he⟩
    have hm : r ∈ (P : Subgroup J).map J.subtype := hP.symm ▸ hR hr
    exact (mem_map_iff_mem J.subtype_injective).mp hm
  have hb := Chapter14.Section06.Seven.Reconstruction.block_types_of_join_eq
    (ChapterC.C27Source.source_join_input input) rfl
    (d.fixedComponent_C27_core_alternatingSeven u h).some P hprod
    (d.fixedComponent_no_normal_baumann u h P hP)
  exact hb.elim (fun h => h.2.1) (fun h => h.1)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
