module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.AutomorphismOrbit
/-!
# Central natural commutator seeds

The natural quadratic Sylow action places [B,V] in the intrinsic omega center.
The seed is nontrivial because the marked Sylow moves V. All maps retain the
original C.1.17 marking.

Source: Campbell, Pushing up in Finite Groups, II.8, printed pp.36–38,
specialized to the original C.1.17 marked family.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

omit [Finite B] in
theorem InLocalClass.omegaCenter_map_le_F (h : InLocalClass e) :
    (omegaCenter B).map e ≤ Campbell.F H :=
  (le_normalClosure : (omegaCenter B).map e ≤ localV e).trans
    (h.localV_le_coreOmegaCenter.trans Campbell.omegaCore_le_F)

omit [Finite B] in
theorem InLocalClass.campbellV_le_range (h : InLocalClass e) :
    Campbell.V H ≤ e.range := by
  obtain ⟨T,he,_⟩ := h.sylow
  rw [he]
  exact Campbell.V_le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)

omit [Finite B] in
theorem InLocalClass.campbellF_le_range (h : InLocalClass e) :
    Campbell.F H ≤ e.range := by
  obtain ⟨T,he,_⟩ := h.sylow
  rw [he]
  exact Campbell.F_le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)

omit [Finite B] in
theorem InLocalClass.campbell_seed_map (h : InLocalClass e) :
    (⁅(⊤ : Subgroup B),(Campbell.V H).comap e⁆).map e = ⁅e.range,Campbell.V H⁆ := by
  rw [map_commutator,←MonoidHom.range_eq_map,map_comap_eq,inf_eq_right.mpr h.campbellV_le_range]

theorem InLocalClass.campbell_seed_le_omegaCenter (h : InLocalClass e) (hB : IsBaumannFixed B) :
    ⁅(⊤ : Subgroup B),(Campbell.V H).comap e⁆ ≤ omegaCenter B := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hid : ⁅e.range,Campbell.V H⁆ = Campbell.V H ⊓ centralizer (e.range : Set H) := by
    rw [←hS,h.campbellV_eq_moved hB m]
    exact (h.sylow_fixed_eq_commutator hB m d hS).symm
  intro x hx
  have hh : e x ∈ Campbell.V H ⊓ centralizer (e.range : Set H) := by
    rw [←hid,←h.campbell_seed_map]
    exact mem_map_of_mem e hx
  have hz : x ∈ center B := by
    apply mem_center_iff.mpr
    intro y
    apply h.injective
    simpa only [map_mul] using hh.2 (e y) ⟨y,rfl⟩
  refine ⟨⟨x,hz⟩,subset_closure ?_,rfl⟩
  change (⟨x,hz⟩ : center B)^(2^1)=1
  apply Subtype.ext
  apply h.injective
  have hex := ((mem_omegaOneCenterAmbient_iff _ _).mp (Campbell.V_le_omegaCore hh.1)).2.1
  change e (x^(2^1)) = e 1
  simpa only [pow_one,map_pow,map_one] using hex

theorem InLocalClass.campbell_seed_ne_bot (h : InLocalClass e) (hB : IsBaumannFixed B) :
    ⁅(⊤ : Subgroup B),(Campbell.V H).comap e⁆ ≠ ⊥ := by
  intro hz
  have hzero : ⁅e.range,Campbell.V H⁆=⊥ := by rw [←h.campbell_seed_map,hz,Subgroup.map_bot]
  have hc := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  obtain ⟨v,hv,hvn⟩ := h.exists_campbell_nonfixed_point hB
  exact hvn (hc hv)

end CFSG.Quasithin.ChapterC.GlaubermanNiles
