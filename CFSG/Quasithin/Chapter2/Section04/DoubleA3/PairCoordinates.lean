module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SylowSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup

/-!
# Correlated cubic blocks and their fixed involutions

The actual index-two Sylow overgroup supplies the original C.5 configuration.
Both blocks, all four modules, and the two conjugating elements are retained
in one selected witness. The common fixed subgroup of each cubic module has
order two: its index follows from the natural action, and the full fixed
subgroup equals the intersection with the opposite module. The original
outside conjugator fixes both involutions and the block exchanger interchanges
them. These are the literal involutions used in the centralizers in 2.4.31–37.

Source: Aschbacher–Smith 2.4.30 and the paragraph following it, printed p.547;
C.5.6 and C.6.1, printed pp.156–165.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original paired cubic configuration, selected using the actual Sylow T. -/
structure SourcePairCoordinates (d : MinimalBlockSetup M) (T : Sylow 2 G) where
  L : Subgroup G
  F : Type
  F' : Type
  field : Field F
  field' : Field F'
  original : OriginalHypotheses d.H T (d.block.map d.H.subtype ⊔ L)
    ((d.S : Subgroup d.H).map d.H.subtype) ((d.S : Subgroup d.H).map d.H.subtype)
  first : @RankOne.Setup G _ ((d.S : Subgroup d.H).map d.H.subtype)
    (d.block.map d.H.subtype) F field
  second : @RankOne.Setup G _ ((d.S : Subgroup d.H).map d.H.subtype) L F' field'
  cubic_first : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3
  cubic_second : ChapterC.IsAlternatingBlock L 3
  commute : L ≤ centralizer (d.block.map d.H.subtype : Set G)
  residual : d.L0.map d.H.subtype = d.block.map d.H.subtype ⊔ L
  pair : ∀ r ∈ (d.S : Subgroup d.H).map d.H.subtype,
    (d.block.map d.H.subtype).conjBy r = d.block.map d.H.subtype ∨
      (d.block.map d.H.subtype).conjBy r = L
  s : G
  s_mem : s ∈ (d.S : Subgroup d.H).map d.H.subtype
  exchange : (d.block.map d.H.subtype).conjBy s = L
  x : G
  x_mem : x ∈ (T : Subgroup G)
  noncommuting : ¬ (sourceModule (d.block.map d.H.subtype)).map
    (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule (d.block.map d.H.subtype) : Set G)
  index : ((d.S : Subgroup d.H).map d.H.subtype).relIndex (T : Subgroup G) = 2
  baumann : ChapterB.baumann ((d.S : Subgroup d.H).map d.H.subtype) = sourceR d
  core : ((d.S : Subgroup d.H).map d.H.subtype) ⊓
    centralizer ((sourceModule (d.block.map d.H.subtype) ⊔ sourceModule L : Subgroup G) : Set G) = twoCore d.H

attribute [instance] SourcePairCoordinates.field SourcePairCoordinates.field'

namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)
noncomputable abbrev U₁ (_c : SourcePairCoordinates d T) : Subgroup G := sourceModule (d.block.map d.H.subtype)
noncomputable abbrev U₂ : Subgroup G := sourceModule c.L
noncomputable abbrev V₁ : Subgroup G := c.U₁.map (MulAut.conj c.x⁻¹).toMonoidHom
noncomputable abbrev V₂ : Subgroup G := c.U₂.map (MulAut.conj c.x⁻¹).toMonoidHom
noncomputable abbrev D : Subgroup G := ((d.S : Subgroup d.H).map d.H.subtype) ⊓
  centralizer ((d.block.map d.H.subtype ⊔ c.L : Subgroup G) : Set G)

 theorem orbit : FourModuleOrbit.SourceInputs (T : Subgroup G)
    ((d.S : Subgroup d.H).map d.H.subtype) c.U₁ c.U₂ c.x :=
  c.first.fourModuleSourceInputs c.commute c.second.module_le T
    ((d.S : Subgroup d.H).map d.H.subtype) c.x c.x_mem (c.original.R_normal c.x_mem)
    c.index c.pair ⟨⟨c.s,c.original.T_le c.s_mem⟩,c.s_mem,c.exchange⟩ c.noncommuting

 theorem four_family :
    elementaryAbelianMaxSubgroups ((d.S : Subgroup d.H).map d.H.subtype) =
      {twoCore d.H,(twoCore d.H).map (MulAut.conj c.x⁻¹).toMonoidHom,
       (c.U₁ ⊔ c.V₂) ⊔ c.D,(c.V₁ ⊔ c.U₂) ⊔ c.D} :=
  (ChapterC.Section06.rankOne_pair_family_from_original c.original c.first c.second c.commute
    c.pair ⟨⟨c.s,c.original.T_le c.s_mem⟩,c.s_mem,c.exchange⟩ c.core c.index c.x c.x_mem
      c.noncommuting).2.2.2.2.2.2

 theorem x_outside : c.x ∉ (d.S : Subgroup d.H).map d.H.subtype := c.orbit.x_outside

end SourcePairCoordinates

private theorem cubic_fixed_line {S K : Subgroup G} {F : Type*} [Field F]
    (h : RankOne.Setup S K F) (hK : ChapterC.IsAlternatingBlock K 3)
    {x : G} (hx : x ∈ normalizer (S : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (RankOne.U K : Set G)) :
    let I := RankOne.U K ⊓ centralizer (ChapterB.baumann S : Set G)
    Nat.card I = 2 ∧
      I = RankOne.U K ⊓ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ∧
      x ∈ centralizer (I : Set G) := by
  let V := (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hc := h.commutator_eq_fixed hx hnc
  have he : RankOne.U K ⊓ centralizer (ChapterB.baumann S : Set G) = RankOne.U K ⊓ V := by
    apply le_antisymm
    · exact (inf_le_inf_left _ (centralizer_le (h.conjugate_le hx))).trans
        (hc.1.symm.trans hc.2).le
    · rw [←hc.2]
      exact (commutator_mono le_rfl (h.conjugate_le hx)).trans
        (RankOne.commutator_le_fixed h.coordinates h.fixedLift)
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G)
    (RankOne.U K ⊓ centralizer (V : Set G)) (RankOne.U K) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,
    RankOne.module_index_of_fixedLift h.coordinates h.fixedLift _ (h.conjugate_le hx) hnc,
    h.cubic_field_card hK,h.cubic_module_card hK,hc.1.symm.trans hc.2] at hm
  change Nat.card (RankOne.U K ⊓ V : Subgroup G) * 2 = 4 at hm
  have hcard : Nat.card (RankOne.U K ⊓ V : Subgroup G) = 2 := by omega
  refine ⟨he ▸ hcard,he,?_⟩
  apply normalizer_le_centralizer_of_card_two _ (he ▸ hcard)
  have hs := h.commutator_structure hx hnc
  have hE : ⁅RankOne.U K,RankOne.S S⁆ =
      RankOne.U K ⊓ centralizer (ChapterB.baumann S : Set G) := hs.2.2.1.trans he.symm
  have hn : x⁻¹ ∈ normalizer ((RankOne.U K ⊓ centralizer (ChapterB.baumann S : Set G) : Subgroup G) : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←hE]
    exact hs.2.2.2
  simpa only [inv_inv] using (normalizer ((RankOne.U K ⊓ centralizer (ChapterB.baumann S : Set G) : Subgroup G) : Set G)).inv_mem hn

namespace SourcePairCoordinates
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} (c : SourcePairCoordinates d T)

 theorem first_fixed_line :
    Nat.card (c.U₁ ⊓ centralizer (sourceR d : Set G) : Subgroup G) = 2 ∧
      c.U₁ ⊓ centralizer (sourceR d : Set G) = c.U₁ ⊓ c.V₁ ∧
      c.x ∈ centralizer ((c.U₁ ⊓ centralizer (sourceR d : Set G) : Subgroup G) : Set G) := by
  have h := cubic_fixed_line c.first c.cubic_first (c.original.R_normal c.x_mem) c.noncommuting
  rw [c.baumann] at h
  exact h

 theorem second_fixed_line :
    Nat.card (c.U₂ ⊓ centralizer (sourceR d : Set G) : Subgroup G) = 2 ∧
      c.U₂ ⊓ centralizer (sourceR d : Set G) = c.U₂ ⊓ c.V₂ ∧
      c.x ∈ centralizer ((c.U₂ ⊓ centralizer (sourceR d : Set G) : Subgroup G) : Set G) := by
  have h := cubic_fixed_line c.second c.cubic_second (c.original.R_normal c.x_mem)
    (RankOne.second_noncommuting c.orbit)
  rw [c.baumann] at h
  exact h

/-- Two actual fixed involutions, exchanged by the original block conjugator.
The chosen x centralizes both, so the marked centralizers use the same actors. -/
theorem exists_fixed_involutions :
    ∃ z₁ z₂ : G, orderOf z₁ = 2 ∧ orderOf z₂ = 2 ∧ z₁ ≠ z₂ ∧
      z₁ ∈ c.U₁ ∧ z₂ ∈ c.U₂ ∧
      z₁ ∈ centralizer (sourceR d : Set G) ∧ z₂ ∈ centralizer (sourceR d : Set G) ∧
      c.s * z₁ * c.s⁻¹ = z₂ ∧
      c.x ∈ centralizer ({z₁} : Set G) ∧ c.x ∈ centralizer ({z₂} : Set G) := by
  let I := c.U₁ ⊓ centralizer (sourceR d : Set G)
  have hIcard : Nat.card I = 2 := c.first_fixed_line.1
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 (by rw [hIcard])
  let z₁ : G := z
  let z₂ : G := c.s * z₁ * c.s⁻¹
  have hz₁ : orderOf z₁ = 2 := (Subgroup.orderOf_coe z).trans hz
  have hz₂ : orderOf z₂ = 2 := (MulEquiv.orderOf_eq (MulAut.conj c.s) z₁).trans hz₁
  have hz₁U : z₁ ∈ c.U₁ := z.property.1
  have hz₁R : z₁ ∈ centralizer (sourceR d : Set G) := z.property.2
  have hsU : c.U₁.map (MulAut.conj c.s).toMonoidHom = c.U₂ :=
    (sourceModule_map_equiv (d.block.map d.H.subtype) (MulAut.conj c.s)).trans
      (congrArg sourceModule c.exchange)
  have hz₂U : z₂ ∈ c.U₂ := hsU ▸ mem_map_of_mem (MulAut.conj c.s).toMonoidHom hz₁U
  have hsR : c.s ∈ normalizer (sourceR d : Set G) :=
    normalizer_le_normalizer_elementaryAbelianMaxJ _
      (((d.S : Subgroup d.H).map d.H.subtype).le_normalizer c.s_mem)
  have hRC : (centralizer (sourceR d : Set G)).map (MulAut.conj c.s).toMonoidHom ≤
      centralizer (sourceR d : Set G) := by
    have hh := map_centralizer_le_centralizer_image (sourceR d : Set G) (MulAut.conj c.s).toMonoidHom
    have hmap : (sourceR d).map (MulAut.conj c.s).toMonoidHom = sourceR d :=
      mem_normalizer_iff_map_conj_eq.mp hsR
    simpa only [←Subgroup.coe_map,hmap] using hh
  have hz₂R : z₂ ∈ centralizer (sourceR d : Set G) :=
    hRC (mem_map_of_mem (MulAut.conj c.s).toMonoidHom hz₁R)
  have hne : z₁ ≠ z₂ := by
    intro he
    have hd := RankOne.cubic_module_disjoint c.cubic_first c.U₂
      ((map_subtype_le _).trans c.commute)
    have hh : z₁ = 1 := disjoint_def.mp hd hz₁U (he ▸ hz₂U)
    rw [hh,orderOf_one] at hz₁
    omega
  exact ⟨z₁,z₂,hz₁,hz₂,hne,hz₁U,hz₂U,hz₁R,hz₂R,rfl,
    mem_centralizer_singleton_iff.mpr (c.first_fixed_line.2.2 z₁ ⟨hz₁U,hz₁R⟩).symm,
    mem_centralizer_singleton_iff.mpr (c.second_fixed_line.2.2 z₂ ⟨hz₂U,hz₂R⟩).symm⟩

end SourcePairCoordinates

end CFSG.Quasithin.Chapter2.DoubleA3
namespace CFSG.Quasithin.Chapter2
open ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.paired_cubic_coordinates
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    Nonempty (SourcePairCoordinates d T) := by
  have hi := d.paired_cubic_sylow_index_two hG T hM hTM hu hST hpair hL
  obtain ⟨L,c,F,F',hF,hF',h,h',hL',hKL,hjoin,hperm,ht,x,hx,hnc⟩ :=
    d.cubic_pair_configuration hG T hST.le hpair hL T hST.le le_rfl hi.1
  obtain ⟨s,hs,hsL⟩ := ht
  have ht' : ∃ t ∈ (d.S : Subgroup d.H).map d.H.subtype,
      (d.block.map d.H.subtype).conjBy t = L := ⟨s,hs,hsL⟩
  have hcl := d.two_block_closures L hperm ht'
  have hfull := d.two_block_core_centralizer L h.short h'.short hKL hperm ht'
  rw [hcl.2] at hfull
  exact ⟨⟨L,F,F',hF,hF',c,h,h',hL,hL',hKL,hjoin,hperm,s,hs,hsL,x,hx,hnc,hi.1,
    (d.cubic_pair_global_source hG T hST hpair hL).2.1,hfull⟩⟩
end CFSG.Quasithin.Chapter2
