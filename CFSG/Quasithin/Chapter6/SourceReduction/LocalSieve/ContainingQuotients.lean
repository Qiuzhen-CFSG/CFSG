module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.Containers
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import Theory.GroupTheory.CComponent.LocalImageEquality

/-!
# Proper containing quotients in the local Cartan sieve

The E.2.2 seed remains a proper local component in the image modulo O₂(Y).
If the images were equal, the quotient kernel lies in the original full
Sylow, so local component minimality lifts equality. Their Sylow orbits
would then coincide, contradicting Cartan escape. This retains moved seeds.

The Bender, even special-unitary, A₅, A₆ and 3.A₆ quotient rows have no
proper local component with the full Sylow. Their actual model equivalences
therefore exclude each of these containing rows. The quotient is the
intrinsic C/O₂(C), identified with the literal image in Y/O₂(Y).

Source: Aschbacher--Smith A.3.12 and 5.1.12--13, printed pp.47--48,635--636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- Escape forces the seed to remain proper in the containing two-core image,
including when the seed is exchanged by the Sylow subgroup. -/
theorem seed_image_lt_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
      C.map (QuotientGroup.mk' (pCore 2 Y)) := by
  have hKY := hKH.trans hY.2
  have hTY := hTH.trans hY.2
  let S := T.subtype hTY
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTY hKY).mp ⟨hKY,hK⟩
  have hKC' : K.subgroupOf Y ≤ C := by
    change K.comap Y.subtype ≤ C
    have hh := comap_mono (f := Y.subtype) hKC
    simpa only [comap_map_eq_self_of_injective Y.subtype_injective] using hh
  have ho : residual H ≤ componentOrbit (C.map Y.subtype) (T : Subgroup G) := by
    rw [←horbit]
    exact iSup_mono fun _ => map_mono hKC
  have hlt := (containing_orbit_normal_and_strict hG hTH hY C hC ho hescape).2
  refine lt_of_le_of_ne (map_mono hKC') ?_
  intro he
  have hk : (QuotientGroup.mk' (pCore 2 Y)).ker ≤ (S : Subgroup Y) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  have heC := local_cComponent_eq_of_map_eq hl.1 hC hKC'
    (QuotientGroup.mk' (pCore 2 Y)) hk he
  have heK : K = C.map Y.subtype := by
    simpa only [map_subgroupOf_eq_of_le hKY] using congrArg (map Y.subtype) heC
  exact hlt.ne (by rw [←heK,horbit])

/-- A proper containing component in the escaping branch cannot have a Bender quotient. -/
theorem not_bender_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    ¬ ClassificationModels.IsBenderModel (C ⧸ pCore 2 C) := by
  intro hm
  let S := T.subtype (hTH.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let := pCore_isNilpotent (p := 2) (G := Y)
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlq : (K.subgroupOf Y).map q ∈
      localCComponents (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) : Subgroup (Y ⧸ pCore 2 Y)) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  exact hlt.ne (eq_of_bender_containing_component _ hlq (hC.map_quotient _) hlt.le
    (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm))

/-- The even special-unitary cover has the same full-Sylow non-enlargement obstruction. -/
theorem not_binary_su3_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (m : ℕ) (hm : 0 < m) : ¬ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m) := by
  intro hmodel
  let S := T.subtype (hTH.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let := pCore_isNilpotent (p := 2) (G := Y)
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlq : (K.subgroupOf Y).map q ∈
      localCComponents (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) : Subgroup (Y ⧸ pCore 2 Y)) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  have hmodel' : IsSU (C.map q) 3 (2 ^ m) := by
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hmodel
    exact ⟨F,inferInstance,inferInstance,J,hF,hconj,
      ⟨(cComponentTwoCoreQuotientEquiv hC).symm.trans e⟩⟩
  exact hlt.ne (eq_of_binary_su3_containing_component _ hlq (hC.map_quotient _)
    hlt.le hm hmodel')

/-- A₅, A₆ and the central triple cover of A₆ cannot contain the escaping seed properly. -/
theorem not_small_alternating_container
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    ¬ (IsAlternating (C ⧸ pCore 2 C) 5 ∨ IsAlternating (C ⧸ pCore 2 C) 6 ∨
      IsAlternatingCover (C ⧸ pCore 2 C) 6) := by
  intro hm
  let S := T.subtype (hTH.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let := pCore_isNilpotent (p := 2) (G := Y)
  have hl : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlq : (K.subgroupOf Y).map q ∈
      localCComponents (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y)) : Subgroup (Y ⧸ pCore 2 Y)) := by
    simpa only [Sylow.coe_mapSurjective] using
      Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hl
  have hlt := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  let e := (cComponentTwoCoreQuotientEquiv hC).symm
  have hm' : IsAlternating (C.map q) 5 ∨ IsAlternating (C.map q) 6 ∨
      IsAlternatingCover (C.map q) 6 := by
    rcases hm with hm | hm | ⟨hq,⟨ez⟩,⟨eq⟩⟩
    · exact .inl (hm.map fun a => e.trans a)
    · exact .inr (.inl (hm.map fun a => e.trans a))
    · let := hq
      let ec := QuotientGroup.congr (center (C.map q)) (center (C ⧸ pCore 2 C)) e (by
        apply le_antisymm
        · rintro _ ⟨x,hx,rfl⟩
          exact (centerCongr e ⟨x,hx⟩).property
        · intro y hy
          exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)
      exact .inr (.inr ⟨IsQuasisimple.of_mulEquiv e.symm,
        ⟨(centerCongr e).trans ez⟩,⟨ec.trans eq⟩⟩)
  exact hlt.ne (eq_of_small_alternating_containing_component _ hlq
    (hC.map_quotient _) hlt.le hm')

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
