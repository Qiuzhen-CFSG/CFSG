module
public import Theory.SpecificGroups.SymmetricFive.CubicSelection
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.PCoreActionCardKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.CommutatorImage
/-!
# The original selected cubic in C.1.23

The two-residual of the S₃ preimage inside L maps onto the actual C₃.
It is normalized by the marked Thompson four-group and the action kernel.
Its intersection with R is Sylow, and it generates H together with R.
The two-group kernel is derived from the original L/O₂(L) cardinality.
Source: Aschbacher–Smith C.1.23(1), printed p.130.
-/
@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
open Theory.SpecificGroups.SymmetricFive Theory.SpecificGroups.SymmetricFive.CubicSelection
variable {H : Type*} [Group H] [Finite H]

noncomputable def selectedPreimage (q : H →* Sym) (L : Subgroup H) : Subgroup H :=
  L ⊓ symmetricThree.comap q
noncomputable def selectedResidual (q : H →* Sym) (L : Subgroup H) : Subgroup H :=
  (pResidual 2 (selectedPreimage q L)).map (selectedPreimage q L).subtype

omit [Finite H] in
theorem selectedPreimage_eq (q : H →* Sym) (L : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5)) :
    selectedPreimage q L = L ⊓ cubic.comap q := by
  ext x
  change x∈L ∧ q x∈symmetricThree ↔ x∈L ∧ q x∈cubic
  constructor
  · rintro ⟨hx,hs⟩
    refine ⟨hx,?_⟩
    rw [←three_inf_alternating]
    exact ⟨hs,hL ▸ mem_map_of_mem q hx⟩
  · rintro ⟨hx,hc⟩
    rw [←three_inf_alternating] at hc
    exact ⟨hx,hc.1⟩

omit [Finite H] in
theorem selectedPreimage_image (q : H →* Sym) (L : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5)) :
    (selectedPreimage q L).map q = cubic := by
  rw [selectedPreimage_eq q L hL]
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact hx.2
  · intro g hg
    obtain ⟨x,hx,rfl⟩ := (hL ▸ cubic_le_alternating hg : g∈L.map q)
    exact ⟨x,⟨hx,hg⟩,rfl⟩

theorem selectedResidual_image (q : H →* Sym) (L : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5)) :
    (selectedResidual q L).map q = cubic := by
  change ((pResidual 2 (selectedPreimage q L)).map (selectedPreimage q L).subtype).map q = _
  rw [map_embedded_pResidual,selectedPreimage_image q L hL,cubic_residual,←MonoidHom.range_eq_map,range_subtype]

omit [Finite H] in
theorem selectedResidual_le (q : H →* Sym) (L : Subgroup H) :
    selectedResidual q L ≤ L := (map_subtype_le _).trans inf_le_left

theorem selectedResidual_twoPerfect (q : H →* Sym) (L : Subgroup H) :
    IsPPerfect 2 (selectedResidual q L) := isPPerfect_embedded_pResidual 2 _

omit [Finite H] in
theorem selectedResidual_normalized (q : H →* Sym) (L : Subgroup H) [L.Normal]
    (hL : L.map q = alternatingGroup (Fin 5)) :
    OuterFourGeometry.four.comap q ≤ normalizer (selectedResidual q L : Set H) := by
  apply le_trans ?_ (normalizer_le_normalizer_characteristic_image
    (selectedPreimage q L) (pResidual 2 (selectedPreimage q L)))
  rw [selectedPreimage_eq q L hL]
  apply le_trans ?_ inf_normalizer_le_normalizer_inf
  refine le_inf le_normalizer_of_normal ?_
  exact (comap_mono four_normalizes_cubic).trans (le_normalizer_comap q)

theorem selectedResidual_generates (q : H →* Sym) (L R : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hR : R.map q = OuterFourGeometry.eight) (hk : q.ker ≤ R) :
    selectedResidual q L ⊔ R = ⊤ := by
  have he : (selectedResidual q L ⊔ R).map q = ⊤ := by
    rw [Subgroup.map_sup,selectedResidual_image q L hL,hR,cubic_sup_eight]
  have hc := congrArg (comap q) he
  simpa only [comap_map_eq,comap_top,sup_eq_left.mpr (hk.trans le_sup_right)] using hc

theorem selectedResidual_sylow (q : H →* Sym) (L : Subgroup H)
    (hL : L.map q = alternatingGroup (Fin 5)) (R : Sylow 2 H)
    (hk : q.ker ≤ R) :
    ∃ P : Sylow 2 (selectedResidual q L),
      (P : Subgroup (selectedResidual q L)) = (R : Subgroup H).subgroupOf (selectedResidual q L) := by
  let Y := selectedResidual q L
  let P : Sylow 2 Y := Classical.choice inferInstance
  have hp : IsPGroup 2 (((P : Subgroup Y).map Y.subtype).map q) :=
    (P.isPGroup'.map Y.subtype).map q
  have hc : IsPGroup 3 cubic := IsPGroup.of_card (n:=1) (by simpa using cubic_card)
  have hd := hp.disjoint_of_coprime hc (by decide : Nat.Coprime 2 3)
  have hle : ((P : Subgroup Y).map Y.subtype).map q ≤ cubic := by
    rw [←selectedResidual_image q L hL]
    exact map_mono (map_subtype_le _)
  have hb : ((P : Subgroup Y).map Y.subtype).map q = ⊥ :=
    le_bot_iff.mp ((le_inf le_rfl hle).trans_eq hd.eq_bot)
  have hPR : (P : Subgroup Y) ≤ (R : Subgroup H).subgroupOf Y := by
    intro y hy
    apply hk
    apply MonoidHom.mem_ker.mpr
    exact mem_bot.mp (hb ▸ mem_map_of_mem q (mem_map_of_mem Y.subtype hy))
  exact ⟨P,(P.is_maximal' R.isPGroup'.comap_subtype hPR).symm⟩

/-- The action kernel is a two-group from the actual component quotient order. -/
theorem action_kernel_twoGroup (q : H →* Sym) (L R : Subgroup H) [L.Normal]
    (hprod : L ⊔ R = ⊤) (hR : IsPGroup 2 R)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hcard : Nat.card (L ⧸ pCore 2 L) = Nat.card (alternatingGroup (Fin 5))) :
    IsPGroup 2 q.ker := by
  apply q.isPGroup_ker_of_card_image_eq_core_quotient L
    (isPGroup_quotient_of_sup_eq_top L R hR hprod)
  rw [hL,hcard]

/-- The literal selected cubic has the source normalization, Sylow and generation
properties once the original action is marked. -/
theorem selected_cubic_source (q : H →* Sym) (L : Subgroup H) [L.Normal]
    (R : Sylow 2 H) (B : Subgroup H)
    (hprod : L ⊔ (R : Subgroup H) = ⊤)
    (hL : L.map q = alternatingGroup (Fin 5))
    (hR : (R : Subgroup H).map q = OuterFourGeometry.eight)
    (hB : B.map q = OuterFourGeometry.four)
    (hcard : Nat.card (L ⧸ pCore 2 L) = Nat.card (alternatingGroup (Fin 5))) :
    IsPPerfect 2 (selectedResidual q L) ∧ selectedResidual q L ≤ L ∧
    (selectedResidual q L).map q = cubic ∧
    B ⊔ q.ker ≤ normalizer (selectedResidual q L : Set H) ∧
    (∃ P : Sylow 2 (selectedResidual q L),
      (P : Subgroup (selectedResidual q L)) = (R : Subgroup H).subgroupOf (selectedResidual q L)) ∧
    selectedResidual q L ⊔ (R : Subgroup H) = ⊤ := by
  have hk := action_kernel_twoGroup q L R hprod R.isPGroup' hL hcard
  have hkR : q.ker ≤ R := hk.le_sylow_of_normal R
  refine ⟨selectedResidual_twoPerfect q L,selectedResidual_le q L,
    selectedResidual_image q L hL,?_,selectedResidual_sylow q L hL R hkR,
    selectedResidual_generates q L R hL hR hkR⟩
  apply le_trans ?_ (selectedResidual_normalized q L hL)
  refine sup_le (map_le_iff_le_comap.mp hB.le) ?_
  intro g hg
  change q g∈OuterFourGeometry.four
  rw [MonoidHom.mem_ker.mp hg]
  exact one_mem _
/-- The genuine image inversion lifts to the source residual commutator
identity through the original two-group kernel. -/
theorem selectedResidual_eq_commutator (q : H →* Sym) (L J : Subgroup H) [L.Normal]
    (hL : L.map q = alternatingGroup (Fin 5)) (hJ : J.map q = OuterFourGeometry.four)
    (hk : IsPGroup 2 q.ker) : selectedResidual q L = ⁅selectedResidual q L,J⁆ := by
  apply eq_commutator_of_isPPerfect_of_map_eq (selectedResidual q L) J
    (selectedResidual_twoPerfect q L) ?_ q hk
  · rw [selectedResidual_image q L hL,hJ]
    exact cubic_eq_commutator_four
  · exact (map_le_iff_le_comap.mp hJ.le).trans (selectedResidual_normalized q L hL)

/-- A canonical reduced module moved by the selected residual is also
moved by J; this discharges the solvable FF producer's movement input. -/
theorem selected_thompson_movement (q : H →* Sym) (L J V : Subgroup H) [L.Normal]
    [V.Normal] (hL : L.map q = alternatingGroup (Fin 5))
    (hJ : J.map q = OuterFourGeometry.four) (hk : IsPGroup 2 q.ker)
    (hm : ⁅V,selectedResidual q L⁆ ≠ ⊥) : ¬ J ≤ centralizer (V : Set H) := by
  intro hc
  apply hm
  rw [commutator_eq_bot_iff_le_centralizer]
  apply le_centralizer_iff.mpr
  rw [selectedResidual_eq_commutator q L J hL hJ hk]
  exact (commutator_le_right (selectedResidual q L) (centralizer (V : Set H))).trans'
    (commutator_mono le_rfl hc)

end CFSG.Quasithin.ChapterC.RankOne.FiveBlockSource
