module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmallIntersection
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.StrictCubeInvariant
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SeedIntersectionIndex
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowSmallMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.NonelementaryMovers

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPairedFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal

/-!
# Strict reverse slices in the image-sixteen branch

A reverse slice of index greater than two forces the full intersection of
neighboring seeds to be fixed by the actual three-transposition cube. Pulling
the moved intersection back along the literal endpoint embedding gives an
invariant subspace containing the radical fixed space. The strict index bound
and the natural-or-core cover identify it as cube-fixed. Central generation
then restores the full seed intersection, including its central attachment.

For two compatible edges, the two actual cubes generate the midpoint
stabilizer, so their common full-seed triple is central there. Both reverse
strict inequalities remain explicit: a forward strict slice alone does not
supply these hypotheses, and no equality of the opposite movers is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (5.5) and (5.12), printed
pp.915,924--927. This is the conditional graph application of the
six-letter strict invariant-subspace calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative Pointwise commutatorElement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "S" => Equiv.Perm (Fin 6)
local notation "cube" => Theory.SpecificGroups.SymmetricSix.BinaryFlags.D

private theorem cube_eq : cube = D 6 := by
  unfold Theory.SpecificGroups.SymmetricSix.BinaryFlags.D CFSG.Quasithin.ChapterB.Offenders.D disjointTranspositions
  congr 1
  ext g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,by decide,rfl⟩
    · exact ⟨1,by decide,rfl⟩
    · exact ⟨2,by decide,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    fin_cases i <;> simp [pairSwap,swap01,swap23,swap45]

private theorem sylow_le_duad : sylowCarrier ≤ H1 := by
  intro r hr
  obtain ⟨i,rfl⟩ := (mem_sylowCarrier_iff r).mp hr
  have cert : ∀ i : Fin 16, sylowWords i ∈ H1 := by decide +kernel
  exact cert i

private theorem model_fixed_transport {M N : Type*}
    [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) S M) (τ : Representation (ZMod 2) S N)
    (E : M ≃ₗ[ZMod 2] N) (hE : ∀ g v, E (σ g v) = τ g (E v))
    (R J : Subgroup S) (W : Submodule (ZMod 2) M)
    (hsmall : 2 * Nat.card W < Nat.card M)
    (hfix : fixedSpace σ R ≤ W)
    (hinv : ∀ r ∈ R, ∀ x ∈ W, σ r x ∈ W)
    (hmodel : ∀ V : Submodule (ZMod 2) N,
      2 * Nat.card V < Nat.card N → fixedSpace τ R ≤ V →
      (∀ r ∈ R, ∀ x ∈ V, τ r x ∈ V) → V ≤ fixedSpace τ J) :
    W ≤ fixedSpace σ J := by
  let V := W.map E.toLinearMap
  have hVsmall : 2 * Nat.card V < Nat.card N := by
    have hWV : Nat.card V ≤ Nat.card W := Nat.card_le_card_of_surjective
      (fun w : W => (⟨E w.val,⟨w.val,w.property,rfl⟩⟩ : V))
      (by rintro ⟨v,w,hw,rfl⟩; exact ⟨⟨w,hw⟩,rfl⟩)
    rw [←Nat.card_congr E.toEquiv]
    omega
  have hVfix : fixedSpace τ R ≤ V := by
    intro x hx
    refine ⟨E.symm x,?_,E.apply_symm_apply x⟩
    apply hfix
    intro r
    apply E.injective
    change E (σ r.val (E.symm x)) = E (E.symm x)
    rw [hE,E.apply_symm_apply]
    exact hx r
  have hVinv : ∀ r ∈ R, ∀ x ∈ V, τ r x ∈ V := by
    intro r hr x hx
    obtain ⟨v,hv,rfl⟩ := hx
    exact ⟨σ r v,hinv r hr v hv,(hE r v)⟩
  have hVc := hmodel V hVsmall hVfix hVinv
  intro v hv j
  apply E.injective
  exact (hE j.val v).trans (hVc ⟨v,hv,rfl⟩ j)

private theorem cover_strict_cube_fixed (s : FullSymmetricAction h e hz hn d)
    (u : S) (hRimage : d.radical.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom)
    (J : Subgroup d.overgroup)
    (hJimage : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    (H : Subgroup d.overgroup) (hHU : H ≤ replacementMoved d)
    (hstrict : 2 < H.relIndex (replacementMoved d))
    (hfix : replacementMoved d ⊓ centralizer (d.radical : Set d.overgroup) ≤ H)
    (hnorm : d.radical ≤ normalizer (H : Set d.overgroup)) :
    H ≤ centralizer (J : Set d.overgroup) := by
  let := replacementMoved_normal h d
  let U₀ := replacementMoved d
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHU
  let σ := coverAction s
  let W := NormalElementaryQuotient.subgroupSpace U₀ H
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hcard : Nat.card H * H.relIndex U₀ = Nat.card U₀ := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup d.overgroup) H U₀ bot_le hHU
    simpa only [relIndex_bot_left] using hh
  have hWsmall : 2 * Nat.card W < Nat.card (Additive U₀) := by
    have hWH : Nat.card W = Nat.card H :=
      (Nat.card_congr (NormalElementaryQuotient.subgroupSpaceEquiv U₀ H hHU).toEquiv).symm
    rw [hWH]
    have hHpos : 0 < Nat.card H := Nat.card_pos
    change 2 * Nat.card H < Nat.card U₀
    nlinarith
  have hWfix : fixedSpace σ (d.radical.map s.projection) ≤ W := by
    intro v hv
    exact hfix ⟨v.toMul.property,
      (NormalElementaryQuotient.mem_fixedSpace_image U₀ s.projection s.surjective hker d.radical v).mp hv⟩
  have hWinv : ∀ r ∈ d.radical.map s.projection, ∀ x ∈ W, σ r x ∈ W := by
    rintro r ⟨g,hg,rfl⟩ v hv
    change ((σ (s.projection g) v).toMul : d.overgroup) ∈ H
    rw [coverAction_conjugate]
    exact (mem_normalizer_iff.mp (hnorm hg) _).mp hv
  have hDR : cube ≤ sylowCarrier := cube_eq ▸ D_le_sylowCarrier
  have hWcube : W ≤ fixedSpace σ (J.map s.projection) := by
    rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
    · apply model_fixed_transport σ (naturalRepresentation (Fin 6)) E hE
        (d.radical.map s.projection) (J.map s.projection) W hWsmall hWfix hWinv
      intro V hVcard hVfix hVinv
      rw [hRimage] at hVfix hVinv
      rw [hJimage,←cube_eq]
      apply StrictCubeInvariant.natural_conjugate_le_fixed sylowCarrier hDR sylow_le_duad u V _ hVfix hVinv
      have hc : Nat.card (BinaryPermutation.natural (Fin 6)) = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),finrank_natural_even (Fin 6) (by decide)]
        norm_num
      rw [hc] at hVcard
      omega
    · apply model_fixed_transport σ (coreRepresentation (Fin 6)) E hE
        (d.radical.map s.projection) (J.map s.projection) W hWsmall hWfix hWinv
      intro V hVcard hVfix hVinv
      rw [hRimage] at hVfix hVinv
      rw [hJimage,←cube_eq]
      apply StrictCubeInvariant.core_conjugate_le_fixed sylowCarrier hDR sylow_le_duad u V _ hVfix hVinv
      have hc : Nat.card (BinaryPermutation.core (Fin 6)) = 32 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),finrank_core]
        norm_num
      rw [hc] at hVcard
      omega
  intro x hx
  let v : Additive U₀ := Additive.ofMul ⟨x,hHU hx⟩
  exact (NormalElementaryQuotient.mem_fixedSpace_image U₀ s.projection s.surjective hker J v).mp
    (hWcube hx)


include e hz hn in
/-- A strict reverse slice fixes the full seed intersection under the
actual edge cube, with no equality of the two movers assumed. -/
theorem sixteen_reverse_strict_seed_fixed_of_seed_index_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (hstrict : 2 < (Z d.radical c).relIndex (U d.radical a)) :
    Z d.radical a ⊓ Z d.radical c ≤ centralizer
      (SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases hh' : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases hh' : color d.radical c <;> simp_all
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧ d.radical.map i = Q d.radical t ∧
      (pCore 2 d.overgroup).map i = Q d.radical a ∧
      (replacementMoved d).map i = U d.radical a := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
    · rcases hg with ⟨hga,hgt⟩
      rw [hga,hgt]
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · rw [MonoidHom.range_comp]
        have he : (embedM d.radical).range = stabilizer d.radical (alpha d.radical) :=
          (stabilizer_m_base d.radical).symm
        rw [he]
        simpa only [alpha,act_mVertex,one_mul] using (stabilizer_act d.radical g (alpha d.radical)).symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hcent.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at ha
      cases ha
  obtain ⟨i,hinj,hir,hiR,hiQ,hiU⟩ := hcoords
  have hpos : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a ha) := by
    rw [(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d
  let U₀ := replacementMoved d
  let V := (Z d.radical c).comap i
  let Z₀ := (Z d.radical a).comap i
  let H := U₀ ⊓ V
  let J₀ := SmallMover.join U₀ (pCore 2 d.overgroup) d.radical 4
  let J := SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4
  have hJmap : J₀.map i = J := by
    rw [SmallMover.join_map i hinj,hiU,hiQ,hiR]
  have hZrange : Z d.radical a ≤ i.range := (Z_le_stabilizer d.radical a).trans_eq hir.symm
  have hZmap : Z₀.map i = Z d.radical a := map_comap_eq_self hZrange
  have hHmap : H.map i = U d.radical a ⊓ Z d.radical c := by
    rw [Subgroup.map_inf U₀ V i hinj,hiU,Subgroup.map_comap_eq]
    rw [←inf_assoc]
    have hUr : U d.radical a ≤ i.range := hiU ▸ map_le_range i U₀
    rw [show U d.radical a ⊓ i.range = U d.radical a from inf_eq_left.mpr hUr]
  have hHstrict : 2 < H.relIndex U₀ := by
    let := finite_Z d.radical a
    let : Finite (U d.radical a) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
    rw [←relIndex_map_map_of_injective H U₀ hinj,hiU]
    exact hstrict.trans_le (relIndex_le_of_le_left
      (hHmap.le.trans inf_le_right)
      index_ne_zero_of_finite)
  have hfix : U₀ ⊓ centralizer (d.radical : Set d.overgroup) ≤ H := by
    rintro x ⟨hx,hxc⟩
    refine ⟨hx,?_⟩
    apply adjacent_Z_le d.radical hc hct
    rw [Z,if_neg (by simp [ht])]
    have hX : i x ∈ X d.radical a :=
      (DistanceEight.U_le_Z d.radical a).trans
        ((replacementGeometry h d).omega_bound a ha hpos)
        (hiU ▸ mem_map_of_mem i hx)
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hX
    refine mem_omegaCenter_iff.mpr ⟨?_,hx2,?_⟩
    · rw [←hiR]
      exact mem_map_of_mem i ((replacement_core_le_radical h d)
        ((mem_omegaCenterIn_iff _ _).mp (replacementMoved_le_omegaCenter h d hx)).1)
    · intro y hy
      rw [←hiR] at hy
      obtain ⟨r,hr,rfl⟩ := hy
      simpa only [←map_mul] using congrArg i (hxc r hr)
  have hnorm : d.radical ≤ normalizer (H : Set d.overgroup) := by
    intro r hr
    have hrt : i r ∈ Q d.radical t := hiR ▸ mem_map_of_mem i hr
    have hrG : i r ∈ stabilizer d.radical c := hrt.2 c (adjacent_symm d.radical hct)
    have hnV : r ∈ normalizer (V : Set d.overgroup) := by
      apply mem_normalizer_iff.mpr
      intro x
      have hh := mem_normalizer_iff.mp (Z_normalized d.radical c hrG) (i x)
      simpa only [V,mem_comap,map_mul,map_inv] using hh
    exact inf_normalizer_le_normalizer_inf
      ⟨by let := replacementMoved_normal h d; rw [normalizer_eq_top]; trivial,hnV⟩
  obtain ⟨u,hN,_,hj,himage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard
  have hJimage : J₀.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [hnormal] at hj himage
    rw [show J₀ = _ from hj]
    exact himage
  have hRimage : d.radical.map s.projection = sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    rwa [hnormal] at hN
  have hHfixed := cover_strict_cube_fixed s u hRimage J₀ hJimage H inf_le_left hHstrict hfix hnorm
  have hXZ := SylowPairedFixer.central_generation_eq_seed (h := h) ha hat hgen
  have hUZ : U₀ ≤ Z₀ := by
    intro x hx
    exact DistanceEight.U_le_Z d.radical a (hiU ▸ mem_map_of_mem i hx)
  have hZsup : Z₀ ≤ U₀ ⊔ center d.overgroup := by
    apply (map_le_map_iff_of_injective hinj).mp
    rw [Subgroup.map_sup,hiU,hZmap,←hXZ,hgen]
    refine sup_le le_sup_left (le_trans ?_ le_sup_right)
    intro x hx
    obtain ⟨y,hy⟩ := hZrange (hXZ ▸ hx.1)
    refine ⟨y,?_,hy⟩
    apply mem_center_iff.mpr
    intro r
    apply hinj
    simpa only [map_mul,hy] using (hx.2 (i r) (hir ▸ ⟨r,rfl⟩))
  have hCV : Z₀ ⊓ center d.overgroup ≤ V := by
    rintro x ⟨hx,hxc⟩
    apply adjacent_Z_le d.radical hc hct
    have hXa : Z d.radical a ≤ X d.radical a :=
      (replacementGeometry h d).omega_bound a ha hpos
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp (hXa hx)
    rw [Z,if_neg (by simp [ht])]
    refine mem_omegaCenter_iff.mpr ⟨?_,hx2,?_⟩
    · rw [←hiQ] at hxQ
      obtain ⟨r,hr,he⟩ := hxQ
      have he' : r=x := hinj he
      rw [←hiR]
      exact ⟨r,replacement_core_le_radical h d hr,he⟩
    · intro y hy
      rw [←hiR] at hy
      obtain ⟨r,hr,rfl⟩ := hy
      simpa only [←map_mul] using congrArg i (mem_center_iff.mp hxc r)
  have hlocal : Z₀ ⊓ V ≤ centralizer (J₀ : Set d.overgroup) := by
    rintro x ⟨hxZ,hxV⟩
    obtain ⟨w,hw,c,hcZ,rfl⟩ := mem_sup_of_normal_right.mp (hZsup hxZ)
    have hcZ₀ : c ∈ Z₀ := by
      have hh := Z₀.mul_mem (Z₀.inv_mem (hUZ hw)) hxZ
      simpa only [inv_mul_cancel_left] using hh
    have hcV := hCV ⟨hcZ₀,hcZ⟩
    have hwV : w ∈ V := by
      have hh := V.mul_mem hxV (V.inv_mem hcV)
      simpa only [mul_inv_cancel_right] using hh
    exact (centralizer (J₀ : Set d.overgroup)).mul_mem (hHfixed ⟨hw,hwV⟩)
      (fun j _ => mem_center_iff.mp hcZ j)
  intro x hx j hj
  obtain ⟨y,hy⟩ := hZrange hx.1
  have hyZ : y ∈ Z₀ := by change i y ∈ Z d.radical a; rw [hy]; exact hx.1
  have hyV : y ∈ V := by change i y ∈ Z d.radical c; rw [hy]; exact hx.2
  change j ∈ J at hj
  rw [←hJmap] at hj
  obtain ⟨k,hk,rfl⟩ := hj
  simpa only [map_mul,hy] using congrArg i (hlocal ⟨hyZ,hyV⟩ k hk)


include e hz hn in
/-- The reverse Baumann strictness hypothesis supplies the seed-index premise
used by the core cube-fixedness calculation. -/
theorem sixteen_reverse_strict_seed_fixed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (hstrict : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a)) :
    Z d.radical a ⊓ Z d.radical c ≤ centralizer
      (SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 : Set (FreeAmalgam d.radical)) := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  let := finite_Z d.radical c
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hseed : 2 < (Z d.radical c).relIndex (U d.radical a) := by
    exact hstrict.trans_le (relIndex_le_of_le_left
      (Escape.EdgeTransfer.Z_le_B hb c hc) index_ne_zero_of_finite)
  exact sixteen_reverse_strict_seed_fixed_of_seed_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb ha hat hct hgen hseed


include e hz hn in
/-- Forward Baumann strictness transfers across the adjacent endpoint seeds,
then invokes the same strict cube-fixedness calculation. -/
theorem sixteen_forward_strict_seed_fixed_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (hforward : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c ≤ centralizer
      (SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 : Set (FreeAmalgam d.radical)) := by
  have hseed := forward_strict_seed_index (h := h) (e := e) (hz := hz) hb ha hat hct hforward
  exact sixteen_reverse_strict_seed_fixed_of_seed_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb ha hat hct hgen hseed


include e hz hn in
/-- Original and selected cubes centralize the common full-seed triple
when both reverse slices are strict. This retains the literal generation
identity and does not compare the movers at the opposite endpoints. -/
theorem sixteen_reverse_strict_compatible_triple_central_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (hb : 2 < replacementDistance h d)
    {a v c b t : Vertex d.radical} (ha : color d.radical a = false)
    (hab : Adjacent d.radical a b) (hvb : Adjacent d.radical v b)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hgen : X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))))
    (hreverse0 : 2 < (B d.radical v ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a))
    (hreverse1 : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical a))
    (hcross : SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical b) 4 ⊔
      SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) 4 = stabilizer d.radical a) :
    Z d.radical v ⊓ Z d.radical a ⊓ Z d.radical c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  have h0 := sixteen_reverse_strict_seed_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb ha hab hvb hgen hreverse0
  have h1 := sixteen_reverse_strict_seed_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard hb ha hat hct hgen hreverse1
  apply le_centralizer_iff.mpr
  rw [←hcross]
  apply sup_le
  · apply le_centralizer_iff.mp
    exact (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)).trans h0
  · apply le_centralizer_iff.mp
    exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans h1

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
