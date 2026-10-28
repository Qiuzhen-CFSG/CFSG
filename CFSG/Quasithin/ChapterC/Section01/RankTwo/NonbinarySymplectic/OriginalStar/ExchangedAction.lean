module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.OriginalCriticalPair
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.DisplacementFactors

/-!
# The original critical exchange inside the center-action factors

Transport the paired minimum-graph comparison back into the ORIGINAL radical
R through its literal characteristic inclusion. The base normalizer two-core
is transported through the actual stabilizer equivalence, and the entire
fixed kernel A and displacement D are retained. For the same original
automorphism a supplying a critical pair, either A is preserved or a
exchanges A and D. In the latter case both full groups have order q and
are disjoint.

The selected source star T has its established original marking and
saturation. Let C be the full minimum center, B = R intersect M, and
Q₀ = T intersect O₂(H). The original factor dichotomy applies to the SAME
automorphism. Preservation of the B action would preserve D = [C,B],
contradicting exchange. Hence its entire order-q-squared action is carried
into the Q₀ action. In particular A is contained in [C,Q₀], the Q₀ action
has order at least q squared, and the full T action has order at least
q to the fourth power.

This identifies the surviving exchanged-kernel branch inside the actual
original action factors. It does not exclude that branch: no upper bound
below q to the fourth power has been proved for the full action. Minimum
marked preservation and saturation, the Sylow branch, n = 2 and the final
block assembly remain open. All fixed attachments and arbitrary original
field degree are retained; no minimum automorphism is extended to R.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), original MS3 in (2.1)(iii), p.855, and the full fixed-kernel comparison
in (3.7)(4), p.875. The minimum cut is the separate Section 7 construction,
pp.932--933. This is an original-radical comparison, not the full (3.7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

private def minimumInclusion : d.radical →* R :=
  { toFun := fun x => ⟨x,(map_subtype_le d.subgroup) x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

private def pullMinimum (J : Subgroup (FreeAmalgam d.radical)) : Subgroup R :=
  (J.comap (embedS d.radical)).map (minimumInclusion d)

omit [Finite H] in
private theorem pullMinimum_covariance (a : MulAut R)
    (J : Subgroup (FreeAmalgam d.radical)) (hJ : J ≤ (embedS d.radical).range) :
    pullMinimum d (J.map (MulAut.conj (minimumAutomorphismElement d a)).toMonoidHom) =
      (pullMinimum d J).map a.toMonoidHom := by
  have he : (MulAut.conj (minimumAutomorphismElement d a)).toMonoidHom.comp
      (embedS d.radical) = (embedS d.radical).comp (minimumAutomorphism d a).toMonoidHom :=
    MonoidHom.ext (minimumAutomorphismElement_conjugate d a)
  have hi : (minimumInclusion d).comp (minimumAutomorphism d a).toMonoidHom =
      a.toMonoidHom.comp (minimumInclusion d) := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    exact minimumAutomorphism_apply d a x
  have hm : (J.comap (embedS d.radical)).map (embedS d.radical) = J :=
    map_comap_eq_self hJ
  conv_lhs => rw [←hm]
  unfold pullMinimum
  rw [map_map,he,←map_map,comap_map_eq_self_of_injective (embedS_injective _),map_map,hi,←map_map]

omit [Finite H] in
private theorem pullMinimum_replacement (X : Subgroup d.overgroup) (hX : X ≤ d.radical) :
    pullMinimum d (X.map (embedM d.radical)) =
      (X.map d.overgroup.subtype).subgroupOf R := by
  have he : (X.map (embedM d.radical)).comap (embedS d.radical) = X.subgroupOf d.radical := by
    ext x
    change embedS d.radical x ∈ X.map (embedM d.radical) ↔ (x : d.overgroup) ∈ X
    rw [←DFunLike.congr_fun (embedM_comp_subtype d.radical) x]
    exact mem_map_iff_mem (embedM_injective d.radical)
  unfold pullMinimum
  rw [he]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,hx,rfl⟩
  · rintro ⟨x,hx,hxr⟩
    refine ⟨⟨x,hX hx⟩,hx,?_⟩
    exact Subtype.ext hxr

include h in
private theorem base_graph_images
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h)) :
    let S := stabilizer d.radical (alpha d.radical)
    let B := ((normalizer ((Q d.radical (beta d.radical)).subgroupOf S : Set S)).pCoreIn 2).map S.subtype
    (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map (embedM d.radical) =
      U d.radical (alpha d.radical) ∧
    (K.subgroupOf d.overgroup).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) ∧
    (R.subgroupOf d.overgroup).map (embedM d.radical) = B := by
  have hmU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map (embedM d.radical) =
      U d.radical (alpha d.radical) := by
    rw [←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl]
  have hmK : (K.subgroupOf d.overgroup).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [←replacement_residual h d,Ltilde_alpha]
  refine ⟨hmU,hmK,?_⟩
  let S := stabilizer d.radical (alpha d.radical)
  let f := embedM d.radical
  have hfr : f.range = S := (stabilizer_m_base d.radical).symm
  let fS := f.codRestrict S (fun x => hfr ▸ ⟨x,rfl⟩)
  have hfSi : Function.Injective fS := fun x y he =>
    embedM_injective d.radical (congrArg Subtype.val he)
  have hfSs : Function.Surjective fS := by
    intro x
    obtain ⟨y,hy⟩ := (show x.val ∈ f.range from hfr.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  let e := MulEquiv.ofBijective fS ⟨hfSi,hfSs⟩
  have heT : d.radical.map e.toMonoidHom = (Q d.radical (beta d.radical)).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_map,subgroupOf_map_subtype]
    change d.radical.map f = Q d.radical (beta d.radical) ⊓ S
    rw [←Q_beta]
    exact (inf_eq_left.mpr (fun _ hx => hx.2 _ (adjacent_symm _ (base_adjacent _)))).symm
  have heB : (R.subgroupOf d.overgroup).map e.toMonoidHom =
      (normalizer ((Q d.radical (beta d.radical)).subgroupOf S : Set S)).pCoreIn 2 := by
    rw [←replacement_normalizer_core_eq_original_restriction h d g hb hnsyl,
      map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective,map_equiv_normalizer_eq,heT]
  rw [←heB,Subgroup.map_map]
  rfl

include h in
private theorem pull_fixed_kernel
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    pullMinimum d (U d.radical (alpha d.radical) ⊓
      centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) =
      (((blockU K).map K.subtype ⊓ centralizer (K : Set H)).subgroupOf R) := by
  let := h.component_normal
  have hp : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hmU := d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hp
  have hU : ⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆ ≤ d.radical :=
    (commutator_le_left _ _).trans (replacement_core_le h d)
  have hgU : (⁅pCore 2 d.overgroup,K.subgroupOf d.overgroup⁆).map (embedM d.radical) =
      U d.radical (alpha d.radical) := by
    rw [←core_alpha d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_residual h d),
      replacement_core_eq_U_of_distance_two h d g hb rfl]
  have hgK : (K.subgroupOf d.overgroup).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [←replacement_residual h d,Ltilde_alpha]
  rw [←hgU,←hgK,map_inf_centralizer_of_injective _ (embedM_injective _),
    pullMinimum_replacement d _ (inf_le_left.trans hU),
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,hmU,
    map_subgroupOf_eq_of_le (show K ≤ d.overgroup from le_sup_left)]

include h in
private theorem pull_overlap
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let S := stabilizer d.radical (alpha d.radical)
    let B := ((normalizer ((Q d.radical (beta d.radical)).subgroupOf S : Set S)).pCoreIn 2).map S.subtype
    pullMinimum d ⁅U d.radical (alpha d.radical) ⊓
      centralizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)),B⁆ =
      ⁅minimumCenter d,d.overgroup.subgroupOf R⁆ := by
  obtain ⟨hU,hK,hB⟩ := base_graph_images h d g hb hnsyl
  dsimp only at hB ⊢
  rw [←hB,←hU,Q_beta,map_inf_centralizer_of_injective _ (embedM_injective _),←map_commutator]
  have hCnormal : R.subgroupOf d.overgroup ≤ normalizer
      ((d.radical ⊓ centralizer (d.radical : Set d.overgroup) : Subgroup d.overgroup) : Set d.overgroup) := by
    intro r hr
    have hn : r ∈ normalizer (d.radical : Set d.overgroup) := by
      rw [←replacement_normalizer_core_eq_original_restriction h d g hb hnsyl] at hr
      exact map_subtype_le _ hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj r).injective,
      mem_normalizer_iff_map_conj_eq.mp hn]
  have hcD : ⁅d.radical ⊓ centralizer (d.radical : Set d.overgroup),R.subgroupOf d.overgroup⁆ ≤ d.radical :=
    (le_normalizer_iff_commutator_le_left.mp hCnormal).trans inf_le_left
  rw [←replacement_field_sized_radical_center_displacement h d g hb
    (replacement_proper_nonsylow_card h d g hb hnsyl hne),pullMinimum_replacement d _ hcD]
  apply map_injective R.subtype_injective
  rw [map_subgroupOf_eq_of_le (show
    (⁅d.radical ⊓ centralizer (d.radical : Set d.overgroup),R.subgroupOf d.overgroup⁆).map
      d.overgroup.subtype ≤ R from (map_mono hcD).trans
        ((map_subgroupOf_eq_of_le le_sup_right).trans_le (map_subtype_le d.subgroup)))]
  rw [map_commutator,map_commutator]
  have hmC : (d.radical ⊓ centralizer (d.radical : Set d.overgroup)).map d.overgroup.subtype =
      (minimumCenter d).map R.subtype := by
    dsimp only [minimumCenter]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective,
      ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
      map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]
  rw [hmC,subgroupOf_map_subtype,subgroupOf_map_subtype,inf_comm]

include h in
/-- The full fixed-kernel comparison in the ORIGINAL radical, under the
same original automorphism that supplied the literal critical pair. -/
theorem original_critical_kernel_exchange_in_radical
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h))
    (a : MulAut R)
    (path : CriticalPath d.radical g (alpha d.radical)
      (act d.radical (minimumAutomorphismElement d a)⁻¹ (alpha d.radical))) :
    let A := (((blockU K).map K.subtype ⊓ centralizer (K : Set H)).subgroupOf R)
    let D := ⁅minimumCenter d,d.overgroup.subgroupOf R⁆
    A.map a.toMonoidHom = A ∨
      A.map a.toMonoidHom = D ∧ D.map a.toMonoidHom = A ∧ Disjoint A D ∧ Nat.card A = 2^n := by
  let Ag := U d.radical (alpha d.radical) ⊓
    centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))
  let S := stabilizer d.radical (alpha d.radical)
  let Bg := ((normalizer ((Q d.radical (beta d.radical)).subgroupOf S : Set S)).pCoreIn 2).map S.subtype
  let Dg := ⁅U d.radical (alpha d.radical) ⊓
    centralizer (Q d.radical (beta d.radical) : Set (FreeAmalgam d.radical)),Bg⁆
  let A := (((blockU K).map K.subtype ⊓ centralizer (K : Set H)).subgroupOf R)
  let D := ⁅minimumCenter d,d.overgroup.subgroupOf R⁆
  have hUQ : U d.radical (alpha d.radical) ≤ Q d.radical (beta d.radical) := by
    rw [←(base_graph_images h d g hb hnsyl).1,Q_beta]
    exact map_mono ((commutator_le_left _ _).trans (replacement_core_le h d))
  have hQrange : Q d.radical (beta d.radical) = (embedS d.radical).range := by
    rw [Q_beta,←embedM_comp_subtype,MonoidHom.range_comp,range_subtype]
  have hAr : Ag ≤ (embedS d.radical).range := inf_le_left.trans (hUQ.trans_eq hQrange)
  have hDr : Dg ≤ (embedS d.radical).range := by
    have hn : Bg ≤ normalizer (U d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
      (map_subtype_le _).trans (U_normalized _)
    exact (commutator_mono inf_le_left le_rfl).trans
      ((le_normalizer_iff_commutator_le_left.mp hn).trans (hUQ.trans_eq hQrange))
  have hA : pullMinimum d Ag = A := pull_fixed_kernel h d g hb
  have hD : pullMinimum d Dg = D := pull_overlap h d g hb hnsyl hne
  rcases original_critical_fixed_kernel_exchange h d g hb hnsyl hne a path with hp | ⟨ha,hd,hdis,hcard⟩
  · left
    have hh := congrArg (pullMinimum d) hp
    rwa [pullMinimum_covariance d a Ag hAr,hA] at hh
  · have ha' := congrArg (pullMinimum d) ha
    have hd' := congrArg (pullMinimum d) hd
    rw [pullMinimum_covariance d a Ag hAr,hA,hD] at ha'
    rw [pullMinimum_covariance d a Dg hDr,hA,hD] at hd'
    refine Or.inr ⟨ha',hd',?_,?_⟩
    · apply disjoint_iff_inf_le.mpr
      intro x hx
      apply R.subtype_injective
      have hDx : (x:H) ∈ ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆ := by
        have hh := mem_map_of_mem R.subtype hx.2
        dsimp only [D,minimumCenter] at hh
        rw [map_commutator,←map_inf_centralizer_of_injective _ R.subtype_injective,
          subgroupOf_map_subtype,inf_comm d.overgroup R] at hh
        exact hh
      exact disjoint_iff_inf_le.mp
        (original_proper_nonsylow_center_overlap h d g hb hnsyl hne).1 ⟨hDx,hx.1⟩
    · have hc : Nat.card D = 2^n := by
        have he := (original_proper_nonsylow_center_overlap h d g hb hnsyl hne).2.1
        have hm : D.map R.subtype =
            ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆ := by
          dsimp only [D,minimumCenter]
          rw [map_commutator,←map_inf_centralizer_of_injective _ R.subtype_injective,
            subgroupOf_map_subtype,inf_comm d.overgroup R]
        rw [←hm,card_map_of_injective R.subtype_injective] at he
        exact he
      change Nat.card A = 2^n
      rw [←hd',card_map_of_injective a.injective,hc]

omit [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem displacement_map_of_action_invariant (C B : Subgroup R) [C.Characteristic]
    (a : MulAut R)
    (he : (B.map (MulAut.conjNormal (H := C))).map
      (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom =
        B.map (MulAut.conjNormal (H := C))) :
    (⁅C,B⁆).map a.toMonoidHom = ⁅C,B⁆ := by
  let θ := MulAut.conjNormal (H := C)
  have hc : θ.comp a.toMonoidHom =
      (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom.comp θ := by
    apply MonoidHom.ext
    intro b
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change a b * (c:R) * (a b)⁻¹ = a (b * a.symm (c:R) * b⁻¹)
    rw [map_mul,map_mul,map_inv,a.apply_symm_apply]
  have him : (B.map a.toMonoidHom).map θ = B.map θ := by
    rw [map_map,hc,←map_map]
    exact he
  rw [map_commutator,characteristic_iff_map_eq.mp inferInstance a]
  exact le_antisymm (commutator_le_of_conjNormal_image_le C _ _ him.le)
    (commutator_le_of_conjNormal_image_le C _ _ him.ge)

include h in
/-- The actual source star and an original critical automorphism share the
same fixed-kernel and action-factor comparison. Exchange forces the entire
order-q-squared intersection action into the retained fixed-core action,
so that the full star action has order at least q to the fourth power. -/
theorem exists_source_star_critical_exchange_control
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R, ∃ a : MulAut R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map (componentProjection h) =
        (R.subgroupOf K).map (componentProjection h) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M) ∧
      (let z := act d.radical (minimumAutomorphismElement d a)⁻¹ (alpha d.radical)
       Adjacent d.radical z (beta d.radical) ∧
       ¬ U d.radical z ≤ Q d.radical (alpha d.radical) ∧
       Nonempty (CriticalPath d.radical g (alpha d.radical) z)) ∧
      (let T := starCentralizer R Y
       let B := d.overgroup.subgroupOf R
       let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
       let C := minimumCenter d
       let θ := minimumCenterAction d
       let A := (((blockU K).map K.subtype ⊓ centralizer (K : Set H)).subgroupOf R)
       let D := ⁅C,B⁆
       A.map a.toMonoidHom = A ∨
         A.map a.toMonoidHom = D ∧ D.map a.toMonoidHom = A ∧
         Disjoint A D ∧ Nat.card A = 2^n ∧ A ≤ ⁅C,Q₀⁆ ∧
         (B.map θ).map (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom ≤ Q₀.map θ ∧
         2^(2*n) ≤ Nat.card (Q₀.map θ) ∧ 2^(4*n) ≤ Nat.card (T.map θ)) := by
  obtain ⟨P,Y,hY,hn,hmin,hmark,hsat,hproduct,hsmall,hfactor,hdisplacement⟩ :=
    exists_source_star_automorphism_factor_dichotomy h d g hb hnsyl hne
  obtain ⟨a,haz,hmove,⟨path⟩⟩ := exists_original_critical_neighbor h d g hb
  refine ⟨P,Y,a,hY,hn,hmin,hmark,hsat,⟨haz,hmove,⟨path⟩⟩,?_⟩
  let T := starCentralizer R Y
  let B := d.overgroup.subgroupOf R
  let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
  let C := minimumCenter d
  let θ := minimumCenterAction d
  let A := (((blockU K).map K.subtype ⊓ centralizer (K : Set H)).subgroupOf R)
  let D := ⁅C,B⁆
  change A.map a.toMonoidHom = A ∨ _
  rcases original_critical_kernel_exchange_in_radical h d g hb hnsyl hne a path with
    hpres | ⟨ha,hd,hdis,hcard⟩
  · exact Or.inl hpres
  change A.map a.toMonoidHom = D at ha
  change D.map a.toMonoidHom = A at hd
  change Disjoint A D at hdis
  change Nat.card A = 2^n at hcard
  have hAD : A ≠ D := by
    intro he
    have hzero : A = ⊥ := by
      apply bot_unique
      intro x hx
      exact disjoint_iff_inf_le.mp hdis ⟨hx,he ▸ hx⟩
    have hh := hcard
    rw [hzero,card_bot] at hh
    have hlo : 1 < 2^n := Nat.one_lt_two_pow_iff.mpr (by have := h.nonbinary; omega)
    omega
  have hDmove : D.map a.toMonoidHom ≠ D := fun he => hAD (hd.symm.trans he)
  have hAE : A ≤ ⁅C,Q₀⁆ := by
    rcases hdisplacement a with hp | ⟨hle,_⟩
    · exact False.elim (hDmove hp)
    · exact hd.symm.trans_le hle
  have hfactor' : (B.map θ).map
      (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom ≤ Q₀.map θ := by
    rcases hfactor a with hp | hq
    · exact False.elim (hDmove (displacement_map_of_action_invariant C B a hp))
    · exact hq
  have hQcard : 2^(2*n) ≤ Nat.card (Q₀.map θ) := by
    have hh := Nat.card_le_card_of_injective (inclusion hfactor') (inclusion_injective _)
    rw [card_map_of_injective (MulAut.conj ((MulAut.characteristic C) a)).injective,
      original_minimum_center_action_card h d g hb hnsyl hne] at hh
    exact hh
  obtain ⟨original,hpos,_⟩ := h.positive_even_geometry
  have hrest := (star_radical_saturated_of_marked_image_eq h original hpos P Y hY hn hmark).1
  have horder := (star_center_action_direct_factors h d g hb P Y hY hmin hrest hnsyl hne).2.2.2
  have hlarge : 2^(4*n) ≤ Nat.card (T.map θ) := by
    rw [horder,show 4*n = 2*n+2*n by omega,pow_add]
    exact Nat.mul_le_mul_left _ hQcard
  exact Or.inr ⟨ha,hd,hdis,hcard,hAE,hfactor',hQcard,hlarge⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
