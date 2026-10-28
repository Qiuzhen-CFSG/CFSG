module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.BlockGeometry
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SylowSquares
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.SecondBlock.IntrinsicNatural

/-!
# Both natural blocks in the original moving pair

A centerless natural block with full two-core has central involutory
Sylow commutators over every even field. Its commuting residual pair
therefore gives this bound on the actual common Baumann subgroup.
The other component's literal local-class embedding then forces its
block status. Applying this in both orientations removes the block
alternative while preserving the same selected component, Hall
intersection, and both original quotient markings.

The original Hall intersection generates a full comparison Sylow by
commutators. The terminal application consequently requires no blockhood
premise. Overcomponent geometry, natural-row selection and original Hall
placement remain with the assembly owner `qt-d-10-nona5-moving-hall-three`.
Source: Aschbacher–Smith 10.2.3(4), printed p.747.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC
open ChapterB.QuasisimpleSource ChapterC.GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]

private theorem paired_baumann_commutator
    (T : Sylow 2 G) (hfit : generalizedFitting G = pCore 2 G)
    (K : Subgroup G) (hb : IsBlock K) {n : ℕ} (hnat : IsL2EvenBlock K n)
    (hR : pResidual 2 G = K ∨
      ∃ t : G, t ∈ (T : Subgroup G) ∧
        pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hzK : center K = ⊥) (hcore : pCore 2 K = blockU K)
    (hS : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G)) (pResidual 2 G)) :
    commutator (baumann (T : Subgroup G)) ≤
      GlaubermanNiles.omegaCenter (baumann (T : Subgroup G)) := by
  let S := baumann (T : Subgroup G)
  let P := S ⊓ K
  have hKR : K ≤ pResidual 2 G := by
    rcases hR with he | ⟨_,_,he⟩
    · exact he.ge
    · exact he ▸ le_sup_left
  have hSP : Chapter1.IsSylowIn 2 P K :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hKR hb.subnormal.subgroupOf
  have hP := hnat.ambient_sylow_commutator_le_omegaCenterIn_of_center_eq_bot
    K P hcore hzK hSP
  have hcomm : ⁅S,S⁆ ≤ omegaCenterIn S := by
    rcases hR with he | ⟨t,ht,he⟩
    · have hSK : S ≤ K := he ▸ (Chapter1.isSylowIn_iff.mp hS).2.1
      simpa only [show P=S from inf_eq_left.mpr hSK] using hP
    · let f := (MulAut.conj t).toMonoidHom
      let J := K.map f
      by_cases hne : K=J
      · have hSK : S ≤ K := by
          have h := (Chapter1.isSylowIn_iff.mp hS).2.1
          change pResidual 2 G = K ⊔ J at he
          simpa only [he,←hne,sup_idem] using h
        simpa only [show P=S from inf_eq_left.mpr hSK] using hP
      have hc : K ≤ centralizer (J : Set G) := commutator_eq_bot_iff_le_centralizer.mp
        (blocks_commute (RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hfit) hb
          (hb.map_equiv (MulAut.conj t)) hne)
      have hSm : S.map f=S := mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
      have hPm : P.map f=S ⊓ J := by
        rw [show P=S ⊓ K from rfl,map_inf _ _ _ (MulAut.conj t).injective,hSm]
      have hJP : Chapter1.IsSylowIn 2 (S ⊓ J) J := by
        have h := Chapter1.Section02.IndexTwo.isSylowIn_map hSP f
        rwa [hPm] at h
      have hJ : ⁅S ⊓ J,S ⊓ J⁆ ≤ omegaCenterIn (S ⊓ J) := by
        have h := map_mono (f := f) hP
        change (⁅P,P⁆).map f ≤ (omegaOneCenterAmbient P).map f at h
        rw [map_commutator,←omegaOneCenterAmbient_map_injective f (MulAut.conj t).injective,hPm] at h
        exact h
      have hsplit : S=P ⊔ (S ⊓ J) := eq_sup_sylow_intersections_of_commuting S K J
        (Chapter1.isSylowIn_iff.mp hS).1 (he ▸ (Chapter1.isSylowIn_iff.mp hS).2.1) hc hSP hJP
      have hh := commutator_le_omegaCenterIn_join_of_commuting P (S ⊓ J)
        (inf_le_right.trans (hc.trans (centralizer_le inf_le_right))) hP hJ
      rwa [←hsplit] at hh
  intro x hx
  have hm' : (commutator S).map S.subtype=⁅S,S⁆ := by
    rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨_,hxc,hx2⟩ := (mem_omegaCenterIn_iff S (x:G)).mp
    (hcomm (hm' ▸ mem_map_of_mem S.subtype hx))
  exact (GlaubermanNiles.mem_omegaCenter_iff x).mpr
    ⟨Subtype.ext hx2,fun y => Subtype.ext (hxc y y.property)⟩

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]
include D
private theorem original_block_commutes_conjugate
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    L ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let X := localJoin T L
  let A := L.subgroupOf X
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  let tX : X := ⟨t,(show (T : Subgroup G) ≤ X from le_sup_right) ht⟩
  let B := A.map (MulAut.conj tX).toMonoidHom
  have hbB : IsBlock B := hb.map_equiv (MulAut.conj tX)
  have hmapA : A.map X.subtype=L := map_subgroupOf_eq_of_le hLX
  have hmapB : B.map X.subtype=L.map (MulAut.conj t).toMonoidHom := by
    rw [show B = A.map (MulAut.conj tX).toMonoidHom from rfl,map_map]
    rw [show X.subtype.comp (MulAut.conj tX).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp X.subtype from rfl,←map_map,hmapA]
  have hne : A ≠ B := by
    intro he
    apply htn
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hmapB.symm.trans ((congrArg (map X.subtype) he).symm.trans hmapA)
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := by
    let := D.quasisimple
    exact IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _
      (subgroupOfEquivOfLe hLX).symm (pCore_map_iso 2 (subgroupOfEquivOfLe hLX).symm))
  have hc := congrArg (map X.subtype) (hb.commutator_eq_bot_of_quasisimple_quotient hbB hqA hne)
  rw [map_commutator,hmapA,hmapB,Subgroup.map_bot] at hc
  exact commutator_eq_bot_iff_le_centralizer.mp hc

/-- The original block controls the common Baumann commutators without a cubic actor. -/
theorem Context.original_block_common_commutator
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L))) :
    commutator (baumann (T : Subgroup G)) ≤
      GlaubermanNiles.omegaCenter (baumann (T : Subgroup G)) := by
  let S := baumann (T : Subgroup G)
  let P := S ⊓ L
  have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
  obtain ⟨hL,hcL,hzL⟩ := ctx.original_natural_block_core D n hn hF e mark hBR hb
  have hSO := ctx.original_block_baumann_le_orbit D n hn hF e mark hBR hb
  have hS := ctx.original_baumann_sylow D n hn hF e
  let X := localOrbit T L ⊔ S
  have hLX : L ≤ X := (le_componentOrbit L T).trans le_sup_left
  have hXM : X ≤ D.maximalLocal := sup_le (localOrbit T L).le_normalizer
    (inf_le_left.trans (le_normalizer_componentOrbit L T))
  have hSP : Chapter1.IsSylowIn 2 P L :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal hS hLX
      (D.component_in_maximalLocal.subgroupOf_of_le hLX hXM).subnormal
  have hP := hL.ambient_sylow_commutator_le_omegaCenterIn_of_center_eq_bot
    L P hcL hzL hSP
  obtain ⟨t,ht,htn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 ctx.nonnormal
  let f := (MulAut.conj t).toMonoidHom
  let K := L.map f
  have hc : L ≤ centralizer (K : Set G) := original_block_commutes_conjugate D hb ht htn
  have hSm : S.map f=S := mem_normalizer_iff_map_conj_eq.mp
    (normalizer_le_normalizer_baumann _ ((T : Subgroup G).le_normalizer ht))
  have hPm : P.map f=S ⊓ K := by
    rw [show P = S ⊓ L from rfl,map_inf _ _ _ (MulAut.conj t).injective,hSm]
  have hKP : Chapter1.IsSylowIn 2 (S ⊓ K) K := by
    have hh := Chapter1.Section02.IndexTwo.isSylowIn_map hSP f
    rwa [hPm] at hh
  have hK : ⁅S ⊓ K,S ⊓ K⁆ ≤ omegaCenterIn (S ⊓ K) := by
    have hh := map_mono (f := f) hP
    change (⁅P,P⁆).map f ≤ (omegaOneCenterAmbient P).map f at hh
    rw [map_commutator,←omegaOneCenterAmbient_map_injective f (MulAut.conj t).injective,hPm] at hh
    exact hh
  have hsplit : S=P ⊔ (S ⊓ K) := eq_sup_sylow_intersections_of_commuting S L K
    (Chapter1.isSylowIn_iff.mp hS).1 (hSO.trans hpair.le) hc hSP hKP
  have hPP : P ≤ centralizer (S ⊓ K : Set G) :=
    inf_le_right.trans (hc.trans (centralizer_le inf_le_right))
  have hcomm : ⁅S,S⁆ ≤ omegaCenterIn S := by
    have hh := commutator_le_omegaCenterIn_join_of_commuting P (S ⊓ K) hPP hP hK
    rwa [←hsplit] at hh
  intro x hx
  have hm : (commutator S).map S.subtype=⁅S,S⁆ := by
    rw [_root_.commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype]
  obtain ⟨_,hxc,hx2⟩ := (mem_omegaCenterIn_iff S (x:G)).mp (hcomm (hm ▸ mem_map_of_mem S.subtype hx))
  exact (GlaubermanNiles.mem_omegaCenter_iff x).mpr
    ⟨Subtype.ext hx2,fun y => Subtype.ext (hxc y y.property)⟩

/-- The comparison block gives the same bound on the original ambient Baumann group. -/
theorem Context.comparison_block_common_commutator
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBR : B.map H.subtype ≤ localOrbit T L)
    (K : Subgroup H) (hb : IsBlock K) (hnat : IsL2EvenBlock K n)
    (hR : pResidual 2 H = K ∨ ∃ t : H,
      t ∈ (T.subtype ctx.hstar.1.1.2 : Subgroup H) ∧
        pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    commutator (baumann (T : Subgroup G)) ≤
      GlaubermanNiles.omegaCenter (baumann (T : Subgroup G)) := by
  let S := T.subtype ctx.hstar.1.1.2
  let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
  let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H
  have hR' : pResidual 2 H = K ∨ ∃ t : H,
      pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom := by
    rcases hR with h | ⟨t,_,h⟩
    · exact Or.inl h
    · exact Or.inr ⟨t,h⟩
  obtain ⟨hzK,hcore,_⟩ := ctx.comparison_block_core_and_sylow D n hn hF e mark hBR K hb hR'
  have hm := (ctx.comparison_block_full_core_moved D n hn hF e mark hBR K hb hR').2
  have hCZ := ctx.seed_centralizer_eq_sylow D n hn hF e mark hBR
  have hkr : centralizer (U : Set H) ≤ pResidual 2 H := by
    rw [source_hstar_action_kernel_eq_core_of_seed_centralizer D ctx.hstar hCZ,hm]
    exact Subgroup.commutator_le_right (H₁ := pCore 2 H) (H₂ := pResidual 2 H)
  have hs : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact (not_lt_of_ge (ChapterE.generationParameter_le_one_of_solvable (G := H))) ctx.large
  have hS := source_baumann_sylow_in_residual_of_seed_centralizer
    (Chapter3.sqtk_of_mem_H D.simpleQTKE ctx.hstar.1.1.1) S
    (source_hstar_minimal_parabolic_of_generation_gt_one D ctx.hstar ctx.large) U
    (source_hstar_omega_orbit_reduced D ctx.hstar) hs
    (ctx.hstar_thompson_moves_omega_orbit D n hn hF e)
    Z (subgroupOf_mono H (le_conjugateSpanBy _ _)) hCZ hkr
  have hc := paired_baumann_commutator S (source_hstar_fitting_eq_core D ctx.hstar)
    K hb hnat hR hzK hcore hS
  have hBm : (baumann (S : Subgroup H)).map H.subtype=baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype=
      baumann ((S : Subgroup H).map H.subtype) at hh
    have hSm : (S : Subgroup H).map H.subtype=(T : Subgroup G) :=
      map_subgroupOf_eq_of_le ctx.hstar.1.1.2
    rwa [hSm] at hh
  let b := ((baumann (S : Subgroup H)).equivMapOfInjective H.subtype
    H.subtype_injective).trans (MulEquiv.subgroupCongr hBm)
  have hh := map_mono (f := b.toMonoidHom) hc
  rwa [_root_.map_commutator_eq,MonoidHom.range_eq_top.mpr b.surjective,
    ← _root_.commutator_def,GlaubermanNiles.omegaCenter_map_equiv] at hh

/-- Recover both original blocks from either orientation, over the same general field. -/
theorem Context.both_blocks_of_aligned_alternative
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hBK : baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ normalizer (K : Set H))
    (hlocal : GlaubermanNiles.InLocalClass (inclusion
      (show baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤
        K ⊔ baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) from le_sup_right)))
    (hR : pResidual 2 H = K ∨ ∃ t : H,
      t ∈ (T.subtype ctx.hstar.1.1.2 : Subgroup H) ∧
        pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hfirst : IsBlock (L.subgroupOf (localJoin T L)) ∨
      (IsBlock K ∧ IsL2EvenBlock K n)) :
    IsBlock (L.subgroupOf (localJoin T L)) ∧ IsBlock K ∧ ∃ m, IsL2EvenBlock K m := by
  rcases hfirst with hbL | ⟨hbK,hnat⟩
  · have hc := ctx.original_block_common_commutator D n hn hF e mark hBB hbL
    exact ⟨hbL,source_intrinsic_component_natural_of_common_baumann_commutator
      T H ctx.hstar.1.1.2 K hK hBK hlocal hc⟩
  · have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
    have hc := ctx.comparison_block_common_commutator D n hn hF e mark hBR K hbK hnat hR
    let X := localJoin T L
    let A := L.subgroupOf X
    have hA : A.IsCComponent := by
      change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
      rw [componentOrbit_sup]
      exact D.maximal.1.1
    have hsource := ctx.original_common_baumann_embedding D n hn hF e
    exact ⟨(source_intrinsic_component_natural_of_common_baumann_commutator
      T X le_sup_right A hA hsource.2.1 hsource.2.2.1 hc).1,hbK,⟨n,hnat⟩⟩

/-- The selected original Hall intersection gives the literal comparison Sylow. -/
theorem Context.comparison_block_axis_sylow
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (hb : IsBlock (L.subgroupOf (localJoin T L)))
    (K : Subgroup H) (hnat : IsL2EvenBlock K n)
    (hcore : pCore 2 K = blockU K)
    (hSK : Chapter1.IsSylowIn 2 (baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ⊓ K) K)
    (hBK : baumann (T.subtype ctx.hstar.1.1.2 : Subgroup H) ≤ normalizer (K : Set H))
    (hne : (B ⊓ K : Subgroup H) ≠ ⊥) :
    ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ =
      baumann (T : Subgroup G) ⊓ K.map H.subtype ∧
    Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆
      (K.map H.subtype) := by
  let S := T.subtype ctx.hstar.1.1.2
  have hBm : (baumann (S : Subgroup H)).map H.subtype=baumann (T : Subgroup G) := by
    have hh := baumann_map_injective H.subtype H.subtype_injective (S : Subgroup H)
    change (baumann (S : Subgroup H)).map H.subtype=
      baumann ((S : Subgroup H).map H.subtype) at hh
    have hSm : (S : Subgroup H).map H.subtype=(T : Subgroup G) :=
      map_subgroupOf_eq_of_le ctx.hstar.1.1.2
    rwa [hSm] at hh
  have hAS : B ⊓ K ≤ normalizer (baumann (S : Subgroup H) : Set H) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator,hBm]
    exact le_normalizer_iff_commutator_le_right.mp
      ((map_mono inf_le_left).trans (ctx.original_block_hall_normalizes_baumann D n hn hF e mark hBB hb))
  have hodd : Odd (Nat.card (B ⊓ K : Subgroup H)) := by
    rw [←card_map_of_injective H.subtype_injective]
    exact ctx.odd_card_of_le_hall_image _ (map_mono inf_le_left)
  obtain ⟨he,hP⟩ := hnat.ambient_odd_commutator_sylow K (baumann (S : Subgroup H))
    (B ⊓ K) hcore hSK inf_le_right hodd hne hAS hBK
  have he' := congrArg (map H.subtype) he
  rw [map_commutator,map_inf _ _ _ H.subtype_injective,hBm] at he'
  rw [map_inf _ _ _ H.subtype_injective,hBm] at he'
  have hP' := Chapter1.Section02.IndexTwo.isSylowIn_map hP H.subtype
  rw [map_commutator,hBm] at hP'
  exact ⟨by simpa only [map_inf _ _ _ H.subtype_injective] using he',hP'⟩

/-- Both natural blocks, their full cores, and the original axis geometry
hold simultaneously for the same selected component and Hall intersection. -/
theorem Context.component_with_both_block_geometry
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L) :
    let S := T.subtype ctx.hstar.1.1.2
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    let B₀ := baumann (S : Subgroup H)
    ∃ (E : BinaryField) (K : Subgroup H),
      Nat.card E.Carrier = Nat.card F ∧ K.IsCComponent ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,E.Carrier)) ∧
      U ≤ normalizer (K : Set H) ∧ B₀ ≤ normalizer (K : Set H) ∧
      InLocalClass (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right)) ∧
      (localV (inclusion (show B₀ ≤ K ⊔ B₀ from le_sup_right))).map (K ⊔ B₀).subtype =
        (⁅U,K⁆ : Subgroup H) ⊔ (thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H)) ∧
      thompsonAlpha (S : Subgroup H) ⊓ centralizer (K : Set H) ≠ ⊥ ∧
      K ⊔ (S : Subgroup H) = ⊤ ∧
      (∃ t ∈ (S : Subgroup H), pResidual 2 H = K ⊔ K.map (MulAut.conj t).toMonoidHom) ∧
      Nat.card (B ⊓ K : Subgroup H) = Nat.card F - 1 ∧ IsCyclic (B ⊓ K : Subgroup H) ∧
      B ≤ normalizer (K : Set H) ∧
      (∀ t : H, B ≤ normalizer (K.map (MulAut.conj t).toMonoidHom : Set H)) ∧
      ChapterC.IsBlock (L.subgroupOf (localJoin T L)) ∧
      ChapterC.IsL2EvenBlock L n ∧ pCore 2 L = ChapterC.blockU L ∧ center L = ⊥ ∧
      (∀ A : Subgroup G, A ≤ L → A ≤ B.map H.subtype → A ≠ ⊥ →
        ⁅baumann (T : Subgroup G),A⁆ = baumann (T : Subgroup G) ⊓ L ∧
        Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),A⁆ L ∧
        A ⊓ centralizer ((⁅baumann (T : Subgroup G),A⁆ : Subgroup G) : Set G) = ⊥ ∧
        IsSQTK KnownSimple.IsKnownSimple
          (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G))) ∧
      ChapterC.IsBlock K ∧ ChapterC.IsL2EvenBlock K n ∧
      pCore 2 K = ChapterC.blockU K ∧ center K = ⊥ ∧
      Chapter1.IsSylowIn 2 (B₀ ⊓ K) K ∧
      ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ =
        baumann (T : Subgroup G) ⊓ K.map H.subtype ∧
      Chapter1.IsSylowIn 2 ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆
        (K.map H.subtype) ∧
    ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
      ∃ a : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)),
        (∀ l : L, a (QuotientGroup.mk' _ ⟨l,le_componentOrbit L T l.property⟩) =
          (e (QuotientGroup.mk' _ l),1)) ∧
        (∀ l : L, a (QuotientGroup.mk' _ (originalConjugateOrbitInclusion ht l)) =
          (1,e (QuotientGroup.mk' _ l))) ∧
    let C := B.map H.subtype
    let hCR : C ≤ localOrbit T L := hBB.trans ((map_subtype_le _).trans inf_le_left)
    let f := (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))).comp (inclusion hCR)
    let A₁ := ((MonoidHom.snd _ _).comp f).ker.map C.subtype
    let A₂ := ((MonoidHom.fst _ _).comp f).ker.map C.subtype
    ((B ⊓ K).map H.subtype = A₁ ∨ (B ⊓ K).map H.subtype = A₂) ∧
      A₁ ≤ L ∧ A₂ ≤ L.map (MulAut.conj t).toMonoidHom ∧
      Nat.card A₁ = Nat.card F - 1 ∧ Nat.card A₂ = Nat.card F - 1 ∧
      Disjoint A₁ A₂ ∧ A₁ ⊔ A₂ = C ∧ IsCyclic A₁ ∧ IsCyclic A₂ ∧
      (⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ ≤ K.map H.subtype ⊓ L ∨
        ⁅baumann (T : Subgroup G),(B ⊓ K).map H.subtype⁆ ≤
          K.map H.subtype ⊓ L.map (MulAut.conj t).toMonoidHom) := by
  obtain ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hblock,t,ht,htn,a,hfirst,hsecond,haxes⟩ :=
    ctx.component_with_block_core_geometry D n hn hF e mark hBB
  have hBR := hBB.trans ((map_subtype_le _).trans inf_le_left)
  have halt : IsBlock (L.subgroupOf (localJoin T L)) ∨
      (IsBlock K ∧ IsL2EvenBlock K n) := by
    rcases hblock with hL | hK
    · exact Or.inl hL.1
    · exact Or.inr ⟨hK.1,hK.2.1⟩
  have hR : pResidual 2 H = K ∨ ∃ s : H,
      s ∈ (T.subtype ctx.hstar.1.1.2 : Subgroup H) ∧
        pResidual 2 H = K ⊔ K.map (MulAut.conj s).toMonoidHom := Or.inr hcover
  obtain ⟨hbL,hbK,hnatK⟩ := ctx.both_blocks_of_aligned_alternative
    D n hn hF e mark hBB K hK hBK hlocal hR halt
  obtain ⟨hnatL,hcoreL,hzL⟩ := ctx.original_natural_block_core D n hn hF e mark hBR hbL
  have hR' : pResidual 2 H = K ∨ ∃ s : H,
      pResidual 2 H = K ⊔ K.map (MulAut.conj s).toMonoidHom := by
    obtain ⟨s,_,hs⟩ := hcover
    exact Or.inr ⟨s,hs⟩
  obtain ⟨hnatK,hcoreK,hzK,hSK⟩ := ctx.comparison_natural_block_core
    D n hn hF e mark hBR K hbK hnatK hE heq.some hR'
  have hne : (B ⊓ K : Subgroup H) ≠ ⊥ := by
    intro he
    rw [he,card_bot,hF] at hcard
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  obtain ⟨haxis,haxisS⟩ := ctx.comparison_block_axis_sylow D n hn hF e mark hBB
    hbL K hnatK hcoreK hSK hBK hne
  exact ⟨E,K,hE,hK,heq,hUK,hBK,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,hnatL,hcoreL,hzL,
    (fun A hAL hAB hne => ctx.original_block_axis_borel D n hn hF e mark hBB hbL A hAL hAB hne),
    hbK,hnatK,hcoreK,hzK,hSK,haxis,haxisS,t,ht,htn,a,hfirst,hsecond,haxes⟩

/-- The source terminal constructor no longer assumes either blockhood.
The moving-Hall assembly owner retains the displayed overcomponent geometry,
natural marking, and original Hall placement. -/
theorem Context.terminal_of_overcomponent
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (A K : Subgroup G) (hAL : A ≤ L) (hAB : A ≤ B.map H.subtype)
    (hA : Nat.card A = 2 ^ n - 1)
    (hK : K ∈ Chapter1.cComponentsIn
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)))
    (hmodel : Chapter1.Section02.LocalModels.IsSL K 3 (2 ^ n) ∨ ClassicalGroup.IsPSL K 3 (2 ^ n))
    (hcentral : K ≤ centralizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)) :
    Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  obtain ⟨E,J,hE,hJ,heq,hUJ,hBJ,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,_⟩ := ctx.component_with_both_block_geometry D n hn hF e mark hBB
  exact ctx.terminal_of_original_block_overcomponent D n hn hF e mark hBB hbL
    A K hAL hAB hA hK hmodel hcentral

end CFSG.Quasithin.Chapter10.MovingHall
