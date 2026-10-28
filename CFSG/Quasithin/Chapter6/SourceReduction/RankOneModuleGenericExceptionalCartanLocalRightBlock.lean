module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightNatural
public import Theory.GroupTheory.ReducedNormal.SylowCentralSeed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftBlock

/-!
# Both original local Cartan block alternatives

The natural action of the literal right residual makes the four-space
irreducible. Its nonzero omega seed therefore spans the whole space inside
H, so the original right omega-span is reduced there. Restricting the
actual A₇ quotient and its coordinates supplies the right Baumann local
class, including the full residual commutator and exact action kernel.

Apply one uniform characteristic pair to LT and H. Omega fixed-space
vanishing eliminates the first characteristic alternative on each side.
If neither side were a block, the same nontrivial second member would be
normalized by both, contrary to the original local uniqueness theorem.
The final application constructs the configuration through the completed
FF reduction under the original universal Input and both Hall conditions.

This proves the block dichotomy on p.637. Both block exclusions, the torus
contradiction and the original source assembly remain necessary.
Source: Aschbacher–Smith 5.1.13 and C.1.28, printed pp.637–638,134.
-/

public noncomputable section
universe u
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

/-- Irreducibility on actual ambient subgroups, under the literal residual. -/
theorem LocalA7Configuration.four_residual_irreducible
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (E : Subgroup G) (hEU : E ≤ localOmegaModule T K)
    (hRE : residual H ≤ normalizer (E : Set G)) :
    E = ⊥ ∨ E = localOmegaModule T K := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let R := (residual H).subgroupOf M
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  obtain ⟨q,hq,hk,_,_,e,f,hf⟩ := a.four_residual_natural h hH hgen c d
  let ρ := NormalElementaryQuotient.representation U q hq hk
  let σ : Representation (ZMod 2) (R.map q) (Additive U) := ρ.comp (R.map q).subtype
  let F : ChapterB.QuasisimpleSource.BinaryField := {
    Carrier := SL2FourNatural.F
    degree := 2
    degree_pos := by decide
    card_eq := by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]; decide }
  have hi : σ.IsIrreducible := ChapterB.QuasisimpleSource.ExtensionConsequences.irreducible_of_equiv
    ({groupEquiv := e,linearEquiv := f,intertwines := hf} :
      ChapterB.QuasisimpleSource.ActionEquiv σ (ChapterB.QuasisimpleSource.linearNatural F 2))
    (ChapterB.QuasisimpleSource.ExtensionConsequences.linearNatural_irreducible F (by decide : 2 ≤ 2))
  let N : Subrepresentation σ := {
    toSubmodule := NormalElementaryQuotient.subspace U ((E.subgroupOf M).subgroupOf U)
    apply_mem_toSubmodule := by
      intro r v hv
      change ((ρ r.val v).toMul : M).val ∈ E
      obtain ⟨x,hx,hxr⟩ := r.property
      rw [←hxr,NormalElementaryQuotient.representation_apply]
      exact le_normalizer_iff.mp hRE x.val hx v.toMul.val.val hv }
  rcases hi.eq_bot_or_eq_top N with hb | ht
  · left
    apply bot_unique
    intro x hx
    let u : U := ⟨⟨x,a.reduced.1 (hEU hx)⟩,hEU hx⟩
    have hu : Additive.ofMul u ∈ N := hx
    rw [hb] at hu
    exact congrArg (fun v : Additive U => v.toMul.val.val) hu
  · right
    apply le_antisymm hEU
    intro x hx
    let u : U := ⟨⟨x,a.reduced.1 hx⟩,hx⟩
    have hu : Additive.ofMul u ∈ N := by rw [ht]; trivial
    exact hu

/-- The original right omega-span is exactly the complete four-space,
and is reduced inside the original H, with its literal residual commutator. -/
theorem LocalA7Configuration.right_omega_span_reduced
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H = localOmegaModule T K ∧
      IsPReduced 2 ((localOmegaModule T K).subgroupOf H) ∧
      ⁅(localOmegaModule T K).subgroupOf H,pResidual 2 H⁆ =
        (localOmegaModule T K).subgroupOf H := by
  let V := localOmegaModule T K
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hHM : H ≤ K ⊔ (T : Subgroup G) := by
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le ((d.residual_le.trans a.contains).trans le_sup_left) le_sup_right
  have hHV : H ≤ normalizer (V : Set G) := hHM.trans (reduced_normalizes a.reduced)
  have hZV := (a.omega_four_geometry h hH hgen c d).1
  have hs : conjugateSpanBy Z H = V := by
    have hVU := conjugateSpanBy_le hZV hHV
    rcases a.four_residual_irreducible h hH hgen c d _ hVU
        ((show residual H ≤ H from map_subtype_le _).trans
          (le_normalizer_conjugateSpanBy Z H)) with hz | he
    · have hzero : Z = ⊥ := bot_unique ((le_conjugateSpanBy Z H).trans_eq hz)
      have hc := (a.omega_four_geometry h hH hgen c d).2.1
      change Nat.card Z = 2 at hc
      rw [hzero,card_bot] at hc
      contradiction
    · exact he
  have hVH : V ≤ H := hs ▸ conjugateSpanBy_le_self
    ((show Z ≤ (T : Subgroup G) from fun z hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans hH.1.1.2)
  let : IsElementaryAbelian 2 V := a.reduced.2.1
  have hv : IsPReduced 2 (V.subgroupOf H) :=
    reduced_of_sylow_central_seed T H V Z hH.1.1.2 hVH hHV hZV
      (fun z hz t ht => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht) hs.symm
  refine ⟨hs,hv,?_⟩
  apply map_injective H.subtype_injective
  rw [map_commutator,map_subgroupOf_eq_of_le hVH]
  exact a.four_residual_full_movement h hH hgen c d


/-- The actual whole right omega-span supplies the second local-class
application to the same Baumann subgroup. -/
theorem LocalA7Configuration.right_baumann_localClass
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    let P := T.subtype hH.1.1.2
    ChapterC.GlaubermanNiles.InLocalClass (inclusion (show ChapterB.baumann (P : Subgroup H) ≤
      pResidual 2 H ⊔ ChapterB.baumann (P : Subgroup H) from le_sup_right)) := by
  let M := K ⊔ (T : Subgroup G)
  let V := localOmegaModule T K
  let U := V.subgroupOf H
  let U₀ := V.subgroupOf M
  let R₀ := (residual H).subgroupOf M
  let P := T.subtype hH.1.1.2
  obtain ⟨hspan,hr,hm⟩ := a.right_omega_span_reduced h hH hgen c d
  have hr₀ : IsPReduced 2 U₀ := LocalOmega.reduced_internal a.reduced
  let := hr₀.normal
  let := hr₀.elementary
  let := hr.normal
  let := hr.elementary
  have hVH : V ≤ H := by
    change localOmegaModule T K ≤ H
    rw [←hspan]
    exact conjugateSpanBy_le_self
      ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from fun z hz =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1).trans hH.1.1.2)
  have hHM : H ≤ M := by
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le ((d.residual_le.trans a.contains).trans le_sup_left) le_sup_right
  have hRM : residual H ≤ M := (show residual H ≤ H from map_subtype_le _).trans hHM
  obtain ⟨q₀,hq₀,hk₀,_,_,e₀,f₀,hf₀⟩ := a.four_residual_natural h hH hgen c d
  let t : H →* M := inclusion hHM
  let j := q₀.comp t
  let q := j.rangeRestrict
  have hq : Function.Surjective q := j.rangeRestrict_surjective
  have hk : q.ker = centralizer (U : Set H) := by
    ext x
    rw [MonoidHom.mem_ker,Subtype.ext_iff]
    change q₀ (t x) = 1 ↔ x ∈ centralizer (U : Set H)
    rw [←MonoidHom.mem_ker,hk₀]
    constructor
    · intro hx v hv
      exact Subtype.ext (congrArg M.subtype (hx ⟨v,hHM v.property⟩ hv))
    · intro hx v hv
      exact Subtype.ext (congrArg H.subtype (hx ⟨v,hVH hv⟩ hv))
  let E := (pResidual 2 H).map q
  let : E.Normal := Normal.map inferInstance q hq
  have htR : (pResidual 2 H).map t = R₀ := by
    apply map_injective M.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hRM]
    rfl
  have hE : E.map j.range.subtype = R₀.map q₀ := by
    rw [map_map]
    change (pResidual 2 H).map (q₀.comp t) = R₀.map q₀
    rw [←map_map,htR]
  let eE : E ≃* R₀.map q₀ :=
    (E.equivMapOfInjective j.range.subtype j.range.subtype_injective).trans
      (MulEquiv.subgroupCongr hE)
  let e := eE.trans e₀
  let eU : U ≃* U₀ := (subgroupOfEquivOfLe hVH).trans
    (subgroupOfEquivOfLe a.reduced.1).symm
  let b : (⁅U,pResidual 2 H⁆ : Subgroup H) ≃* U₀ := (MulEquiv.subgroupCongr hm).trans eU
  let f := f₀.toLinearMap.comp (b.toMonoidHom.toAdditive.toZModLinearMap 2)
  have hf : Function.Surjective f := f₀.surjective.comp b.surjective
  have he : ∀ (g : H) (hg : q g ∈ E) (v : Additive (⁅U,pResidual 2 H⁆ : Subgroup H)),
      f (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        SL2NaturalOffenders.NoStrong.natural (e ⟨q g,hg⟩) (f v) := by
    intro g hg v
    have hh := hf₀ (eE ⟨q g,hg⟩) (Additive.ofMul (b v.toMul))
    change f₀ (NormalElementaryQuotient.representation U₀ q₀ hq₀ hk₀ (q₀ (t g))
      (Additive.ofMul (b v.toMul))) = _ at hh
    change f₀ (Additive.ofMul (b (MulAut.conjNormal g v.toMul))) =
      specialLinearNatural 2 (e₀ (eE ⟨q g,hg⟩)) (f₀ (Additive.ofMul (b v.toMul)))
    rw [←hh]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [NormalElementaryQuotient.representation_apply]
    rfl
  have hfk : ∀ (v : Additive (⁅U,pResidual 2 H⁆ : Subgroup H)),
      f v = 0 ↔ (v.toMul : H) ∈ centralizer (pResidual 2 H : Set H) := by
    intro v
    constructor
    · intro hv
      have hv₀ : v = 0 := (f₀.injective.comp b.injective) (hv.trans (map_zero f).symm)
      rw [hv₀]
      exact one_mem _
    · intro hv
      have hvV : v.toMul.val.val ∈ V := (commutator_le_left U (pResidual 2 H)) v.toMul.property
      have hvC : v.toMul.val.val ∈ centralizer (residual H : Set G) := by
        rintro r ⟨r,hr,rfl⟩
        exact congrArg H.subtype (hv r hr)
      have hzero := (a.four_geometry h d (a.four h hH hgen c d)).1.le ⟨hvV,hvC⟩
      have hv₀ : v = 0 := by
        apply Additive.toMul.injective
        apply Subtype.ext
        apply Subtype.ext
        exact hzero
      rw [hv₀,map_zero]
  have hPm : (P : Subgroup H).map H.subtype = (T : Subgroup G) := map_subgroupOf_eq_of_le hH.1.1.2
  have hJ : ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (U : Set H) := by
    intro hj
    apply a.right_thompson_moves
    have hjm : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hPm]
    rw [←hjm]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg H.subtype (hj hx ⟨v,hVH hv⟩ hv)
  let N := normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H)
  have hZm : (omegaOneCenterAmbient (P : Subgroup H)).map H.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hPm]
  have hZN : omegaOneCenterAmbient (T : Subgroup G) ≤ N.map H.subtype := by
    rw [←hZm]
    exact map_mono le_normalClosure
  have hHN : H ≤ normalizer (N.map H.subtype : Set G) := by
    have hh := N.le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hseed : U ≤ N := by
    intro u hu
    have hu' : u.val ∈ localOmegaModule T K := hu
    rw [←hspan] at hu'
    have hh := (conjugateSpanBy_le hZN hHN) hu'
    exact (mem_map_iff_mem H.subtype_injective).mp hh
  have hfit : generalizedFitting H = pCore 2 H :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1))
  exact ChapterC.RankOne.ChiProduct.SelectedRankOne.normal_layer_seed_localClass
    P (hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen)
    U hr hJ q hq hk E e
    (by rw [Nat.card_eq_fintype_card,SL2FourNatural.card_field]; decide) f hf he hfk hseed hfit


open ChapterC.GlaubermanNiles

/-- The same uniform characteristic pair gives the right block or the
second member normalized by the original H. -/
theorem LocalA7Configuration.right_characteristic_or_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (P : CharacteristicPair (ChapterB.baumann (T : Subgroup G))) (hP : P.Universal.{u,u}) :
    H ≤ normalizer (P.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∨
      ChapterC.IsChiBlockIn (pResidual 2 H) := by
  let S := T.subtype hH.1.1.2
  let E := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair T P H hH.1.1.2
  have hE := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair_universal
    T P hP H hH.1.1.2
  let B₀ := ChapterB.baumann (S : Subgroup H)
  let N := pResidual 2 H ⊔ B₀
  have hlocal := a.right_baumann_localClass h hH hgen c d
  rcases hE N (inclusion (show B₀ ≤ N from le_sup_right)) hlocal with hc | hn | hb
  · exfalso
    apply ChapterC.RankOne.ChiProduct.FixedPair.firstSeed_ne_bot T P
    apply bot_unique
    intro z hz
    apply (a.omega_four_geometry h hH hgen c d).2.2.le
    refine ⟨hz.1,?_⟩
    have hm := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair_member_map
      T H hH.1.1.2 P.first
    obtain ⟨v,hv,hvz⟩ := hm.ge hz.2
    obtain ⟨b,hb,rfl⟩ := hv
    rintro _ ⟨r,hr,rfl⟩
    let rN : N := ⟨r,mem_sup_left hr⟩
    have hh := mem_center_iff.mp (hc (mem_map_of_mem
      (inclusion (show B₀ ≤ N from le_sup_right)) hb)) rN
    have hh' := congrArg (H.subtype.comp N.subtype) hh
    change (r : G) * (b.val : G) = (b.val : G) * r at hh'
    change (b.val : G) = z at hvz
    rwa [hvz] at hh'
  · left
    let C := P.second.map (ChapterB.baumann (T : Subgroup G)).subtype
    let C' := E.second.map (inclusion (show B₀ ≤ N from le_sup_right))
    let := hn
    have hm : C'.map (H.subtype.comp N.subtype) = C := by
      rw [map_map]
      have hh := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair_member_map
        T H hH.1.1.2 P.second
      rw [map_map] at hh
      exact hh
    have hN : N.map H.subtype ≤ normalizer (C : Set G) := by
      have hh := C'.le_normalizer_map (H.subtype.comp N.subtype)
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,MonoidHom.range_comp,
        range_subtype,hm] at hh
      exact hh
    have hR : residual H ≤ normalizer (C : Set G) := (map_mono le_sup_left).trans hN
    let := P.second_characteristic
    rw [←residual_sup_sylow T H hH.1.1.2]
    exact sup_le hR (((T : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_baumann (T : Subgroup G))).trans
        (normalizer_le_normalizer_characteristic_image _ P.second))
  · exact Or.inr (ChapterC.RankOne.ChiProduct.SelectedRankOne.chi_residual_of_selected_block S hb)

/-- C.1.28 for the two original groups: local uniqueness excludes the
common characteristic member, so one of the literal residuals is a block. -/
theorem LocalA7Configuration.left_or_right_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∨
      ChapterC.IsChiBlockIn (pResidual 2 H) := by
  by_cases hb : ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G)))
  · exact Or.inl hb
  have ht : (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hz : W = ⊥ := bot_unique (h.reduced_le_sylow.trans_eq he)
    exact h.noncentral (by rw [hz,commutator_bot_left])
  obtain ⟨P,hP⟩ := ChapterC.RankOne.ChiProduct.SelectedRankOne.exists_baumann_universal_pair.{u,u}
    (T : Subgroup G) T.isPGroup' ht
  rcases a.right_characteristic_or_block h hH hgen c d P hP with hn | hr
  · exact (a.residual_escapes_second_of_left_nonblock h hH hgen c d P hP hb
      ((show residual H ≤ H from map_subtype_le _).trans hn)).elim
  · exact Or.inr hr

/-- Apply the two block alternatives and local uniqueness under the original
universal Input, with the completed FF reduction as the configuration producer. -/
theorem localCartan_noncentral_block_alternative
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∨
      ChapterC.IsChiBlockIn (pResidual 2 H) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  exact a.left_or_right_block h hH hgen c d

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
