module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitExclusion
public import CFSG.Quasithin.ChapterG.Section11.LargeActorExchangedExclusion
public import Theory.Representation.SimplePairCoordinates
public import Theory.Representation.BinaryPermutation.PointStabilizerRank

/-!
# Exchanged natural constituents of the original large action

The natural S₈ constituent forces actor rank five. Its perfect normal image
is A₈. A central constituent kernel would embed the actor in Aut(A₈), whose
two-rank is four. For S₆, a central kernel instead embeds an actor of rank at
least three in Aut(A₆). Such an elementary subgroup lies in the natural S₆.
Its permutation action gives a literal intertwiner on the constituent,
contradicting homogeneous selection of the exchanged pair.

A noncentral kernel in either row makes the component Sylow two-subgroups
elementary, by the normal elementary actor and the two jointly faithful
exchanged actions. This passes to the actual quotient A₆ or A₈, contradicting
an explicit element of order four.

For S₅, a faithful constituent again contradicts homogeneous selection.
A nontrivial kernel identifies the whole component-orbit action with the
product of two natural A₅ actions. Each vector stabilizer contains a subgroup
of order three, contradicting the original point-centralizer three-rank bound.
Thus every low-rank source branch satisfies the printed G.11 catalogue.
The fixed-line branch and conversion to the marked 14.4.2 action catalogue
remain assembly obligations. The kernel argument extends the S₆/rank-four
calculation in ChapterG.Section11.LargeActorExchangedExclusion.

Source: Aschbacher--Smith G.10.15, G.11.6 and 14.4.2,
printed pp.361--366,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNatural
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition

private theorem alternating_eight_automorphism_two_rank :
    primeRank 2 (MulAut (alternatingGroup (Fin 8))) ≤ 4 := by
  let e : Equiv.Perm (Fin 8) ≃* MulAut (alternatingGroup (Fin 8)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      8 (by decide) (by decide))
  rw [← primeRank_equiv 2 e]
  let S := Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeSylow
  rw [S.primeRank_eq]
  change primeRank 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeGroup ≤ 4
  rw [primeRank_equiv 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeWreathEquiv]
  apply WreathTwoElementaryRank.rank_bound (r := 2) _ (by decide)
  apply primeRank_le_of_noncommutative_card_prime_pow (n := 2)
  · norm_num [DihedralGroup.nat_card,DihedralGroup.card]
  · exact DihedralGroup.not_commutative (by decide) (by decide)

variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem exchanged_conjugation_injective
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hi : IsIrreducible ρ)
    {L : Subgroup D} (hL : IsComponent D L)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤)
      X I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤) :
    letI := componentOrbit_top_normal L
    Function.Injective (MulAut.conjNormal.comp X.subtype :
      X →* MulAut (componentOrbit L ⊤)) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    hi H hL.componentOrbit_top_ne_bot
  let f : X →* MulAut H := MulAut.conjNormal.comp X.subtype
  apply (injective_iff_map_eq_one f).mpr
  intro z hz
  have hzi : (z : D)⁻¹ = z := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (z : D) z.property)
  have hzI : (z : D) ∈ subspaceStabilizer ρ I := by
    by_contra hn
    have hm : I.map (ρ (z : D)⁻¹) ≠ I := by
      rw [hzi]
      exact fun he => hn ((subspace_map_eq_iff ρ I _).mp he)
    have ho := hI.conjugation_not_inner ρ hfix z hm
    apply ho
    change f z ∈ MulAut.innerSubgroup H
    rw [hz]
    exact (MulAut.innerSubgroup H).one_mem
  have hzc : (z : D) ∈ centralizer (H : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact hz
  have he := h.spanning_constituent_stabilizer_centralizer_eq_bot hI.isIrrPlus hgen
  apply Subtype.ext
  apply mem_bot.mp
  rw [← he]
  exact ⟨⟨hzI,z.property⟩,hzc⟩

omit [Finite D] [FiniteDimensional (ZMod 2) U] [IsElementaryAbelian 2 X] in
private theorem natural_orbit_coordinates
    (H : Subgroup D) [H.Normal] [Group.IsPerfect H]
    (I : Submodule (ZMod 2) U) (hH : H ≤ subspaceStabilizer ρ I)
    (hne : I ≠ ⊥) (hfix : fixedSpace ρ H = ⊥)
    (n : ℕ) (hn : 5 ≤ n)
    (hm : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    ∃ p : H →* alternatingGroup (Fin n), Function.Surjective p ∧
      (∀ a : H, p a = 1 ↔ (invariantSubspace ρ H I hH).toRepresentation a = 1) ∧
      ∃ f : I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin n),
        ∀ a w, f ((invariantSubspace ρ H I hH).toRepresentation a w) =
          BinaryPermutation.naturalRepresentation (Fin n) (p a).val (f w) := by
  let Y := X ⊓ subspaceStabilizer ρ I
  let P := H ⊔ Y
  let σ := ChapterG.Section09.constituentAction ρ H Y I hH inf_le_right
  let q := QuotientGroup.mk' σ.ker
  let ι := Subgroup.inclusion (show H ≤ P from le_sup_left)
  let r := q.comp ι
  have hrange : r.range = (H.subgroupOf P).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext a
    constructor
    · rintro ⟨b,rfl⟩; exact b.property
    · intro ha; exact ⟨⟨a,ha⟩,rfl⟩
  let : r.range.Normal := hrange ▸ Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e,c,stable,hc⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let j := d.toMonoidHom.comp r
  have hj (a : H) : j a = 1 ↔ (invariantSubspace ρ H I hH).toRepresentation a = 1 := by
    constructor
    · intro ha
      have hq : q (ι a) = 1 := d.injective (by
        change d (q (ι a)) = 1 at ha
        simpa only [map_one] using ha)
      exact (QuotientGroup.eq_one_iff _).mp hq
    · intro ha
      change d (q (ι a)) = 1
      have hq : q (ι a) = 1 := (QuotientGroup.eq_one_iff (ι a)).mpr ha
      rw [hq,map_one]
  have hjrange : j.range = r.range.map d.toMonoidHom := MonoidHom.range_comp _ _
  let : j.range.Normal := hjrange ▸ Subgroup.Normal.map inferInstance d.toMonoidHom d.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hjne : j.range ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    rw [← hfix]
    intro u hu a
    have ha := (hj a).mp (mem_bot.mp (hz ▸ (show j a ∈ j.range from ⟨a,rfl⟩)))
    exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩ : U)) ha
  let : Nontrivial j.range := j.range.nontrivial_iff_ne_bot.mpr hjne
  have hA : j.range = alternatingGroup (Fin n) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simpa using hn) j.range
  let p := (MulEquiv.subgroupCongr hA).toMonoidHom.comp j.rangeRestrict
  refine ⟨p, (MulEquiv.subgroupCongr hA).surjective.comp j.rangeRestrict_surjective,
    (fun a => (Subtype.ext_iff).trans (hj a)), ?_⟩
  let f := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) I) ≃ₗ[ZMod 2] I).symm.trans c
  refine ⟨f,?_⟩
  intro a w
  exact hc ⟨q (ι a),mem_top _⟩ ⟨w,Submodule.mem_top⟩

private theorem alternating_eight_not_elementary_sylow
    (h : ∀ S : Sylow 2 (alternatingGroup (Fin 8)), IsElementaryAbelian 2 S) : False := by
  let a : alternatingGroup (Fin 8) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
      simp [Equiv.Perm.mem_alternatingGroup, map_mul]⟩
  have ha : orderOf a = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers,ha]; norm_num)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  let := h S
  have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hS (mem_zpowers a))
  have hd := orderOf_dvd_of_pow_eq_one ha2
  rw [ha] at hd
  norm_num at hd

private theorem no_exchanged_eight_of_actor_five
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable D) {L : Subgroup D} (hL : IsComponent D L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I) (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hfive : finrank (ZMod 2) (Additive X) = 5)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 8))) : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  obtain ⟨p,hp,hkill,_⟩ := natural_orbit_coordinates H I hI.invariant
    (hI.isIrrPlus.ne_bot ρ) hfix 8 (by decide) hmodel
  have hcenter : center H = ⊥ := center_eq_bot_of_constituent_quotient ρ h.faithful hi
    H I hI.invariant (hI.isIrrPlus.ne_bot ρ) p hp
    (alternatingGroup.center_eq_bot (by simp)) (fun a ha => (hkill a).mp ha)
  let R := invariantSubspace ρ H I hI.invariant
  have hnoncentral : ¬ R.toRepresentation.asGroupHom.ker ≤ center H := by
    intro hk
    have hj : Function.Injective p := (injective_iff_map_eq_one p).mpr (by
      intro a ha
      apply mem_bot.mp
      rw [← hcenter]
      exact hk (show a ∈ R.toRepresentation.asGroupHom.ker from Units.ext ((hkill a).mp ha)))
    let e := MulEquiv.ofBijective p ⟨hj,hp⟩
    obtain ⟨x,_,hc,_,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
    have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
      apply top_unique
      rw [← hc.sup_eq_top]
      exact sup_le (Homogeneous.le_orbitSpan _ _ I) (le_iSup (fun y : X => I.map (ρ y)) x)
    let j : X →* MulAut (alternatingGroup (Fin 8)) :=
      (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp X.subtype)
    have hj : Function.Injective j := (MulAut.congr e).injective.comp
      (exchanged_conjugation_injective h hi hL hI hgen)
    let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective
      (MonoidHom.ofInjective hj).symm.toMonoidHom (MonoidHom.ofInjective hj).symm.injective
    have hb := (primeRank_le_iff_elementary_card_le _).mp alternating_eight_automorphism_two_rank
      j.range inferInstance
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
      Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hfive] at hb
    norm_num at hb
  obtain ⟨S,_,_,hXS⟩ := hS
  have hnX : (S : Subgroup D) ≤ normalizer (X : Set D) :=
    (normal_subgroupOf_iff_le_normalizer ‹X ≤ (S : Subgroup D)›).mp hXS
  obtain ⟨x,_,hsep⟩ := h.exchanged_pair_separates hn hL hm S hnX
    (cover.some.component_normalizer_index_le_two hL) hI hv
  let N := R.toRepresentation.asGroupHom.ker
  let : IsElementaryAbelian 2 ((((S : Subgroup D).subgroupOf H) ⊓ N) : Subgroup H) :=
    ExchangedKernel.kernel_sylow_elementary ρ H X S hnX R x hsep
  have hcomp (P : Sylow 2 L) : IsElementaryAbelian 2 P :=
    ExchangedKernel.component_sylow_elementary_of_kernel hL S N hnoncentral P
  have hind : (normalizer (L : Set D)).index = 2 := by
    have hb := cover.some.component_normalizer_index_le_two hL
    have hpos := (normalizer (L : Set D)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set D)).index ≠ 1 := by
      intro he
      let : L.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp he)
      have heH : H = L := le_antisymm
        (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top]))
        (le_componentOrbit L ⊤)
      let : IsQuasisimple H := heH.symm ▸ hL.2
      rcases IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
      · exact hnoncentral hc
      · have hle : I ≤ fixedSpace ρ H := by
          intro u hu a
          have ha : R.toRepresentation.asGroupHom a = 1 := MonoidHom.mem_ker.mp (by
            change a ∈ N
            rw [ht]
            exact mem_top a)
          exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : U)) ha
        exact hI.isIrrPlus.ne_bot ρ (bot_unique (hfix ▸ hle))
    omega
  exact alternating_eight_not_elementary_sylow
    (ExchangedOrbit.elementary_sylow_image p hp (ExchangedOrbit.orbit_sylow_elementary hL hind hcomp))

omit [Finite D] [FiniteDimensional (ZMod 2) U] [IsElementaryAbelian 2 X] in
private theorem natural_twist_not_moved
    {H : Subgroup D} [H.Normal] {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ H X I) (hfix : fixedSpace ρ H = ⊥)
    (x : X) (hx : I.map (ρ (x : D)⁻¹) ≠ I) (n : ℕ)
    (e : H ≃* alternatingGroup (Fin n))
    (f : I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin n))
    (hf : ∀ a w, f ((invariantSubspace ρ H I hI.invariant).toRepresentation a w) =
      BinaryPermutation.naturalRepresentation (Fin n) (e a).val (f w))
    (s : Equiv.Perm (Fin n))
    (hs : ∀ a : H, (e (MulAut.conjNormal (x : D) a)).val =
      s * (e a).val * s⁻¹) : False := by
  let σ := BinaryPermutation.naturalRepresentation (Fin n)
  let S := LinearEquiv.ofBijective (σ s) (σ.apply_bijective s)
  let c := f.trans (S.trans f.symm)
  let R := invariantSubspace ρ H I hI.invariant
  have hc (w : I) : f (c w) = σ s (f w) := by
    change f (f.symm _) = _
    rw [f.apply_symm_apply]
    rfl
  let a : RepEquiv R.toRepresentation (conjugateRep R.toRepresentation (x : D)) :=
    .mk c (by
      intro b
      apply LinearMap.ext
      intro w
      apply f.injective
      change f (c (R.toRepresentation b w)) =
        f (R.toRepresentation (MulAut.conjNormal (x : D) b) (c w))
      have hl := (hc (R.toRepresentation b w)).trans (congrArg (σ s) (hf b w))
      have hr := (hf (MulAut.conjNormal (x : D) b) (c w)).trans
        (congrArg (σ (e (MulAut.conjNormal (x : D) b)).val) (hc w))
      apply hl.trans
      apply Eq.trans _ hr.symm
      rw [hs]
      change σ s (σ (e b).val (f w)) = σ (s * (e b).val * s⁻¹) (σ s (f w))
      simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one])
  exact hI.not_equiv_moved ρ hfix x hx
    ⟨(a.trans (conjugateSubrepresentationEquiv ρ H R (x : D)).symm).toRepresentationEquiv⟩

private theorem alternating_six_not_elementary_sylow
    (h : ∀ S : Sylow 2 (alternatingGroup (Fin 6)), IsElementaryAbelian 2 S) : False := by
  let a : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by
      simp [Equiv.Perm.mem_alternatingGroup, map_mul]⟩
  have ha : orderOf a = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers,ha]; norm_num)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  let := h S
  have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hS (mem_zpowers a))
  have hd := orderOf_dvd_of_pow_eq_one ha2
  rw [ha] at hd
  norm_num at hd

private theorem no_exchanged_six
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable D) {L : Subgroup D} (hL : IsComponent D L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I) (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hthree : 3 ≤ finrank (ZMod 2) (Additive X))
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  obtain ⟨p,hp,hkill,f,hf⟩ := natural_orbit_coordinates H I hI.invariant
    (hI.isIrrPlus.ne_bot ρ) hfix 6 (by decide) hmodel
  have hcenter : center H = ⊥ := center_eq_bot_of_constituent_quotient ρ h.faithful hi
    H I hI.invariant (hI.isIrrPlus.ne_bot ρ) p hp
    (alternatingGroup.center_eq_bot (by simp)) (fun a ha => (hkill a).mp ha)
  let R := invariantSubspace ρ H I hI.invariant
  have hnoncentral : ¬ R.toRepresentation.asGroupHom.ker ≤ center H := by
    intro hk
    have hj : Function.Injective p := (injective_iff_map_eq_one p).mpr (by
      intro a ha
      apply mem_bot.mp
      rw [← hcenter]
      exact hk (show a ∈ R.toRepresentation.asGroupHom.ker from Units.ext ((hkill a).mp ha)))
    let e := MulEquiv.ofBijective p ⟨hj,hp⟩
    obtain ⟨x,hx,hc,_,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
    have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
      apply top_unique
      rw [← hc.sup_eq_top]
      exact sup_le (Homogeneous.le_orbitSpan _ _ I) (le_iSup (fun y : X => I.map (ρ y)) x)
    let j : X →* MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp X.subtype)
    have hj : Function.Injective j := (MulAut.congr e).injective.comp
      (exchanged_conjugation_injective h hi hL hI hgen)
    let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective
      (MonoidHom.ofInjective hj).symm.toMonoidHom (MonoidHom.ofInjective hj).symm.injective
    have hcard : 8 ≤ Nat.card j.range := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
        Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
        Nat.card_zmod]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hthree
    have hnatural := AlternatingSix.ShadowLocal.elementary_le_natural_of_eight_le
      j.range hcard (show j x ∈ j.range from ⟨x,rfl⟩)
    obtain ⟨s,hs⟩ := hnatural
    have hα (a : H) : j x (e a) = e (MulAut.conjNormal (x : D) a) := by
      change e (MulAut.conjNormal (x : D) (e.symm (e a))) = _
      rw [e.symm_apply_apply]
    have hs' (a : H) : (e (MulAut.conjNormal (x : D) a)).val =
        s * (e a).val * s⁻¹ := by
      rw [← hα]
      exact (congrArg (fun α : MulAut (alternatingGroup (Fin 6)) => (α (e a)).val) hs).symm
    have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (x : D) x.property)
    apply natural_twist_not_moved hI hfix x (by rwa [hxi]) 6 e f hf s hs'
  obtain ⟨S,_,_,hXS⟩ := hS
  have hnX : (S : Subgroup D) ≤ normalizer (X : Set D) :=
    (normal_subgroupOf_iff_le_normalizer ‹X ≤ (S : Subgroup D)›).mp hXS
  obtain ⟨x,_,hsep⟩ := h.exchanged_pair_separates hn hL hm S hnX
    (cover.some.component_normalizer_index_le_two hL) hI hv
  let N := R.toRepresentation.asGroupHom.ker
  let : IsElementaryAbelian 2 ((((S : Subgroup D).subgroupOf H) ⊓ N) : Subgroup H) :=
    ExchangedKernel.kernel_sylow_elementary ρ H X S hnX R x hsep
  have hcomp (P : Sylow 2 L) : IsElementaryAbelian 2 P :=
    ExchangedKernel.component_sylow_elementary_of_kernel hL S N hnoncentral P
  have hind : (normalizer (L : Set D)).index = 2 := by
    have hb := cover.some.component_normalizer_index_le_two hL
    have hpos := (normalizer (L : Set D)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set D)).index ≠ 1 := by
      intro he
      let : L.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp he)
      have heH : H = L := le_antisymm
        (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top]))
        (le_componentOrbit L ⊤)
      let : IsQuasisimple H := heH.symm ▸ hL.2
      rcases IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
      · exact hnoncentral hc
      · have hle : I ≤ fixedSpace ρ H := by
          intro u hu a
          have ha : R.toRepresentation.asGroupHom a = 1 := MonoidHom.mem_ker.mp (by
            change a ∈ N
            rw [ht]
            exact mem_top a)
          exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : U)) ha
        exact hI.isIrrPlus.ne_bot ρ (bot_unique (hfix ▸ hle))
    omega
  exact alternating_six_not_elementary_sylow
    (ExchangedOrbit.elementary_sylow_image p hp (ExchangedOrbit.orbit_sylow_elementary hL hind hcomp))

private theorem natural_five_point_rank (w : BinaryPermutation.natural (Fin 5)) :
    1 ≤ primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) w) := by
  obtain ⟨u,rfl⟩ := BinaryPermutation.coreToNatural_surjective w
  have hb := BinaryPermutation.PointStabilizerRank.full_stabilizer_lower u.val
  have hc := Fintype.card_congr (Equiv.sumCompl (fun i : Fin 5 => u.val i = 0))
  rw [Fintype.card_sum,Fintype.card_fin] at hc
  change Fintype.card {i : Fin 5 // u.val i = 0} +
    Fintype.card {i : Fin 5 // u.val i ≠ 0} = 5 at hc
  have hl : 1 ≤ primeRank 3 (BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (BinaryPermutation.alternatingRepresentation (Fin 5)) u.val) := by
    omega
  have hi : BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (BinaryPermutation.alternatingRepresentation (Fin 5)) u.val ≤
      BinaryNaturalDual.VectorStabilizers.representationStabilizer
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5))
      (BinaryPermutation.coreToNatural (Fin 5) u) := by
    intro a ha
    apply Subtype.ext
    change (BinaryPermutation.constants (Fin 5)).mkQ
      (BinaryPermutation.representation (Fin 5) a.val u.val) =
      (BinaryPermutation.constants (Fin 5)).mkQ u.val
    change BinaryPermutation.representation (Fin 5) a.val u.val = u.val at ha
    rw [ha]
  exact hl.trans (Theory.GroupTheory.primeRank_le_of_injective 3
    (Subgroup.inclusion hi) (Subgroup.inclusion_injective hi))

private theorem paired_five_point_rank
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (H : Subgroup D)
    (e : H ≃* (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    (c : U ≃ₗ[ZMod 2] (BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5)))
    (hc : ∀ a u, c (ρ (a : H) u) =
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (e a).1 (c u).1,
       BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (e a).2 (c u).2))
    (v : U) : 2 ≤ primeRank 3 (ChapterG.Section10.pointCentralizer ρ v) := by
  let P := ChapterG.Section10.pointCentralizer ρ v
  let A := BinaryNaturalDual.VectorStabilizers.representationStabilizer
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) (c v).1
  let B := BinaryNaturalDual.VectorStabilizers.representationStabilizer
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) (c v).2
  let j : A × B →* P := {
    toFun a := ⟨(e.symm (a.1.val,a.2.val) : D),by
      change ρ (e.symm (a.1.val,a.2.val) : D) v = v
      apply c.injective
      rw [hc,e.apply_symm_apply]
      exact Prod.ext a.1.property a.2.property⟩
    map_one' := by
      apply Subtype.ext
      change (e.symm 1 : D) = 1
      exact congrArg (fun a : H => (a : D)) e.symm.map_one
    map_mul' a b := by
      apply Subtype.ext
      change (e.symm ((a.1.val,a.2.val)*(b.1.val,b.2.val)) : D) = (e.symm (a.1.val,a.2.val) : D) * e.symm (b.1.val,b.2.val)
      exact congrArg (fun a : H => (a : D)) (e.symm.map_mul _ _) }
  have hj : Function.Injective j := by
    intro a b he
    have he' : (e.symm (a.1.val,a.2.val) : D) = (e.symm (b.1.val,b.2.val) : D) :=
      congrArg (fun a : P => (a : D)) he
    have hh := e.symm.injective (Subtype.ext he')
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  have hb := Theory.GroupTheory.primeRank_le_of_injective 3 j hj
  rw [primeRank_prod_eq_add] at hb
  have ha := natural_five_point_rank (c v).1
  have hc := natural_five_point_rank (c v).2
  change 1 ≤ primeRank 3 A at ha
  change 1 ≤ primeRank 3 B at hc
  change 2 ≤ primeRank 3 P
  omega

private theorem no_exchanged_five_of_point_rank
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable D) {L : Subgroup D} (hL : IsComponent D L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hpoint : primeRank 3 (ChapterG.Section10.pointCentralizer ρ v) ≤ 1) : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  obtain ⟨p,hp,hkill,f,hf⟩ := natural_orbit_coordinates H I hI.invariant
    (hI.isIrrPlus.ne_bot ρ) hfix 5 (by decide) hmodel
  obtain ⟨x,hx,hcompl,_,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
  have hk : p.ker ≠ ⊥ := by
    intro hk
    let e := MulEquiv.ofBijective p ⟨(MonoidHom.ker_eq_bot_iff _).mp hk,hp⟩
    let α : MulAut (alternatingGroup (Fin 5)) := (MulAut.congr e) (MulAut.conjNormal (x : D))
    obtain ⟨s,hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).surjective α
    have hs' (a : H) : (e (MulAut.conjNormal (x : D) a)).val =
        s * (e a).val * s⁻¹ := by
      have hh := congrArg (fun β : MulAut (alternatingGroup (Fin 5)) => (β (e a)).val) hs
      change s * (e a).val * s⁻¹ = (e (MulAut.conjNormal (x : D) (e.symm (e a)))).val at hh
      rw [e.symm_apply_apply] at hh
      exact hh.symm
    have hxi : (x : D)⁻¹ = x := inv_eq_iff_mul_eq_one.mpr (by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (x : D) x.property)
    exact natural_twist_not_moved hI hfix x (by rwa [hxi]) 5 e f hf s hs'
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨e,c,hc⟩ := Representation.simple_pair_coordinates ρ h.faithful H
    (invariantSubspace ρ H I hI.invariant)
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 5)) p hp hk f hf
    x hcompl.disjoint hcompl.sup_eq_top
  have hb := paired_five_point_rank ρ H e c hc v
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNatural

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original low-rank exchanged remainder has degree eight and a natural
S₅ constituent. The whole component orbit and the natural S₆ and S₈
constituents have been excluded, retaining the literal action markings. -/
theorem source_large_lowRank_five_constituent_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
      (IsIrreducible F.terminalRepresentation ∧
        ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
          ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
          ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
          ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
            ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
              (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
              v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry
                F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
              (∃ x : F.terminalDot (F.X g), I.map (F.terminalRepresentation x) ≠ I ∧
                IsCompl I (I.map (F.terminalRepresentation x))) ∧
              finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
              finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
              (B.restrict I).Nondegenerate ∧
              ChapterG.Section06.HasModelOn
                (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
                  (componentOrbit C ⊤) (F.terminalDot (F.X g) ⊓
                    subspaceStabilizer F.terminalRepresentation I) I hI.invariant inf_le_right)) ⊤ ⊤
                (BinaryPermutation.naturalRepresentation (Fin 5))) := by
  rcases source_large_lowRank_exchanged_reduction d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH B v hyp hfix hw with hc |
      ⟨hi,C,hC,hm,horth,I,hI,hv,hgeo,hcompl,hdim,_,hnd,n,hn5,hn8,hn7,hmodel⟩
  · exact Or.inl hc
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hcover := source_terminal_cover F d chosen
  have hr := ChapterG.Section11.ExchangedRecognition.exchanged_natural_ranks
    hyp hcover hw hS hn hC hm hI hgeo n hn5 hn8 hmodel
  have hn' : n = 5 := by
    rcases hr with hh | hh | hh
    · exact hh.1
    · have he : n = 6 := hh.1
      subst n
      have hb : 3 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
        rcases hh.2.2.2 with h | h <;> omega
      exact (ExchangedNatural.no_exchanged_six hyp hcover hw hS hn
        hC hm hI hv hgeo hb hmodel).elim
    · have he : n = 8 := hh.1
      subst n
      exact (ExchangedNatural.no_exchanged_eight_of_actor_five hyp hcover hw hS hn
        hC hm hI hv hgeo hh.2.2.2.1 hmodel).elim
  subst n
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 8 := by
    rcases hr with hh | hh | hh <;> omega
  exact Or.inr ⟨hi,C,hC,hm,horth,I,hI,hv,hgeo,hcompl,hdim,hd,hnd,hmodel⟩

/-- Every low-rank branch of the original large extraspecial action now
satisfies the printed G.11 catalogue. The exchanged A₅ pair is excluded by
the actual point-centralizer three-rank bound; no whole-action marking is
assumed. Conversion of this catalogue and the fixed-line branch remain
separate assembly obligations. -/
theorem source_large_lowRank_conclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) := by
  rcases source_large_lowRank_five_constituent_reduction d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH B v hyp hfix hw with hc |
      ⟨hi,C,hC,hm,horth,I,hI,hv,hgeo,hcompl,hdim,hd,hnd,hmodel⟩
  · exact hc
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  let P := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (P.subgroupOf D) ≤ 1 at hu
  have hpD : P ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  exact (ExchangedNatural.no_exchanged_five_of_point_rank hyp (source_terminal_cover F d chosen)
    hw hS hn hC hm hI hgeo hmodel hu).elim

/-- The original source action has only the fixed-line recognition branch
or the printed G.11 catalogue. All low-rank whole-component and exchanged
remainders have been discharged on the literal original action. -/
theorem source_large_catalogue_or_fixed_line (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
          fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
          2 * finrank (ZMod 2) (hatSpace F (F.E g)) = finrank (ZMod 2) (Additive F.Uhat) ∧
          Group.rank (F.terminalDot (F.X g)) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) ∧
          (∀ a b : F.terminalDot (F.X g),
            (∀ w : hatSpace F (F.E g),
              F.terminalRepresentation a w = F.terminalRepresentation b w) → a = b) ∧
          FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g))) ∨
        ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis F d earlier hq
    chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,?_,?_⟩
  · exact ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural
      alternatives F hne g hgP hgH⟩
  by_cases hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))
  · exact Or.inr (source_large_lowRank_conclusion d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH B v hyp hline hfix hw)
  · obtain ⟨hf,hE,hX,hinj⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen structural
      alternatives F hne hZ g hgP hgH v hline hw
    exact Or.inl ⟨hw,hf,hE,hX,hinj,source_fixed_line_module d earlier hq chosen structural
      alternatives F hne hZ hlarge g hgP hgH B v hyp hline hw⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
