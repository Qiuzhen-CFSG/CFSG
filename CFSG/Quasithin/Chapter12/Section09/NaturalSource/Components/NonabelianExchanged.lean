module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianWhole
public import Theory.Representation.SimplePairCoordinates
public import Theory.Representation.BinaryPermutation.PairedPointRank
public import Theory.SpecificGroups.Alternating.SixSubgroupObstructions
public import Theory.GroupTheory.CComponent.NonquasisimpleAction
public import Theory.Representation.BinaryOffender.FaithfulComponentPair

/-!
# Exchanged constituents and the original point component

The literal point-centralizer three-rank bound excludes every remaining
exchanged natural S₅, S₆ or S₈ constituent. For a central constituent
kernel, permutation-induced automorphisms give a forbidden intertwiner
between the moved constituents. For a noncentral kernel the original
Sylow normality forces elementary Sylow subgroups, excluding A₆ and A₈.
In the A₅ case the two complementary actions give actual A₅ × A₅ and
direct-sum coordinates; the Sylow-fixed point then has three-rank at least
two in its centralizer.

A whole irreducible component orbit must equal the image of the original
normal point component: otherwise it centralizes the nontrivial perfect
point residual, contradicting irreducibility. The same-flag application
therefore leaves the original fixed-line branch or a whole action of that
specific point-component image. Neither remaining branch is asserted to
be excluded, and no low-rank witness is inferred from the fixed line.

Source: Aschbacher--Smith G.10.15, G.11.6, 12.8.13(7--8), and 12.9.4,
printed pp.362--366,856,859. The quotient and elementary-kernel arguments
extend ChapterG.Section11.LargeActorExchangedExclusion without its
unavailable half-degree hypothesis.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Exchanged
open ChapterG.Section11
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
private theorem natural_orbit_quotient
    (m : ℕ) (hm5 : 5 ≤ m)
    (H : Subgroup D) [H.Normal] [Group.IsPerfect H]
    (I : Submodule (ZMod 2) U) (hH : H ≤ subspaceStabilizer ρ I)
    (hne : I ≠ ⊥) (hfix : fixedSpace ρ H = ⊥)
    (hm : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin m))) :
    ∃ p : H →* alternatingGroup (Fin m), Function.Surjective p ∧
      (∀ a : H, p a = 1 ↔ (invariantSubspace ρ H I hH).toRepresentation a = 1) ∧
      ∃ c : I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin m),
        ∀ a u, c ((invariantSubspace ρ H I hH).toRepresentation a u) =
          BinaryPermutation.naturalRepresentation (Fin m) (p a).val (c u) := by
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
  have hA : j.range = alternatingGroup (Fin m) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simpa using hm5) j.range
  let p := (MulEquiv.subgroupCongr hA).toMonoidHom.comp j.rangeRestrict
  refine ⟨p, (MulEquiv.subgroupCongr hA).surjective.comp j.rangeRestrict_surjective,
    fun a => (Subtype.ext_iff).trans (hj a),
    (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) I) ≃ₗ[ZMod 2] I).symm.trans c, ?_⟩
  intro a u
  exact hc ⟨q (ι a), mem_top _⟩ ⟨u, Submodule.mem_top⟩


omit [Finite D] [FiniteDimensional (ZMod 2) U] [IsElementaryAbelian 2 X] in
private theorem moved_not_intertwines
    {H : Subgroup D} [H.Normal] {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ H X I) (hfix : fixedSpace ρ H = ⊥)
    (x : X) (hx : I.map (ρ (x : D)⁻¹) ≠ I)
    (c : I ≃ₗ[ZMod 2] I)
    (hc : ∀ a u, c ((invariantSubspace ρ H I hI.invariant).toRepresentation a u) =
      (invariantSubspace ρ H I hI.invariant).toRepresentation
        ((MulAut.conjNormal (x : D) : MulAut H) a) (c u)) : False := by
  let R := invariantSubspace ρ H I hI.invariant
  let e : Representation.RepEquiv R.toRepresentation
      (conjugateRep R.toRepresentation (x : D)) := .mk c (by
        intro a
        apply LinearMap.ext
        intro u
        exact hc a u)
  exact hI.not_equiv_moved ρ hfix x hx
    ⟨(e.trans (conjugateSubrepresentationEquiv ρ H R (x : D)).symm).toRepresentationEquiv⟩

omit [Finite D] [FiniteDimensional (ZMod 2) U] in
set_option backward.isDefEq.respectTransparency false in
private theorem permutation_intertwiner
    {H : Subgroup D} [H.Normal] {I : Submodule (ZMod 2) U}
    (hH : H ≤ subspaceStabilizer ρ I) (m : ℕ)
    (e : H ≃* alternatingGroup (Fin m))
    (c : I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin m))
    (hc : ∀ a u, c ((invariantSubspace ρ H I hH).toRepresentation a u) =
      BinaryPermutation.naturalRepresentation (Fin m) (e a).val (c u))
    (x : D) (σ : Equiv.Perm (Fin m))
    (hσ : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin m))) =
      (MulAut.congr e) (MulAut.conjNormal x : MulAut H)) :
    ∃ t : I ≃ₗ[ZMod 2] I,
      ∀ a u, t ((invariantSubspace ρ H I hH).toRepresentation a u) =
        (invariantSubspace ρ H I hH).toRepresentation
          ((MulAut.conjNormal x : MulAut H) a) (t u) := by
  let τ := BinaryPermutation.naturalRepresentation (Fin m)
  let t := (c.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (τ.asGroupHom σ))).trans c.symm
  have ht (u : I) : c (t u) = τ σ (c u) := c.apply_symm_apply _
  refine ⟨t, fun a u => c.injective ?_⟩
  rw [ht,hc,hc,ht]
  have he := congrArg (fun α : MulAut (alternatingGroup (Fin m)) =>
    (α (e a) : Equiv.Perm (Fin m))) hσ
  change σ * (e a).val * σ⁻¹ = (e ((MulAut.conjNormal x : MulAut H)
    (e.symm (e a)))).val at he
  rw [e.symm_apply_apply] at he
  change τ σ (τ (e a).val (c u)) =
    τ (e ((MulAut.conjNormal x : MulAut H) a)).val (τ σ (c u))
  rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul]
  exact congrArg (fun a => τ a (c u)) (mul_inv_eq_iff_eq_mul.mp he)

private theorem central_kernel_impossible
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hi : IsIrreducible ρ)
    {L : Subgroup D} (hL : IsComponent D L)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤)
    (x : X) (hx : I.map (ρ (x : D)) ≠ I)
    (m : ℕ) (hm : m = 5 ∨ m = 6 ∨ m = 8)
    (hcard : 8 ≤ Nat.card X)
    (p : componentOrbit L ⊤ →* alternatingGroup (Fin m)) (hp : Function.Surjective p)
    (hkill : ∀ a, p a = 1 ↔
      (invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation a = 1)
    (c : I ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin m))
    (hc : ∀ a u, c ((invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation a u) =
      BinaryPermutation.naturalRepresentation (Fin m) (p a).val (c u))
    (hker : (invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation.asGroupHom.ker ≤
      center (componentOrbit L ⊤)) : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  have hm5 : 5 ≤ m := by omega
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  have hz := center_eq_bot_of_constituent_quotient ρ h.faithful hi H I hI.invariant
    (hI.isIrrPlus.ne_bot ρ) p hp (alternatingGroup.center_eq_bot (by simpa using (by omega : 4 ≤ m)))
    (fun a ha => (hkill a).mp ha)
  have hpi : Function.Injective p := (injective_iff_map_eq_one p).mpr (by
    intro a ha
    apply mem_bot.mp
    rw [← hz]
    exact hker (show _ = 1 from Units.ext ((hkill a).mp ha)))
  let e := MulEquiv.ofBijective p ⟨hpi,hp⟩
  let j : X →* MulAut (alternatingGroup (Fin m)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp X.subtype)
  have hj : Function.Injective j := (MulAut.congr e).injective.comp
    (exchanged_conjugation_injective h hi hL hI hgen)
  have hperm : ∃ σ : Equiv.Perm (Fin m),
      (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin m))) = j x := by
    by_cases hm6 : m = 6
    · subst m
      let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective
        (MonoidHom.ofInjective hj).symm.toMonoidHom (MonoidHom.ofInjective hj).symm.injective
      have hlarge : 8 ≤ Nat.card j.range := by
        rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv]
        exact hcard
      exact AlternatingSix.ShadowLocal.elementary_le_natural_of_eight_le j.range hlarge ⟨x,rfl⟩
    · exact GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5 hm6 |>.surjective (j x)
  obtain ⟨σ,hσ⟩ := hperm
  obtain ⟨t,ht⟩ := permutation_intertwiner hI.invariant m e c hc x σ hσ
  have hxi : (x:D)⁻¹ = x := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:D) x.property)
  exact moved_not_intertwines hI hfix x (by simpa only [hxi] using hx) t ht

private def sixEmbedding (m : ℕ) (hm : 6 ≤ m) :
    alternatingGroup (Fin 6) →* alternatingGroup (Fin m) :=
  (((Equiv.Perm.extendDomainHom (Fin.castLEEmb hm).toEquivRange).comp
    (alternatingGroup (Fin 6)).subtype)).codRestrict _ (by
      intro x
      change Equiv.Perm.sign (x.val.extendDomain _) = 1
      rw [Equiv.Perm.sign_extendDomain]
      exact x.prop)

private theorem sixEmbedding_injective (m : ℕ) (hm : 6 ≤ m) :
    Function.Injective (sixEmbedding m hm) := by
  intro x y h
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective (Fin.castLEEmb hm).toEquivRange
    (congrArg Subtype.val h)

private theorem noncentral_kernel_elementary
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hS : NormalSylow ρ v X) (hn : ¬ Group.IsSolvable D)
    {L : Subgroup D} (hL : IsComponent D L) (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I) (hv : v ∉ I)
    (hker : ¬ (invariantSubspace ρ (componentOrbit L ⊤) I hI.invariant).toRepresentation.asGroupHom.ker ≤
      center (componentOrbit L ⊤)) :
    ∀ P : Sylow 2 (componentOrbit L ⊤), IsElementaryAbelian 2 P := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let R := invariantSubspace ρ H I hI.invariant
  let N := R.toRepresentation.asGroupHom.ker
  obtain ⟨S,_,hXS,hSX⟩ := hS
  have hnX : (S : Subgroup D) ≤ normalizer (X : Set D) :=
    (normal_subgroupOf_iff_le_normalizer hXS).mp hSX
  obtain ⟨x,_,hsep⟩ := h.exchanged_pair_separates hn hL hm S hnX
    (cover.some.component_normalizer_index_le_two hL) hI hv
  let : IsElementaryAbelian 2 ((((S : Subgroup D).subgroupOf H) ⊓ N) : Subgroup H) :=
    ExchangedKernel.kernel_sylow_elementary ρ H X S hnX R x hsep
  have hcomp (P : Sylow 2 L) : IsElementaryAbelian 2 P :=
    ExchangedKernel.component_sylow_elementary_of_kernel hL S N hker P
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hL.componentOrbit_top_ne_bot
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
      · exact hker hc
      · have hle : I ≤ fixedSpace ρ H := by
          intro u hu a
          have ha : R.toRepresentation.asGroupHom a = 1 := MonoidHom.mem_ker.mp (by
            change a ∈ N
            rw [ht]
            exact mem_top a)
          exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I =>
            (f.val ⟨u,hu⟩ : U)) ha
        exact hI.isIrrPlus.ne_bot ρ (bot_unique (hfix ▸ hle))
    omega
  exact ExchangedOrbit.orbit_sylow_elementary hL hind hcomp

/-- A point-centralizer three-rank bound excludes all three remaining exchanged
natural constituents. The five-letter case constructs the actual paired action;
the other two contradict the elementary Sylow consequence of a noncentral kernel.
A central kernel is removed using the marked permutation intertwiners. -/
theorem not_natural_of_point_rank
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable D)
    (hr : primeRank 3 (ChapterG.Section10.pointCentralizer ρ v) ≤ 1)
    {L : Subgroup D} (hL : IsComponent D L) (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I) (hv : v ∉ I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (m : ℕ) (hm5 : 5 ≤ m) (hm8 : m ≤ 8)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin m))) : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  obtain ⟨p,hp,hkill,c,hc⟩ := natural_orbit_quotient m hm5 H I hI.invariant
    (hI.isIrrPlus.ne_bot ρ) hfix hmodel
  obtain ⟨x,hx,hcompl,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
  have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top]
    exact sup_le (Homogeneous.le_orbitSpan ρ X I) (le_iSup (fun y : X => I.map (ρ y)) x)
  have hranks := ExchangedRecognition.exchanged_natural_ranks h cover hw hS hn hL hm hI hgeo
    m hm5 hm8 hmodel
  have hmodels : m = 5 ∨ m = 6 ∨ m = 8 := by
    rcases hranks with hh | hh | hh <;> omega
  have hcard : 8 ≤ Nat.card X := by
    have hr3 : 3 ≤ finrank (ZMod 2) (Additive X) := by
      rcases hranks with hh | hh | hh <;> omega
    rw [Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr3
  let R := invariantSubspace ρ H I hI.invariant
  by_cases hk : R.toRepresentation.asGroupHom.ker ≤ center H
  · exact central_kernel_impossible h hi hL hI hgen x hx m hmodels hcard p hp hkill c hc hk
  by_cases hm5eq : m = 5
  · subst m
    have hpk : p.ker ≠ ⊥ := by
      intro hb
      apply hk
      intro a ha
      have hpa : p a = 1 := (hkill a).mpr (congrArg Units.val (MonoidHom.mem_ker.mp ha))
      have ha1 : a = 1 := mem_bot.mp (hb ▸ (show a ∈ p.ker from hpa))
      rw [ha1]
      exact one_mem _
    obtain ⟨e,C,hC⟩ := Representation.simple_pair_coordinates ρ h.faithful H R
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 5)) p hp hpk c hc
      x hcompl.disjoint hcompl.sup_eq_top
    obtain ⟨S,hSv,_⟩ := hS
    have hb := Representation.BinaryPermutationPair.two_le_point_rank ρ H e C hC S v
      (fun _ ha => hSv ha) (ChapterG.Section10.pointCentralizer ρ v) (fun _ => Iff.rfl)
    omega
  · have hm6 : 6 ≤ m := by omega
    have hE := ExchangedOrbit.elementary_sylow_image p hp
      (noncentral_kernel_elementary h cover hS hn hL hm hI hv hk)
    let P : Sylow 2 (alternatingGroup (Fin m)) := Classical.choice inferInstance
    let : IsElementaryAbelian 2 P := hE P
    exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute P
      (fun a b _ _ => show Commute a b from mul_comm a b)
      (sixEmbedding m hm6) (sixEmbedding_injective m hm6)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.Exchanged

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- A whole irreducible component orbit is the image of the original normal
point component. If it were distinct, component dichotomy would make its
whole orbit commute with the nontrivial perfect point residual, contradicting
irreducibility of the literal action. -/
theorem nonabelian_whole_eq_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (C : ComponentGeometry F L)
    {X J : Subgroup F.TerminalHdot} {r : ℕ}
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation X J (componentOrbit J ⊤) r) :
    J = F.terminalDot C.K1 ∧ componentOrbit J ⊤ = J := by
  let K := F.terminalDot C.K1
  let A := F.terminalDot (F.Li L 1)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let : K.Normal := C.normal.map q (QuotientGroup.mk'_surjective _)
  have hAK : A ≤ K := map_mono (comap_mono C.contains)
  have hK : K.IsCComponent := by
    apply (NonquasisimpleAction.ccomponent_image_or_bot C.component q
      (QuotientGroup.mk'_surjective _)).resolve_left
    intro hb
    exact point_hat_ne_bot h hn F hne (le_bot_iff.mp (hb ▸ hAK))
  have he : J = K := by
    rcases h9.component.subnormal_dichotomy K hK.subnormal with hle | hc
    · exact h9.component.isCComponent.eq_of_le hK hle
    · have hnormal : (⊤ : Subgroup F.TerminalHdot) ≤ normalizer (K : Set F.TerminalHdot) := by
        rw [normalizer_eq_top]
      have hcomm : componentOrbit J ⊤ ≤ centralizer (K : Set F.TerminalHdot) :=
        iSup_conjugates_le_centralizer J ⊤ K hnormal hc
      let : Group.IsPerfect A := point_hat_perfect h hn F
      let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr (point_hat_ne_bot h hn F hne)
      exact (not_irreducible_of_faithful_commuting_perfect F.terminalRepresentation
        h9.faithful (componentOrbit J ⊤) A
        (hAK.trans (le_centralizer_iff.mp hcomm)) h9.irreducible).elim
  refine ⟨he,?_⟩
  rw [he]
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer K ⊤ K le_rfl
    (by rw [normalizer_eq_top])) (le_componentOrbit K ⊤)

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components

namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- On the original flag, the extraspecial-center branch has either the
original fixed line or the whole irreducible original point component. All exchanged
natural constituents are excluded using the literal point-centralizer bound. -/
theorem nonabelian_extraspecial_point_component
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU = F.Vi 1 ∧ F.terminalDot (conjugate F.ZU g) = ⊥ ∧
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        ¬ Group.IsSolvable F.TerminalHdot ∧ IsIrreducible F.terminalRepresentation ∧
        2 * (n-1) ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        primeRank 3 (F.terminalPointCentralizer v) ≤ 1 ∧
        (fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
            Submodule.span (ZMod 2) {v} ∨
          (LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
            ∃ C : ComponentGeometry F L,
              ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
                F.terminalRepresentation (F.terminalDot (F.X g))
                (F.terminalDot C.K1) (F.terminalDot C.K1)
                (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))))) := by
  obtain ⟨hZ,hsmall,hX,B,v,hg10,hline,hS,hns,hi,hd,hr,hcases⟩ :=
    nonabelian_extraspecial_recognition modules h hn preferred earlier four F hne g hgP hgH
  let := hX
  refine ⟨hZ,hsmall,hX,B,v,hg10,hline,hS,hns,hi,hd,hr,?_⟩
  rcases hcases with hf | ⟨hw,J,hJ,hm,_,hwhole | hex⟩
  · exact .inl hf
  · obtain ⟨C⟩ := componentGeometry earlier h hn F
    obtain ⟨hJ,hOrbit⟩ := nonabelian_whole_eq_point h hn F hne C hwhole
    rw [hOrbit,hJ] at hwhole
    exact .inr ⟨hw,C,hwhole⟩
  · obtain ⟨I,hI,hv,hgeo,_,_,_,_,m,hm5,hm8,_,hmodel⟩ := hex
    exact (Exchanged.not_natural_of_point_rank hg10 ⟨nonabelian_sqtkCover h F⟩
      hw hS hns hr hJ hm hI hv hgeo m hm5 hm8 hmodel).elim

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
