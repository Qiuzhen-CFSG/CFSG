module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSylowFirstCore
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticMarkedFiveAction
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSylowFiveActors
public import Theory.SpecificGroups.ReeTwo.MarkedComplementAlternative
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.FullReeExclusion

/-!
# Recognition and exclusion of the original large quintic endpoint

The actual Sylow actor and marked core coordinates give the complete native
extension alternative. Every incorrect action or nonsplit extension fixes the
actual central point in its intrinsic first core, contradicting the original
middle-core point mover. The remaining standard endpoint is the full Ree
first parabolic, excluded by the proved source centralizer theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem first_core_obstruction_transport
    {K L : Type*} [Group K] [Group L]
    (e : K ≃* L) (z : K)
    (h : Nat.card (ReeTwo.InvertingExtension.firstCore K) = 2048 ∧
      ∃ hz : z ∈ ReeTwo.InvertingExtension.firstCore K,
        ∀ α : MulAut (ReeTwo.InvertingExtension.firstCore K), α ⟨z,hz⟩ = ⟨z,hz⟩) :
    Nat.card (ReeTwo.InvertingExtension.firstCore L) = 2048 ∧
      ∃ hz : e z ∈ ReeTwo.InvertingExtension.firstCore L,
        ∀ α : MulAut (ReeTwo.InvertingExtension.firstCore L), α ⟨e z,hz⟩ = ⟨e z,hz⟩ := by
  obtain ⟨hc,hz,hf⟩ := h
  let d : ReeTwo.InvertingExtension.firstCore K ≃* ReeTwo.InvertingExtension.firstCore L :=
    centralizerUpperCentralSeriesEquiv e 2
  have hz' : e z ∈ ReeTwo.InvertingExtension.firstCore L := (d ⟨z,hz⟩).property
  refine ⟨(Nat.card_congr d.toEquiv).symm.trans hc,hz',?_⟩
  intro α
  have hh := congrArg d (hf (d.trans (α.trans d.symm)))
  have hd : d ⟨z,hz⟩ = ⟨e z,hz'⟩ := Subtype.ext
    (centralizerUpperCentralSeriesEquiv_coe e 2 ⟨z,hz⟩)
  simpa only [MulEquiv.trans_apply,MulEquiv.apply_symm_apply,hd] using hh

private theorem involution_powers {K : Type*} [Group K] (z : K)
    (hz : z ^ 2 = 1) {x : K} (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
  have hr : z ^ n = z ^ (n % 2) := zpow_eq_zpow_emod' n hz
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · left; rw [hr,h]; simp
  · right; rw [hr,h]; simp

/-- The original order-1024 quintic endpoint has the standard native whole
group structure, with all incorrect complement extensions excluded. -/
theorem source_quintic_large_native_endpoint
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024) :
    Nonempty (ReeTwo.Centralizer ≃* H) := by
  classical
  let Q := H.pCoreIn 2
  let S := (T : Subgroup G).subgroupOf H
  have hQH : Q ≤ H := pCoreIn_le 2 H
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow H (T.subtype hH.1.1.2)).trans_eq
      (map_subgroupOf_eq_of_le hH.1.1.2)
  obtain ⟨A,c,s,hAH,hA,hc5,hcA,hsT,hsA,hs,hs4Z,_,_⟩ :=
    source_quintic_large_sylow_five_actors hG T hempty hM hu hmany hcard e H hH hi hlarge
  have hcH : c ∈ H := hAH (hcA ▸ mem_zpowers c)
  have hgen := source_quintic_large_squaring_generates_sylow
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA s hsT hsA hs
  obtain ⟨eQ,hz,_,hfive⟩ := source_quintic_large_marked_five_action
    hG T hempty hM hu hmany hcard e H hH hi hlarge c hcH hc5
  let j : ReeTwo.Core →* H := (inclusion hQH).comp eQ.toMonoidHom
  have hj : Function.Injective j := (inclusion_injective hQH).comp eQ.injective
  have hjS : j.range ≤ S := by
    rintro _ ⟨q,rfl⟩
    exact hQT (eQ q).property
  let cH : H := ⟨c,hcH⟩
  let sH : H := ⟨s,hH.1.1.2 hsT⟩
  have hcH5 : cH ^ 5 = 1 := Subtype.ext (by
    change c ^ 5 = 1
    simpa only [hc5] using pow_orderOf_eq_one c)
  have hsc : sH * cH * sH⁻¹ = cH ^ 2 :=
    Subtype.ext (hs c (hcA ▸ mem_zpowers c))
  have hz2 : (eQ (ReeTwo.Core.root 9) : G) ^ 2 = 1 := by
    have hh := congrArg (Q.subtype.comp eQ.toMonoidHom)
      (show ReeTwo.Core.root 9 ^ 2 = 1 from by decide +kernel)
    simpa only [map_pow,map_one,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype] using hh
  have hfour : sH ^ 4 = 1 ∨ sH ^ 4 = j (ReeTwo.Core.root 9) := by
    rcases involution_powers (eQ (ReeTwo.Core.root 9) : G) hz2 (hz.symm ▸ hs4Z) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hjrange : j.range = Q.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact (eQ q).property
    · intro hx
      refine ⟨eQ.symm ⟨x,hx⟩,?_⟩
      apply Subtype.ext
      exact congrArg (fun q : Q => (q:G)) (eQ.apply_symm_apply ⟨x,hx⟩)
  have hgenS : j.range ⊔ zpowers sH = S := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,hjrange,map_subgroupOf_eq_of_le hQH,MonoidHom.map_zpowers,
      map_subgroupOf_eq_of_le hH.1.1.2]
    exact hgen
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  let f : H →* MulAut ReeTwo.Core := (MulAut.congr eQ.symm).toMonoidHom.comp
    (Q.normalizerMonoidHom.comp (inclusion hHQ))
  have hact (h : H) (q : ReeTwo.Core) : j (f h q) = h * j q * h⁻¹ := by
    apply Subtype.ext
    simp only [j,f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.congr_apply,
      MulEquiv.symm_symm,MulEquiv.trans_apply,MulEquiv.apply_symm_apply]
    rfl
  have hfc : f cH = ReeTwo.Core.c := by
    apply MulEquiv.ext
    intro q
    apply hj
    rw [hact]
    exact Subtype.ext (hfive q).symm
  obtain ⟨hHcard,hTcard,_,_,_⟩ := source_quintic_large_sylow_first_core_geometry
    hG T hempty hM hu hmany hcard e H hH hi hlarge
  let d : S ≃* (T : Subgroup G) := subgroupOfEquivOfLe hH.1.1.2
  have hScard : Nat.card S = 4096 := (Nat.card_congr d.toEquiv).trans hTcard
  rcases ReeTwo.Centralizer.equiv_or_firstCore_obstruction_of_native_five
      hHcard S hScard j hj hjS cH sH hcH5 hsT hsc hfour hgenS f hact hfc with
      hmodel | hbad
  · exact hmodel
  · exfalso
    let z : S := ⟨j (ReeTwo.Core.root 9),hjS ⟨ReeTwo.Core.root 9,rfl⟩⟩
    have hb := first_core_obstruction_transport d z hbad
    apply source_quintic_large_first_core_mark_obstruction
      hG T hempty hM hu hmany hcard e H hH hi hlarge (d z) ?_ ?_ hb
    · exact hz ▸ mem_zpowers (eQ (ReeTwo.Core.root 9) : G)
    · intro he
      have he' : eQ (ReeTwo.Core.root 9) = 1 :=
        Subtype.ext (congrArg (fun t : T => (t:G)) he)
      exact (by decide +kernel : ReeTwo.Core.root 9 ≠ 1)
        (eQ.injective (he'.trans eQ.map_one.symm))

/-- The full Ree endpoint is impossible under the original source hypotheses. -/
theorem source_quintic_large_core_excluded
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    Nat.card (H.pCoreIn 2) ≠ 1024 := by
  intro hlarge
  obtain ⟨d⟩ := source_quintic_large_native_endpoint
    hG T hempty hM hu hmany hcard e H hH hi hlarge
  exact Section02.SolvableAmalgam.source_full_ree_parabolic_exclusion
    hG T hempty hM hu hmany hcard e H hH
    ⟨ReeTwo.ParabolicMarkedComparison.Verified.firstEquiv.symm.trans d⟩

end CFSG.Quasithin.Chapter14.Section06
