module

public import Stellmacher.SectionEight.LemmaEightOneOffender
public import Stellmacher.SectionEight.LocalQuotientHypotheses
public import Stellmacher.SectionThree.NormalClosureResidualJoin
public import Stellmacher.SectionOne.OffenderSylowClosureGeneration

/-!
# Local Sylow offender generation from the opposite center

In a local Section Eight context, every subgroup normal in the distinguished Sylow
and containing the opposite vertex center has quotient image containing the
full offender join J on the original initial center. This is the lower
inclusion in the opening image equality of (8.4), Stellmacher, Journal of
Algebra 190 (1997), p.38 of `refs/files/stellmacher-n-group.pdf`. The abbreviated
LaTeX proof does not reproduce that opening correctly.

Let A be the opposite-center image, K its ambient quotient normal closure,
and J0 the intersection of K with the projected Sylow. The proved (8.1)
offender lemma puts A in that Sylow. The lift of J0 contains the opposite
center, so reversed criticality excludes it from the initial two-core.
The local unique-maximal P-set hypotheses and (3.4), through the normal-closure
residual theorem, put the projected local two-residual inside K. Its Sylow
supplement therefore shows that K supplements the projected Sylow. The
Section One selected-product theorem now forces the full offender join into
the image of the given Sylow-normal subgroup. Normality of that image is
transported directly under the witness projection. The original ambient group,
module, and witness's exact action are retained throughout. The canonical
public theorem is a wrapper through `ctx.toLocalContext`, so its existing
statement and consumers are preserved while generated-group contexts can
apply the same proof directly.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

public theorem eight_four_oneJ_le_of_normal_sylow_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ∀ T : Subgroup G, NormalIn T S → ZAt ctx.Γ ctx.criticalPath.a' ≤ T →
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ≤
          (T.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection := by
  classical
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  dsimp only
  intro T hT hZT
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := stabilizer Γ cp.a
  let Sb := (S.subgroupOf P).map w.projection
  let A := ((z Γ cp.a').subgroupOf P).map w.projection
  let Tb := (T.subgroupOf P).map w.projection
  let K := Subgroup.normalClosure (A : Set w.X)
  let J := Sb ⊓ K
  have h74 := lemma_seven_four h Γ cp
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hlen := cp.length_pos
  let last : Γ.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hi : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hi, cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hZendS : z Γ cp.a' ≤ S := hZT.trans hT.1
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnotcentral : ¬ z Γ cp.a' ≤ Subgroup.centralizer (z Γ cp.a : Set G) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w (z Γ cp.a')
    (hZendS.trans hSP) hnotcentral
  have hP := (SevenSix.edge_local_data h Γ cp).1
  obtain ⟨_, U, hU⟩ := hP.1.1.2.1
  have hUSP : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUSP]
  have hA : SectionOne.oneA (V := z Γ cp.a) Sb A :=
    (eight_five_offender_local ctx w).1
  have hAK : A ≤ K := Subgroup.le_normalClosure
  have hAJ : A ≤ J := le_inf hA.1 hAK
  have hJS : J ≤ Sb := inf_le_left
  have hJn : (J.subgroupOf Sb).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs j hj
    exact ⟨Sb.mul_mem (Sb.mul_mem hs hj.1) (Sb.inv_mem hs),
      (inferInstance : K.Normal).conj_mem j hj.2 s⟩
  have hnot : ¬ S ⊓ (J.comap w.projection).map P.subtype ≤ twoCoreAmbient P := by
    intro hC
    apply (h74.commutator_case ctx.commutator_ne).2.2
    intro y hy
    have hyT : y ∈ S ⊓ (J.comap w.projection).map P.subtype := by
      refine ⟨hZendS hy, ?_⟩
      let yP : P := ⟨y, hZendS.trans hSP hy⟩
      exact Subgroup.mem_map.mpr ⟨yP,
        hAJ (Subgroup.mem_map_of_mem w.projection hy), rfl⟩
    have hyQ := hC hyT
    rw [Γ.twoCoreAt_def]
    exact hyQ
  have hres := SectionThree.normalClosure_eq_residual_sup_of_normal_sylow_image
    S (SevenSix.sectionThreeHypotheses h) P
    ((pFamily_iff_pSet (⊤ : Subgroup G) S P).mp hP.1) hP.2
    w.projection w.surjective J hJS hJn hnot
  have hRK : ((twoResidualAmbient P).subgroupOf P).map w.projection ≤ K := by
    have hcl : Subgroup.normalClosure (J : Set w.X) ≤ K :=
      Subgroup.normalClosure_le_normal inf_le_right
    rw [hres] at hcl
    exact le_sup_left.trans hcl
  have hgen : K ⊔ Sb = ⊤ := by
    have hRS : (twoResidualAmbient P).subgroupOf P ⊔ S.subgroupOf P = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le
          (show twoResidualAmbient P ≤ P from Subgroup.map_subtype_le _),
        Subgroup.map_subgroupOf_eq_of_le hSP,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact SectionThree.twoResidual_sup_sylowImage ⟨U, hU⟩
    have hRSb := congrArg (Subgroup.map w.projection) hRS
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map,
      w.projection.range_eq_top_of_surjective w.surjective] at hRSb
    exact top_unique (hRSb ▸ sup_le_sup hRK (le_refl Sb))
  have hTbS : Tb ≤ Sb := Subgroup.map_mono (Subgroup.subgroupOf_mono P hT.1)
  have hTnorm : S ≤ Subgroup.normalizer T :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT.1).mp hT.2
  have hTbn : (Tb.subgroupOf Sb).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTbS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs t ht
    obtain ⟨sP, hsP, rfl⟩ := Subgroup.mem_map.mp hs
    obtain ⟨tP, htP, rfl⟩ := Subgroup.mem_map.mp ht
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem w.projection
      (Subgroup.le_normalizer_iff.mp hTnorm sP.val hsP tP.val htP)
  have hAT : A ≤ Tb := Subgroup.map_mono (Subgroup.subgroupOf_mono P hZT)
  have hresult := SectionOne.oneJ_le_of_offender_normalClosure_supplement hlocal Ub A Tb (hUb.symm ▸ hA) (hUb.symm ▸ hTbS)
    (hUb.symm ▸ hTbn) hAT (hUb.symm ▸ hgen)
  rw [hUb] at hresult
  exact hresult

public theorem eight_four_oneJ_le_of_normal_sylow
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ∀ T : Subgroup G, NormalIn T S → ZAt ctx.Γ ctx.criticalPath.a' ≤ T →
      SectionOne.oneJ (V := ZAt ctx.Γ ctx.criticalPath.a)
        ((S.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) ≤
          (T.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection := by
  exact eight_four_oneJ_le_of_normal_sylow_local ctx.toLocalContext w

end Stellmacher.SectionEight
