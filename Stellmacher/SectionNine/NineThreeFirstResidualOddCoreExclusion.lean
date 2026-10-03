module
public import Stellmacher.SectionNine.NineThreeNormalizedGeometry
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricActorCommutator
public import Theory.GroupTheory.PGroup.OddCoreConjugateContainment

/-!
# Excluding the first residual from the odd-core layer of a common overgroup

For the actual normalized extraction pair in (9.3), let C be any ambient
subgroup containing both extracted groups. The image of the first extracted
two-residual in C/O₂(C) is not contained in its odd core. This proves the
first alternative of the final C₀ argument on p.50, without assuming that C
is itself a two-local subgroup or that it has characteristic two.

If that containment held, the actual inverse first residual conjugator would
compare the first new center with the old penultimate center modulo O₂(C).
Both centers lie in the same elementary terminal module, itself contained in
the second extracted group and hence C. Critical minimality puts the old
center in the first-step core. The join of its ambient image intersected
with C and O₂(C) is therefore a two-group normalized by the second extracted
group and containing the first new center. This makes their commutator a
two-group, contrary to the unchanged second prescribed actor extraction.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.50,
`refs/files/stellmacher-n-group.pdf`. The normal odd-core quotient condition
is explicit and concerns the supplied C; no subnormality is substituted for
it. The full literal extracted residual and its original conjugator are used.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem map_conjugate
    {G H : Type u} [Group G] [Group H] (f : G →* H) (A : Subgroup G) (x : G) :
    (A.conjBy x).map f = (A.map f).conjBy (f x) := by
  change (A.map (MulAut.conj x).toMonoidHom).map f =
    (A.map f).map (MulAut.conj (f x)).toMonoidHom
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

public theorem nine_three_first_residual_not_le_odd_core_layer
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (C : Subgroup H)
    (hEC : (first.E.map (MulAut.conj config.g⁻¹).toMonoidHom).map embedding ⊔
      (second.E.map (MulAut.conj config.g⁻¹).toMonoidHom).map embedding ≤ C) :
    ¬ (((twoResidualAmbient (first.E.map (MulAut.conj config.g⁻¹).toMonoidHom)).map embedding).subgroupOf C).map (QuotientGroup.mk' (pCore 2 C)) ≤
        pPrimeCore 2 (C ⧸ pCore 2 C) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hbLocal : 1 < cp.length := hb
  let c := MulAut.conj config.g⁻¹
  let d := Γ.act config.g cp.a'
  let l := Γ.act config.g first.l
  let m := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let V := VAt Γ d
  let E1 := first.E.map c.toMonoidHom
  let E2 := second.E.map c.toMonoidHom
  let E1H := E1.map embedding
  let E2H := E2.map embedding
  let VH := V.map embedding
  let ZmH := (ZAt Γ m).map embedding
  let ZlH := (ZAt Γ l).map embedding
  let R := (twoResidualAmbient E1).map embedding
  have hE1C : E1H ≤ C := le_sup_left.trans hEC
  have hE2C : E2H ≤ C := le_sup_right.trans hEC
  have hRC : R ≤ C := (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans hE1C
  intro hROdd
  let x := config.first_geometry.x
  have hnew : Γ.act x⁻¹ l = m := config.first_new_vertex
  have hxR : embedding x ∈ R := Subgroup.mem_map_of_mem embedding config.first_geometry.residual_mem
  have hxC : embedding x⁻¹ ∈ C := by rw [map_inv]; exact C.inv_mem (hRC hxR)
  have hxOdd : (QuotientGroup.mk' (pCore 2 C)) ⟨embedding x⁻¹,hxC⟩ ∈
      pPrimeCore 2 (C ⧸ pCore 2 C) := by
    apply hROdd
    refine Subgroup.mem_map_of_mem _ ?_
    change embedding x⁻¹ ∈ R
    rw [map_inv]
    exact R.inv_mem hxR
  have hZmConj : ZmH.conjBy (embedding x⁻¹) = ZlH := by
    have hz : ZAt Γ m = (ZAt Γ l).conjBy x := by
      rw [← hnew]
      change z Γ (Γ.act x⁻¹ l) = _
      rw [z_act,inv_inv]
      rfl
    have hh : (ZAt Γ m).conjBy x⁻¹ = ZAt Γ l := by rw [hz,Subgroup.conjBy_inv]
    rw [← map_conjugate,hh]
  have hZmV : ZAt Γ m ≤ V := by
    change z Γ m ≤ v Γ d
    rw [v,Γ.vAt_def]
    apply le_sSup
    exact ⟨m,hnew ▸ (show Γ.act x⁻¹ l ∈ neighborhood Γ d from config.first_geometry.neighbor),rfl⟩
  have hZlV : ZAt Γ l ≤ V := by
    have hn : first.l ∈ neighborhood Γ cp.a' := by
      rw [first.penultimate]
      exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).1
    have hn' : l ∈ neighborhood Γ d := (mem_neighborhood_iff_adjacent Γ).mpr
      (adjacent_act Γ config.g ((mem_neighborhood_iff_adjacent Γ).mp hn))
    change z Γ l ≤ v Γ d
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨l,hn',rfl⟩
  have hVp : IsPGroup 2 V := by
    have hp := (nine_three_second_extraction_inputs ctx.toLocalContext hb).2.2.1.isPGroup
    have he : V = (VAt Γ cp.a').map c.toMonoidHom := by
      change v Γ (Γ.act config.g cp.a') = _
      rw [v_act]
    rw [he]
    exact hp.map _
  have hVHE2 : VH ≤ E2H := Subgroup.map_mono (by
    have he : E2 = V ⊔ V.conjBy config.second_geometry.x := config.second_geometry.generated
    rw [he]
    exact le_sup_left)
  have hVC : VH ≤ C := hVHE2.trans hE2C
  have hZmVH : ZmH ≤ VH := Subgroup.map_mono hZmV
  have hZlVH : ZlH ≤ VH := Subgroup.map_mono hZlV
  have hZmBound : ZmH ≤ ZlH ⊔ (pCore 2 C).map C.subtype := by
    have hh := conjugate_le_sup_pCore_of_mem_pPrimeCore_image_in 2 C VH ZmH hVC
      (hVp.map embedding) hZmVH (embedding x⁻¹) hxC hxOdd (hZmConj ▸ hZlVH)
    rwa [hZmConj] at hh
  have hZlQ : ZAt Γ l ≤ QAt Γ cp.firstStep := by
    have hold : ZAt Γ first.l ≤ QAt Γ cp.firstStep := by
      apply critical_minimality Γ cp
      rw [Γ.distance_symm,first.penultimate,← cp.path_first]
      have hd := path_distance_le Γ cp 1 (cp.length-1) (by omega) (by omega)
      exact hd.trans_lt (by omega)
    rw [← config.fixes_firstStep]
    change z Γ (Γ.act config.g first.l) ≤ q Γ (Γ.act config.g cp.firstStep)
    rw [z_act,q_act]
    exact Subgroup.map_mono hold
  let Q := (QAt Γ cp.firstStep).map embedding ⊓ C
  let O := (pCore 2 C).map C.subtype
  let M := Q ⊔ O
  have hZlQ' : ZlH ≤ Q := le_inf (Subgroup.map_mono hZlQ) (hZlVH.trans hVC)
  have hZmM : ZmH ≤ M := hZmBound.trans (sup_le_sup_right hZlQ' O)
  have hQp : IsPGroup 2 Q := by
    have hp : IsPGroup 2 (QAt Γ cp.firstStep) := by
      change IsPGroup 2 (q Γ cp.firstStep)
      rw [q,Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2)).map _
    exact (hp.map embedding).to_le inf_le_left
  have hOp : IsPGroup 2 O := (pCore_isPGroup (p := 2)).map _
  have hOC : NormalIn O C := ⟨Subgroup.map_subtype_le _,twoCoreIn_normal C⟩
  have hQO : Q ≤ Subgroup.normalizer O := inf_le_right.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hOC.1).mp hOC.2)
  have hMp : IsPGroup 2 M := hQp.to_sup_of_normal_right' hOp hQO
  have hE2G : E2H ≤ (GAt Γ cp.firstStep).map embedding := Subgroup.map_mono config.second_geometry.group_le
  have hE2Q : E2H ≤ Subgroup.normalizer Q := by
    have hn := stabilizer_le_normalizer_q Γ cp.firstStep
    have hm : (GAt Γ cp.firstStep).map embedding ≤ Subgroup.normalizer ((QAt Γ cp.firstStep).map embedding) := by
      rintro z ⟨a,ha,rfl⟩
      exact Subgroup.le_normalizer_map embedding (Subgroup.mem_map_of_mem embedding (hn ha))
    exact (le_inf (hE2G.trans hm) (hE2C.trans C.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hE2O : E2H ≤ Subgroup.normalizer O := hE2C.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hOC.1).mp hOC.2)
  have hE2M : E2H ≤ Subgroup.normalizer M :=
    (le_inf hE2Q hE2O).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup Q O)
  have hcM : ⁅ZmH,E2H⁆ ≤ M := (Subgroup.commutator_mono hZmM le_rfl).trans
    (Subgroup.le_normalizer_iff_commutator_le_left.mp hE2M)
  have hcp : IsPGroup 2 (⁅ZAt Γ m,E2⁆ : Subgroup G) := by
    have hm : IsPGroup 2 ((⁅ZAt Γ m,E2⁆ : Subgroup G).map embedding) := by
      rw [Subgroup.map_commutator]
      exact hMp.to_le hcM
    exact hm.of_equiv ((⁅ZAt Γ m,E2⁆ : Subgroup G).equivMapOfInjective
      embedding ctx.embedding_injective).symm
  exact geometric_actor_commutator_not_two Γ cp.firstStep (Γ.act config.g second.l) V E2
    (second.A0.map c.toMonoidHom) (c second.actor) config.second_geometry hVp
    (ZAt Γ m) hZmV config.second_actor_center hcp

end Stellmacher.SectionNine
