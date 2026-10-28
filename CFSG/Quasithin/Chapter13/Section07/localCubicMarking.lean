module
public import CFSG.Quasithin.Chapter13.Section07.pairChiefCount
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# A common cubic for the original pair and local point residual

The literal L₁ image is the two-residual of a natural point stabilizer.
Its A₄ marking can be chosen by an even permutation, hence lifted from L.
A cubic subgroup of the original pair exists by Cauchy. Its commutators
on V lie in the original four-group point plane, so coprime decomposition
and |V|=16 give a nonidentity fixed point. Natural A₆ transitivity moves
the original point to this fixed line. Two-perfection then puts the same
actual cubic inside the corresponding L-conjugate of L₁.
The original LT two-core normalizes both groups. These are the marked
source inputs for the separate cubic chief-count comparison.
Source: Aschbacher–Smith, 13.7.10(8), printed p.942.
-/

@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion NaturalAction ChapterF.Section09.Setup
open Section08.TransvectionQuotients.FiveSeed.BarMarking
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

theorem source_local_residual_image
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let C := subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁)
    (F.L₁.subgroupOf (L⊔(T:Subgroup G))).map (permutation d) =
      (pResidual 2 C).map C.subtype := by
  dsimp only
  let X := L⊔(T:Subgroup G)
  let P := X⊓normalizer (V₁:Set G)
  let C := subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁)
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have hPV : V₁≤V := h.point_lt.le.trans h.plus_le
  have hPi : (P.subgroupOf X).map (permutation d)=C := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (permutation_stabilizes_iff d V₁ hPV x).mpr hx.2
    · intro y hy
      obtain ⟨x,rfl⟩ := nonabelian_permutation_surjective d h hU hV y
      exact ⟨x,⟨x.property,(permutation_stabilizes_iff d V₁ hPV x).mp hy⟩,rfl⟩
  have hres : (pResidual 2 P).map P.subtype=F.L₁ := by
    have hh := normalizer_residual_eq L V₁ (T:Subgroup G) T.isPGroup' d.normalizes_L
    change (pResidual 2 P).map P.subtype=(pResidual 2 (L⊓normalizer (V₁:Set G):Subgroup G)).map (L⊓normalizer (V₁:Set G)).subtype at hh
    have hn : normalizer (V₁:Set G)=centralizer (V₁:Set G) := h.normalizer_point_eq
    rw [hn] at hh
    exact hh
  have hsub : ((pResidual 2 P).map P.subtype).subgroupOf X=
      (pResidual 2 (P.subgroupOf X)).map (P.subgroupOf X).subtype := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_left),
      map_embedded_pResidual,map_subgroupOf_eq_of_le (show P≤X from inf_le_left)]
  rw [←hres,hsub,map_embedded_pResidual,hPi]

/-- The actual barred L₁ is a four-letter A₄, via an even ambient conjugator. -/
theorem source_local_residual_even_marking
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁.subgroupOf (L⊔(T:Subgroup G))).map (permutation d)
    ∃l:L,R.map (MulAut.conj (permutation d (inclusion le_sup_left l))).toMonoidHom=K := by
  dsimp only
  let X := L⊔(T:Subgroup G)
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let C := subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁)
  let R := (F.L₁.subgroupOf X).map (permutation d)
  have hR : R=(pResidual 2 C).map C.subtype := source_local_residual_image d h hU hV
  have hdim : Module.finrank (ZMod 2) (image d V₁)=1 :=
    image_dim d V₁ (h.point_lt.le.trans h.plus_le) 1 d.line_card
  obtain ⟨r,hr⟩ := OrdinaryNormalizer.point_residual_conjugate (⊤ : Subgroup S) le_top (image d V₁) hdim
  have hr' : R.map (MulAut.conj r).toMonoidHom=K := by
    rw [hR]
    have he : (⊤⊓subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁) : Subgroup S)=C := inf_of_le_right le_top
    rw [he] at hr
    exact hr
  obtain ⟨t,ht,htA,_⟩ := nonabelian_transposition_images d h hU hV
  have htC : t∈C := by
    have hm : t∈(F.VH.subgroupOf X).map (permutation d) := htA.symm ▸ mem_zpowers t
    obtain ⟨a,ha,hat⟩ := hm
    rw [←hat]
    apply (permutation_stabilizes_iff d V₁ (h.point_lt.le.trans h.plus_le) a).mpr
    exact (Subgroup.centralizer_le_normalizer _) (h.H_centralizes (h.VH_le_H ha))
  have htN : t∈normalizer (R:Set S) := by
    rw [hR]
    exact (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))) htC
  have hte : R.map (MulAut.conj t).toMonoidHom=R := mem_normalizer_iff_map_conj_eq.mp htN
  have hex : ∃r':S,r'∈alternatingGroup (Fin 6) ∧ R.map (MulAut.conj r').toMonoidHom=K := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign r) with hs|hs
    · exact ⟨r,Equiv.Perm.mem_alternatingGroup.mpr hs,hr'⟩
    · refine ⟨r*t,?_,?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup,map_mul,hs,ht.sign_eq]
        decide
      · change R.conjBy (r*t)=K
        rw [conjBy_mul]
        change (R.map (MulAut.conj t).toMonoidHom).conjBy r=K
        rw [hte]
        exact hr'
  obtain ⟨r,hrEven,hr⟩ := hex
  obtain ⟨q,hq⟩ := d.local_quotient.surjective ⟨r,hrEven⟩
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (centralCore L) q
  refine ⟨l,?_⟩
  rw [permutation_L,hl,hq]
  exact hr
/-- A literal cubic in the original pair has a nonidentity fixed point on V. -/
theorem pair_cubic_fixed_point
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hspan : V≤V₃⊔conjugate V₁ (g:G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let I := Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)
    ∃ A : Subgroup G, A≤I ∧ Nat.card A=3 ∧
      ∃v:G,v∈V ∧ v≠1 ∧ v∈centralizer (A:Set G) := by
  dsimp only
  let I := Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)
  obtain ⟨_,⟨e⟩⟩ := pair_twoCore_quotient d h hU hV g hout
  have hquot : Nat.card (I⧸pCore 2 I)=6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G:=I) 3
    ((show 3∣Nat.card (I⧸pCore 2 I) by rw [hquot];decide).trans (card_quotient_dvd_card (pCore 2 I)))
  let A := (zpowers a).map I.subtype
  have hAI : A≤I := map_subtype_le _
  have hAcard : Nat.card A=3 := (card_map_of_injective I.subtype_injective).trans
    ((Nat.card_zpowers a).trans ha)
  obtain ⟨hVE,_,_,_,_⟩ := pair_intersection_layer d h hU g hout
  let Z := V₁⊔conjugate V₁ (g:G)
  have hcomm : ⁅V,A⁆≤Z := (commutator_mono hVE hAI).trans
    (chosen_intersection_central_layer d h hU g hs)
  obtain ⟨_,_,hZcard,_⟩ := pair_point_plane_data d h hU hV g hs hspan hout
  have hIX : I≤L⊔(T:Subgroup G) := by
    apply sup_le ((VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right))
    rintro _ ⟨x,hx,rfl⟩
    change (g:G)⁻¹*x*((g:G)⁻¹)⁻¹∈_
    rw [inv_inv]
    exact mul_mem (mul_mem ((L⊔(T:Subgroup G)).inv_mem g.property)
      (((VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)) hx)) g.property
  have hAV : A≤normalizer (V:Set G) := hAI.trans (hIX.trans d.normalizes_V)
  let : IsElementaryAbelian 2 V := h.elementary
  have hVcard : Nat.card V=16 := by
    rw [Nat.card_congr d.coordinate.toEquiv]
    change Nat.card (natural (Fin 6))=16
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=natural (Fin 6)),finrank_natural_even (Fin 6) (by decide),Nat.card_zmod]
    decide
  have hdecomp := eq_commutator_sup_centralizer_of_solvable_coprime V A hAV
    inferInstance (by rw [hAcard,hVcard];decide)
  have hne : V⊓centralizer (A:Set G)≠⊥ := by
    intro he
    rw [he,sup_bot_eq] at hdecomp
    have hc := Nat.card_le_card_of_injective (inclusion _) (inclusion_injective (hdecomp.le.trans hcomm))
    rw [hVcard,hZcard] at hc
    omega
  obtain ⟨v,hv,hv1⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hne)
  exact ⟨A,hAI,hAcard,v,hv.1,by simpa only [mem_bot] using hv1,hv.2⟩

/-- Every nonidentity vector is the original marked point moved by an element of L. -/
theorem source_point_conjugate (v:G) (hv:v∈V) (hv1:v≠1) :
    ∃l:L, v∈conjugate V₁ (l:G) := by
  obtain ⟨z,hz1,_⟩ := (Nat.card_eq_two_iff' (1:V₁)).mp d.line_card
  let zV : V := ⟨z,d.seed_le (d.plane_le_seed (d.line_le_plane z.property))⟩
  let vV : V := ⟨v,hv⟩
  have hz0 : (d.coordinate zV).toAdd≠0 := by
    intro he
    have hh := d.coordinate.injective (he.trans (map_one d.coordinate).symm)
    have hh' : (z:G)=1 := congrArg (fun x:V=>(x:G)) hh
    exact hz1 (Subtype.ext hh')
  have hv0 : (d.coordinate vV).toAdd≠0 := by
    intro he
    have hh := d.coordinate.injective (he.trans (map_one d.coordinate).symm)
    exact hv1 (congrArg Subtype.val hh)
  obtain ⟨a,ha⟩ := NaturalTransport.transitive_nonzero
    (d.coordinate zV).toAdd (d.coordinate vV).toAdd hz0 hv0
  obtain ⟨q,hq⟩ := d.local_quotient.surjective a
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (centralCore L) q
  have he : (l:G)*(z:G)*(l:G)⁻¹=v := by
    have hh := d.conjugation l zV
    rw [hl,hq] at hh
    change (d.coordinate _).toAdd=naturalRepresentation (Fin 6) a.val (d.coordinate zV).toAdd at hh
    rw [ha] at hh
    exact congrArg Subtype.val (d.coordinate.injective hh)
  refine ⟨l⁻¹,?_⟩
  change v∈V₁.map (MulAut.conj ((l⁻¹:L):G)⁻¹).toMonoidHom
  refine ⟨z,z.property,?_⟩
  change ((l:G)⁻¹)⁻¹*(z:G)*(((l:G)⁻¹)⁻¹)⁻¹=v
  simpa only [inv_inv] using he

omit d in
private theorem cubic_twoPerfect {A:Type*} [Group A] (h:IsPGroup 3 A) : IsPPerfect 2 A := by
  intro N hN hq
  let := hN
  have hd := IsPGroup.disjoint_of_coprime ((h.to_quotient N).to_subgroup ⊤)
    (hq.to_subgroup ⊤) (by decide:Nat.Coprime 3 2)
  apply top_unique
  intro a _
  apply (QuotientGroup.eq_one_iff a).mp
  exact Subgroup.disjoint_def.mp hd (mem_top _) (mem_top _)

/-- The original pair and an L-conjugate of the actual L₁ contain the same cubic. -/
theorem pair_common_cubic
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hspan : V≤V₃⊔conjugate V₁ (g:G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let I := F.VH⊔conjugate F.VH (g:G)
    ∃(A:Subgroup G)(l:L),Nat.card A=3 ∧ A≤I ∧ A≤conjugate F.L₁ (l:G) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let X := L⊔(T:Subgroup G)
  let I := F.VH⊔conjugate F.VH (g:G)
  obtain ⟨A,hAI,hAc,v,hv,hv1,hvc⟩ := pair_cubic_fixed_point d h hU hV g hs hspan hout
  have hAg : IsPGroup 3 A := IsPGroup.of_card (n:=1) (by simpa using hAc)
  have hAp := cubic_twoPerfect hAg
  have hIX : I≤X := by
    have hVX : F.VH≤X := (VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
    apply sup_le hVX
    rintro _ ⟨x,hx,rfl⟩
    change (g:G)⁻¹*x*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact X.mul_mem (X.mul_mem (X.inv_mem g.property) (hVX hx)) g.property
  have hAX := hAI.trans hIX
  let : (L.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer d.normalizes_L)
  have hgen : L.subgroupOf X⊔(T:Subgroup G).subgroupOf X=⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L≤X from le_sup_left),
      map_subgroupOf_eq_of_le (show (T:Subgroup G)≤X from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  have hcore : pResidual 2 X≤L.subgroupOf X := sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top _ _ T.isPGroup'.comap_subtype hgen⟩
  have hAL : A≤L := by
    have hp : IsPPerfect 2 (A.subgroupOf X) := hAp.of_surjective
      (subgroupOfEquivOfLe hAX).symm.toMonoidHom (subgroupOfEquivOfLe hAX).symm.surjective
    have hh := (le_pResidual_of_isPPerfect (A.subgroupOf X) hp).trans hcore
    intro a ha
    exact hh (show (⟨a,hAX ha⟩:X)∈A.subgroupOf X from ha)
  obtain ⟨l,hvl⟩ := source_point_conjugate d v hv hv1
  let P := conjugate V₁ (l:G)
  have hPc : Nat.card P=2 := (card_map_of_injective (MulAut.conj (l:G)⁻¹).injective).trans d.line_card
  have hPC : P≤centralizer (A:Set G) := by
    intro w hw
    by_cases hw1:w=1
    · simpa only [hw1] using (one_mem (centralizer (A:Set G)))
    · have he : (⟨w,hw⟩:P)=⟨v,hvl⟩ :=
        ((Nat.card_eq_two_iff' (1:P)).mp hPc).unique
          (fun hh=>hw1 (congrArg Subtype.val hh)) (fun hh=>hv1 (congrArg Subtype.val hh))
      have he' : w=v := congrArg Subtype.val he
      rw [he']
      exact hvc
  let C := L⊓centralizer (P:Set G)
  have hAC : A≤C := le_inf hAL (le_centralizer_iff.mp hPC)
  have hAR : A≤(pResidual 2 C).map C.subtype := by
    have hp : IsPPerfect 2 (A.subgroupOf C) := hAp.of_surjective
      (subgroupOfEquivOfLe hAC).symm.toMonoidHom (subgroupOfEquivOfLe hAC).symm.surjective
    have hh := map_mono (f:=C.subtype) (le_pResidual_of_isPPerfect (A.subgroupOf C) hp)
    rwa [map_subgroupOf_eq_of_le hAC] at hh
  have hcent : (centralizer (V₁:Set G)).map (MulAut.conj (l:G)⁻¹).toMonoidHom=centralizer (P:Set G) := by
    let e := MulAut.conj (l:G)⁻¹
    apply le_antisymm (map_centralizer_le_centralizer_image _ _)
    intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)
  have he : conjugate F.L₁ (l:G)=(pResidual 2 C).map C.subtype := by
    change ((pResidual 2 (L⊓centralizer (V₁:Set G):Subgroup G)).map
      (L⊓centralizer (V₁:Set G)).subtype).map (MulAut.conj (l:G)⁻¹).toMonoidHom=_
    rw [map_embedded_pResidual,map_inf _ _ _ (MulAut.conj (l:G)⁻¹).injective,
      hcent]
    have hL : L.map (MulAut.conj (l:G)⁻¹).toMonoidHom=L :=
      mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer (L.inv_mem l.property))
    rw [hL]
  exact ⟨A,l,hAc,hAI,he.symm ▸ hAR⟩

/-- The actual LT two-core normalizes both groups used in the cubic comparison. -/
theorem pair_core_normalizes
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (g : (L⊔(T:Subgroup G):Subgroup G)) (l:L) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let I := F.VH⊔conjugate F.VH (g:G)
    let Q := (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    I≤L⊔(T:Subgroup G) ∧ conjugate F.L₁ (l:G)≤L⊔(T:Subgroup G) ∧
      Q≤normalizer (I:Set G) ∧ Q≤normalizer (conjugate F.L₁ (l:G):Set G) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let X := L⊔(T:Subgroup G)
  let Q := X.pCoreIn 2
  have hVX : F.VH≤X := (VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hL1L : F.L₁≤L := (map_subtype_le _).trans inf_le_left
  have hconj (B:Subgroup G) (hB:B≤X) (x:X) : conjugate B (x:G)≤X := by
    rintro _ ⟨b,hb,rfl⟩
    change (x:G)⁻¹*b*((x:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact X.mul_mem (X.mul_mem (X.inv_mem x.property) (hB hb)) x.property
  have hQX : X≤normalizer (Q:Set G) := by
    exact X.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hQT : Q≤(T:Subgroup G) := h.sylow_centralizer.symm.le.trans inf_le_left
  have hQA : Q≤normalizer (F.VH:Set G) := hQT.trans (h.T_le_H.trans (le_normalizer_conjugateSpanBy V H))
  have hQL : Q≤normalizer (F.L₁:Set G) := by
    have hz0 : normalizer (V₁:Set G) ≤ normalizer (centralizer (V₁:Set G):Set G) := by
      exact normalizer_le_normalizer_centralizer V₁
    have hz : (T:Subgroup G) ≤ normalizer (centralizer (V₁:Set G):Set G) :=
      d.line_stable.trans hz0
    exact hQT.trans (((le_inf d.normalizes_L hz).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L⊓centralizer (V₁:Set G))
        (pResidual 2 (L⊓centralizer (V₁:Set G):Subgroup G))))
  have htransport (B:Subgroup G) (hB:Q≤normalizer (B:Set G)) (x:X) :
      Q≤normalizer (conjugate B (x:G):Set G) := by
    have hh := map_mono (f:=(MulAut.conj (x:G)⁻¹).toMonoidHom) hB
    rw [map_normalizer_eq_of_bijective B (MulAut.conj (x:G)⁻¹).bijective] at hh
    have he : Q.map (MulAut.conj (x:G)⁻¹).toMonoidHom=Q :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q:Set G)).inv_mem (hQX x.property))
    rwa [he] at hh
  exact ⟨sup_le hVX (hconj _ hVX g),hconj _ (hL1L.trans le_sup_left) (inclusion le_sup_left l),
    (le_inf hQA (htransport _ hQA g)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _),
    htransport _ hQL (inclusion le_sup_left l)⟩

end CFSG.Quasithin.Chapter13.Section07
