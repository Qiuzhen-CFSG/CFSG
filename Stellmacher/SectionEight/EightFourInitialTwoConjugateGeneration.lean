module

public import Stellmacher.SectionEight.EightFourFaithfulSylowMaximal

public import Stellmacher.SectionFiveToSeven.NeighborJoinCore
public import Stellmacher.SectionEight.EightFourSylowOffenderGeneration
public import Stellmacher.SectionEight.LocalQuotientSylowActionSetup
public import Stellmacher.SectionOne.OneSevenOppositeSylow
public import Stellmacher.SectionEight.LemmaEightOneResidualJoin
public import Stellmacher.SectionThree.ResidualFrattiniKernelLift
public import Stellmacher.SectionFiveToSeven.Result7_6.LongPath

/-!
# Two conjugate neighbor modules contain the initial residual at length two

At critical length two in the graph-local Section Eight noncommuting context,
one element of the initial stabilizer conjugates its first neighbor module
so that the two modules together contain the actual initial two-residual.
The same element makes the opposite center and the conjugate edge
generate the initial stabilizer. Both graph-local theorems retain these
conclusions and the original canonical theorems are exact wrappers through
`ctx.toLocalContext`.
The assertions use the full faithful center action and keep the ambient
conjugator and the exact witness instances. They require neither the
central-first-step assumption nor the nontrivial fixed-closure branch.

The neighbor module lies in the edge Sylow and contains the opposite center.
Sylow offender generation therefore puts the full oneJ in its image under
the faithful initial-center quotient. The simultaneous opposite-Sylow theorem
for the entire oneSeven factor product supplies one conjugator generating
that product. Lifting it yields containment of the actual residual modulo
the action kernel. The kernel joined with the Sylow is proper, since the
faithful quotient has nontrivial even order and trivial two-core. Finally,
the actual initial core normalizes both modules. The local Frattini-kernel
lifting theorem consequently removes the kernel and proves containment in
the two modules themselves. The fixed spaces for the original and opposite
critical subgroups span the center module, so faithfulness makes their
intersection trivial. The opposite center consequently has nontrivial image
outside the conjugate Sylow. Maximality of that faithful Sylow gives quotient
generation. Native unique maximality and properness of the kernel joined
with the Sylow then remove the kernel from this second generation equation.

This is the source (1),(2) argument used in Stellmacher (8.4)(8), Journal of
Algebra 190 (1997), p.39. The endpoint version follows by reversing and
normalizing the critical path; no arbitrary four-element subgroup is used
as a substitute for the complete factor system.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

set_option maxHeartbeats 400000 in
/-- One graph-local conjugator simultaneously gives residual containment and opposite generation. -/
public theorem eight_four_initial_opposite_generation_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ x : H, x ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      EAt ctx.Γ ctx.criticalPath.a ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep).conjBy x ∧
      ZAt ctx.Γ ctx.criticalPath.a' ⊔
        (GAt ctx.Γ ctx.criticalPath.a ⊓
          (GAt ctx.Γ ctx.criticalPath.firstStep).conjBy x) =
        GAt ctx.Γ ctx.criticalPath.a := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length = 2 := hlen
  let h := ctx.sectionSeven
  let P := GAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let C := P ⊓ Subgroup.centralizer (Za : Set H)
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have hZQ : Za ≤ QAt Γ cp.a :=
    ((lemma_seven_three h Γ).center_core cp.a cp.firstStep hfirst).trans (Subgroup.map_subtype_le _)
  have hQP : QAt Γ cp.a ≤ P := by
    change q Γ cp.a ≤ P
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  obtain ⟨w⟩ := exists_quotientModuleWitness P Za (hZQ.trans hQP)
    (stabilizer_le_normalizer_z Γ cp.a)
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom Za w.action
  have hlocal := (local_quotient_sylow_action_setup h Γ cp w).1
  obtain ⟨hSP,U,hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  let Sb := (S.subgroupOf P).map w.projection
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  let E := SectionOne.oneSevenGenerated (G := w.X) (V := Za)
  let J := SectionOne.oneJ (V := Za) Sb
  obtain ⟨hEn,hprod,_⟩ := SectionOne.oneSeven_global_product hlocal Ub
  obtain ⟨xb,hxb,hgen,hspan⟩ := SectionOne.oneSevenFactor_exists_opposite_sylow hlocal Ub
    E hEn (SectionOne.oneSevenFactors (G := w.X) (V := Za)) hprod
    (fun D hD => (SectionOne.mem_oneSevenFactors_iff D).mp hD)
  have hident := SectionOne.oneSeven_global_identification hlocal Ub
  rw [← hident.1,hUb] at hgen hspan
  obtain ⟨xP,hxP⟩ := w.surjective xb
  let x : H := xP
  have hVQ : V ≤ q Γ cp.firstStep :=
    SevenSix.neighbor_join_le_core_of_length_gt_one Γ cp (by omega) cp.firstStep
  have hVS : V ≤ S := hVQ.trans (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hVP : V ≤ P := hVS.trans hSP
  have hSnorm : S ≤ Subgroup.normalizer (V : Set H) :=
    (cp.S_le_edge_stabilizers.trans inf_le_right).trans (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hZendV : z Γ cp.a' ≤ V := by
    have hadj : Γ.adjacent cp.firstStep cp.a' := by
      have hadj := cp.path_adj ⟨1,by omega⟩
      have hi : (⟨1,by omega⟩ : Fin cp.length).castSucc = ⟨1,by omega⟩ := rfl
      have hi2 : (⟨1,by omega⟩ : Fin cp.length).succ = ⟨cp.length,by omega⟩ := Fin.ext (by simp; omega)
      rw [hi,hi2,cp.path_first,cp.path_end] at hadj
      exact hadj
    change z Γ cp.a' ≤ v Γ cp.firstStep
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨cp.a', (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hadj, rfl⟩
  have hJV : J ≤ (V.subgroupOf P).map w.projection :=
    eight_four_oneJ_le_of_normal_sylow_local ctx w V
      ⟨hVS,(Subgroup.normal_subgroupOf_iff_le_normalizer hVS).mpr hSnorm⟩ hZendV
  let L := V ⊔ V.conjBy x
  have hconjP : V.conjBy x ≤ P := by
    rintro y ⟨v,hv,rfl⟩
    exact P.mul_mem (P.mul_mem xP.property (hVP hv)) (P.inv_mem xP.property)
  have hLP : L ≤ P := sup_le hVP hconjP
  have hmapconj (A : Subgroup H) (hAP : A ≤ P) : ((A.conjBy x).subgroupOf P).map w.projection =
      ((A.subgroupOf P).map w.projection).conjBy xb := by
    have hi : (A.conjBy x).subgroupOf P = (A.subgroupOf P).conjBy xP := by
      ext v
      constructor
      · intro hv
        obtain ⟨b,hb,heq⟩ := hv
        refine ⟨⟨b,hAP hb⟩,hb,?_⟩
        exact Subtype.ext heq
      · rintro ⟨b,hb,heq⟩
        exact ⟨(b:H),hb,congrArg Subtype.val heq⟩
    rw [hi]
    simp only [Subgroup.conjBy,Subgroup.map_map]
    congr 1
    ext v
    change w.projection (xP*v*xP⁻¹) = xb*w.projection v*xb⁻¹
    simp only [map_mul,map_inv,hxP]
  have hEL : E ≤ (L.subgroupOf P).map w.projection := by
    rw [Subgroup.subgroupOf_sup hVP hconjP,Subgroup.map_sup,hmapconj V hVP]
    rw [hgen]
    exact sup_le_sup hJV (Subgroup.map_mono hJV)
  have hresL : ((twoResidualAmbient P).subgroupOf P).map w.projection ≤
      (L.subgroupOf P).map w.projection := by
    apply le_trans ?_ hEL
    have hres := lemma_eight_one_residual_join_local ctx w
    change SectionOne.oneE (V := Za) Sb = ((EAt Γ cp.a).subgroupOf P).map w.projection ⊔ J at hres
    have heq : SectionOne.oneE (V := Za) Sb = E := by rw [← hUb]; exact hident.2
    rw [heq] at hres
    have hle := (le_sup_left : ((EAt Γ cp.a).subgroupOf P).map w.projection ≤
      ((EAt Γ cp.a).subgroupOf P).map w.projection ⊔ J)
    have hh := hle.trans hres.ge
    change ((twoResidualAmbient P).subgroupOf P).map w.projection ≤ E
    have hEa : EAt Γ cp.a = twoResidualAmbient P := Γ.twoResidualAt_def cp.a
    rw [hEa] at hh
    exact hh
  have hcover : twoResidualAmbient P ≤ L ⊔ C := by
    have hpre := Subgroup.map_le_iff_le_comap.mp hresL
    rw [Subgroup.comap_map_eq,w.kernel_eq] at hpre
    intro e he
    let eP : P := ⟨e,Subgroup.map_subtype_le _ he⟩
    have hep := hpre (show eP ∈ (twoResidualAmbient P).subgroupOf P from he)
    have hemap := Subgroup.mem_map_of_mem P.subtype hep
    rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hLP,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left] at hemap
    exact hemap
  have hCn : (C.subgroupOf P).Normal := by
    have heq : C.subgroupOf P = w.projection.ker := w.kernel_eq.symm
    rw [heq]
    infer_instance
  have hproper : C ⊔ S ≠ P := by
    intro he
    have hmap := congrArg (fun K : Subgroup H => (K.subgroupOf P).map w.projection) he
    rw [Subgroup.subgroupOf_sup inf_le_left hSP,Subgroup.map_sup,
      show C.subgroupOf P = w.projection.ker from w.kernel_eq.symm,
      Subgroup.map_ker_self,bot_sup_eq,Subgroup.subgroupOf_self,Subgroup.map_top_of_surjective _ w.surjective] at hmap
    change Sb = ⊤ at hmap
    have hp : IsPGroup 2 w.X := by
      have hp := Ub.isPGroup'
      rw [hUb,hmap] at hp
      exact hp.of_surjective (⊤ : Subgroup w.X).subtype (fun x => ⟨⟨x,trivial⟩,rfl⟩)
    have hcore : pCore 2 w.X = ⊤ := top_unique (le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩)
    have htopbot := hcore.symm.trans hlocal.twoCore_eq_bot
    have hc : Nat.card w.X = 1 := by
      simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using Subgroup.card_eq_one.mpr htopbot
    have heven := hlocal.G_even
    rw [hc] at heven
    exact (by decide : ¬ Even (1 : ℕ)) heven
  have hQnorm : twoCoreAmbient P ≤ Subgroup.normalizer L := by
    have hQV : twoCoreAmbient P ≤ Subgroup.normalizer V :=
      ((show twoCoreAmbient P = q Γ cp.a from (Γ.twoCoreAt_def cp.a).symm) ▸
        (SevenSix.local_cores_le_edge_sylow h Γ cp).1).trans hSnorm
    have hQconj : twoCoreAmbient P ≤ Subgroup.normalizer (V.conjBy x) := by
      apply Subgroup.le_normalizer_iff.mpr
      intro a ha v hv
      obtain ⟨b,hb,rfl⟩ := hv
      let aP : P := ⟨a,Subgroup.map_subtype_le _ ha⟩
      have hQx : x⁻¹*a*x ∈ twoCoreAmbient P := by
        have hn := SevenSix.stabilizer_le_normalizer_q Γ cp.a (P.inv_mem xP.property)
        have hqa : a ∈ q Γ cp.a := by
          rw [q,Γ.twoCoreAt_def]
          exact ha
        have hh := (Subgroup.mem_normalizer_iff.mp hn a).mp hqa
        rw [q,Γ.twoCoreAt_def] at hh
        change x⁻¹ * a * (x⁻¹)⁻¹ ∈ twoCoreAmbient P at hh
        simpa only [inv_inv] using hh
      refine ⟨(x⁻¹*a*x)*b*(x⁻¹*a*x)⁻¹,
        Subgroup.le_normalizer_iff.mp hQV _ hQx _ hb, ?_⟩
      simp [MulAut.conj_apply,mul_assoc]
    exact (le_inf hQV hQconj).trans (Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine ⟨x,xP.property,?_,?_⟩
  · rw [show EAt Γ cp.a = twoResidualAmbient P from Γ.twoResidualAt_def cp.a]
    exact SectionThree.residual_le_of_le_sup_proper_normal_kernel S (SevenSix.sectionThreeHypotheses h)
      P ((pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1)
      (SevenSix.edge_local_data h Γ cp).1.2 C L inf_le_left hCn hproper hLP hQnorm hcover
  · let Y := ZAt Γ cp.a'
    let K := (Y.subgroupOf P).map w.projection
    have hYP : Y ≤ P := (lemma_seven_four h Γ cp).reverse_containment.1
    have hKJ : K ≤ J := le_sSup (eight_five_offender_local ctx w).1
    have hKne : K ≠ ⊥ := by
      intro hK
      apply ctx.commutator_ne
      have hker : Y.subgroupOf P ≤ w.projection.ker := by
        rw [← Subgroup.map_eq_bot_iff]
        exact hK
      rw [w.kernel_eq] at hker
      have hYC : Y ≤ Subgroup.centralizer (Za : Set H) := by
        intro y hy
        exact (hker (show (⟨y,hYP hy⟩ : P) ∈ Y.subgroupOf P from hy)).2
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hYC
    have hJJ : J ⊓ J.conjBy xb = ⊥ := by
      apply le_bot_iff.mp
      intro a ha
      let F := (w.action a).toMonoidHom.eqLocus (MonoidHom.id Za)
      have hleft : FixedPoints.subgroup J Za ≤ F := by
        intro v hv
        exact hv ⟨a,ha.1⟩
      have hright : FixedPoints.subgroup (J.conjBy xb) Za ≤ F := by
        intro v hv
        exact hv ⟨a,ha.2⟩
      have htop : (⊤ : Subgroup Za) ≤ F := by
        rw [← hspan]
        exact sup_le hleft hright
      have hfixed : a ∈ fixingSubgroup w.X (Set.univ : Set Za) := by
        rw [mem_fixingSubgroup_iff]
        intro v _
        exact htop (Subgroup.mem_top v)
      rw [hlocal.action_faithful] at hfixed
      exact hfixed
    have hJid : J = Sb ⊓ E := by
      simpa only [hUb] using hident.1
    have hEn : E.Normal := hEn
    have hEconj : E.conjBy xb = E :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer_eq_top (H := E)) ▸ Subgroup.mem_top xb)
    have hJconj : (Sb.conjBy xb) ⊓ E = J.conjBy xb := by
      rw [hJid]
      change Sb.map (MulAut.conj xb).toMonoidHom ⊓ E =
        (Sb ⊓ E).map (MulAut.conj xb).toMonoidHom
      rw [Subgroup.map_inf _ _ _ (MulAut.conj xb).injective]
      change Sb.conjBy xb ⊓ E = Sb.conjBy xb ⊓ E.conjBy xb
      rw [hEconj]
    have hKnot : ¬ K ≤ Sb.conjBy xb := by
      intro hle
      apply hKne
      apply le_bot_iff.mp
      rw [← hJJ]
      exact le_inf hKJ (by
        rw [← hJconj]
        exact le_inf hle (hKJ.trans (hJid ▸ inf_le_right)))
    have hnewMax : IsCoatom (Sb.conjBy xb) :=
      (OrderIso.isCoatom_iff (MulAut.conj xb).mapSubgroup Sb).mpr (eight_four_faithful_sylow_isCoatom_local ctx w)
    have hKG : K ⊔ Sb.conjBy xb = ⊤ := by
      apply hnewMax.2
      exact lt_of_le_of_ne le_sup_right (by
        intro he
        apply hKnot
        exact le_sup_left.trans he.symm.le)
    have hSxP : S.conjBy x ≤ P := by
      rintro y ⟨s, hs, rfl⟩
      exact P.mul_mem (P.mul_mem xP.property (hSP hs)) (P.inv_mem xP.property)
    let D := Y ⊔ S.conjBy x
    have hDP : D ≤ P := sup_le hYP hSxP
    have hDimage : (D.subgroupOf P).map w.projection = ⊤ := by
      rw [Subgroup.subgroupOf_sup hYP hSxP, Subgroup.map_sup, hmapconj S hSP]
      exact hKG
    have hDC : D ⊔ C = P := by
      have hh := congrArg (Subgroup.comap w.projection) hDimage
      rw [Subgroup.comap_map_eq, Subgroup.comap_top, w.kernel_eq] at hh
      have hm := congrArg (Subgroup.map P.subtype) hh
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDP,
        Subgroup.map_subgroupOf_eq_of_le inf_le_left,
        ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hm
      exact hm
    have hPset := (pFamily_iff_pSet _ _ _).mp (SevenSix.edge_local_data h Γ cp).1.1
    obtain ⟨M, hM, hSM, huniq⟩ := hPset.2
    have hCM : C ≤ M.map P.subtype := le_sup_left.trans
      (SectionThree.le_unique_maximal_over huniq le_sup_right
        (sup_le inf_le_left hSP) hproper)
    have hMproper : M.map P.subtype ≠ P := by
      intro he
      apply hM.1
      apply Subgroup.map_injective P.subtype_injective
      simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype] using he
    have hPconj (a : P) : P.conjBy (a : H) = P :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer a.property)
    have hCconj : C.conjBy x⁻¹ = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (show C ≤ P from inf_le_left)).mp
          hCn (P.inv_mem xP.property))
    have hDtop : D = P := by
      by_contra hproperD
      let D' := D.conjBy x⁻¹
      have hD'P : D' ≤ P :=
        (Subgroup.map_mono hDP).trans_eq (hPconj xP⁻¹)
      have hD'ne : D' ≠ P := by
        intro he
        have hm := congrArg (fun A : Subgroup H => A.conjBy x) he
        change (D.conjBy x⁻¹).conjBy x = P.conjBy x at hm
        rw [Subgroup.conjBy_inv', hPconj xP] at hm
        exact hproperD hm
      have hSD' : S ≤ D' := by
        have hh := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom)
          (le_sup_right : S.conjBy x ≤ D)
        change (S.conjBy x).conjBy x⁻¹ ≤ D' at hh
        rw [Subgroup.conjBy_inv] at hh
        exact hh
      have hD'M : D' ≤ M.map P.subtype :=
        SectionThree.le_unique_maximal_over huniq hSD' hD'P hD'ne
      have hD'C : D' ⊔ C = P := by
        have hh := congrArg (fun A : Subgroup H => A.conjBy x⁻¹) hDC
        change (D ⊔ C).map (MulAut.conj x⁻¹).toMonoidHom = P.conjBy x⁻¹ at hh
        rw [Subgroup.map_sup] at hh
        change D' ⊔ C.conjBy x⁻¹ = P.conjBy x⁻¹ at hh
        rw [hCconj] at hh
        have hPx : P.conjBy x⁻¹ = P := by exact hPconj xP⁻¹
        rw [hPx] at hh
        exact hh
      apply hMproper
      apply le_antisymm (Subgroup.map_subtype_le _)
      exact hD'C.ge.trans (sup_le hD'M hCM)
    apply le_antisymm (sup_le hYP inf_le_left)
    exact hDtop.ge.trans (sup_le_sup le_rfl (le_inf hSxP
      (Subgroup.map_mono (cp.S_le_edge_stabilizers.trans inf_le_right))))

/-- One actual conjugator makes two neighbor modules contain the initial residual. -/
public theorem eight_four_initial_two_conjugate_generation_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ x : H, x ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      EAt ctx.Γ ctx.criticalPath.a ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep).conjBy x := by
  obtain ⟨x, hx, hresidual, _⟩ := eight_four_initial_opposite_generation_local ctx hlen
  exact ⟨x, hx, hresidual⟩

/-- The canonical context retains the same simultaneous generation conclusion. -/
public theorem eight_four_initial_opposite_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ x : H, x ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      EAt ctx.Γ ctx.criticalPath.a ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep).conjBy x ∧
      ZAt ctx.Γ ctx.criticalPath.a' ⊔
        (GAt ctx.Γ ctx.criticalPath.a ⊓
          (GAt ctx.Γ ctx.criticalPath.firstStep).conjBy x) =
        GAt ctx.Γ ctx.criticalPath.a := by
  exact eight_four_initial_opposite_generation_local ctx.toLocalContext hlen

/-- The canonical containment statement is unchanged. -/
public theorem eight_four_initial_two_conjugate_generation
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hlen : ctx.criticalPath.length = 2) :
    ∃ x : H, x ∈ GAt ctx.Γ ctx.criticalPath.a ∧
      EAt ctx.Γ ctx.criticalPath.a ≤ VAt ctx.Γ ctx.criticalPath.firstStep ⊔
        (VAt ctx.Γ ctx.criticalPath.firstStep).conjBy x := by
  exact eight_four_initial_two_conjugate_generation_local ctx.toLocalContext hlen

end Stellmacher.SectionEight
