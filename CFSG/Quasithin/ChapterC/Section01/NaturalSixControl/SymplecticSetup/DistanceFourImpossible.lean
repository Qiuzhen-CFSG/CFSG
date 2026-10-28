module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardResidualBridge
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardCoreKernel
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardMovedSpanNatural
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanKernelDerived
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Terminal.Transport
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanEndpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
/-!
# Excluding critical distance four in the native symplectic source

Use the prescribed backward path in reverse, retaining its endpoint orbit and
its endpoint moving index. The source endpoint bound and faithful moved quotient
place the core commutator inside the product of U and the moved forward span.
Its derived line then controls the cross commutator with the opposite kernel.

The two central edge lines have product of order at most four. The native
symmetric-six small-section theorem makes the neighboring component fix the
original derived line. That line lies in its natural moving layer, so it vanishes,
contradicting its proved order two. All conjugations use the same actual path.

Source: MS93 (3.10)(i), printed pp.879--881, and the terminal argument in
(5.12), printed p.927, for the symplectic branch of Aschbacher--Smith C.1.37.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem derived_fixed_of_two_central_lines
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (D : Subgroup M) (hDQ : D≤pCore 2 M)
    (hDN : R≤normalizer (D:Set M))
    (hDcard : Nat.card (⁅D,D⁆:Subgroup M)≤2)
    (hDC : ⁅D,D⁆≤centralizer (R:Set M))
    (hCcard : Nat.card (⁅⁅pCore 2 M,L⁆,⁅pCore 2 M,L⁆⁆:Subgroup M)≤2)
    (hCC : ⁅⁅pCore 2 M,L⁆,⁅pCore 2 M,L⁆⁆≤centralizer (R:Set M))
    (hcomm : ⁅D,⁅pCore 2 M,L⁆⁆≤⁅⁅pCore 2 M,L⁆,⁅pCore 2 M,L⁆⁆) :
    ⁅D,D⁆≤centralizer (L:Set M) := by
  let C := ⁅pCore 2 M,L⁆
  let N := D⊔C
  let H := ⁅D,D⁆⊔⁅C,C⁆
  have hCQ : C≤pCore 2 M := commutator_le_left _ _
  have hDR : D≤R := hDQ.trans s.core_le
  have hCR : C≤R := hCQ.trans s.core_le
  have hHR : H≤centralizer (R:Set M) := sup_le hDC hCC
  have hHN : R≤normalizer (H:Set M) :=
    (le_centralizer_iff.mp hHR).trans (Subgroup.centralizer_le_normalizer _)
  have hNC : ⁅N,N⁆≤H := by
    apply commutator_sup_le_of_relative_normal R D C N H hHN hDR hCR
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal R D C D H hHN hDR hCR le_sup_left
      exact (by rw [commutator_comm]; exact hcomm.trans le_sup_right)
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal R D C C H hHN hDR hCR
        (hcomm.trans le_sup_right) le_sup_right
  have hNnorm : (⊤:Subgroup M)≤normalizer (N:Set M) := by
    rw [←s.sup_eq_top]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      exact (commutator_mono (sup_le hDQ hCQ) le_rfl).trans le_sup_right
    · apply le_trans (le_inf hDN (le_normalizer_of_normal (H:=C)))
        (normalizer_inf_normalizer_le_normalizer_sup D C)
  let : N.Normal := ⟨by
    intro n hn g
    exact (le_normalizer_iff.mp hNnorm g (mem_top _)) n hn⟩
  have hNQ : ⁅N,N⁆≤pCore 2 M :=
    (show ⁅N,N⁆≤N from commutator_le_left _ _).trans (sup_le hDQ hCQ)
  have hcardH : Nat.card H≤4 := by
    have hprod : ((⁅D,D⁆:Subgroup M):Set M)*((⁅C,C⁆:Subgroup M):Set M)=(H:Set M) :=
      (coe_mul_of_right_le_normalizer_left _ _
        (((commutator_le_left C C).trans hCR).trans
          ((le_centralizer_iff.mp hDC).trans (Subgroup.centralizer_le_normalizer _)))).symm
    let f : (⁅D,D⁆:Subgroup M)×(⁅C,C⁆:Subgroup M)→H :=
      fun x => ⟨x.1*x.2,H.mul_mem (mem_sup_left x.1.property) (mem_sup_right x.2.property)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x,hx⟩
      have hx' : x∈((⁅D,D⁆:Subgroup M):Set M)*((⁅C,C⁆:Subgroup M):Set M) := hprod.symm ▸ hx
      obtain ⟨a,ha,b,hb,rfl⟩ := hx'
      exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩
    have hh := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_prod] at hh
    exact hh.trans (Nat.mul_le_mul hDcard hCcard)
  have hcard : (⊥:Subgroup M).relIndex ⁅N,N⁆≤8 := by
    rw [relIndex_bot_left]
    exact (card_le_of_le hNC).trans (hcardH.trans (by decide))
  have hker : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hh := commutator_pResidual_le_of_symmetricSix_small_section s.projection
    (s.projection_surjective_of_radical_image_le_conjugate u hfull.le) hker ⁅N,N⁆ ⊥
    (hNQ.trans_eq s.projection_kernel.symm) hcard
  rw [s.residual] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp ((commutator_mono (commutator_mono le_sup_left le_sup_left) le_rfl).trans hh))

include s in
private theorem centerTransfer_coordinates {c t : Vertex R}
    (hc : color R c=false) (hct : Adjacent R c t) :
    ∃ i : M→*FreeAmalgam R, Function.Injective i ∧
      R.map i=Q R t ∧ (pCore 2 M).map i=Q R c ∧ L.map i=Ltilde R c := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common R c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_⟩
    · have he := Q_act R g (beta R)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act R g (alpha R)
      rw [Q_alpha R s.two_group s.core_le] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act R g (alpha R)
      rw [Ltilde_alpha,s.residual] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

private theorem derived_fixed_of_two_central_lines_at
    (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex R} (hc : color R c=false) (hct : Adjacent R c t)
    (D : Subgroup (FreeAmalgam R)) (hDQ : D≤Q R c)
    (hDN : Q R t≤normalizer (D:Set (FreeAmalgam R)))
    (hDcard : Nat.card (⁅D,D⁆:Subgroup (FreeAmalgam R))≤2)
    (hDC : ⁅D,D⁆≤centralizer (Q R t:Set (FreeAmalgam R)))
    (hCcard : Nat.card (⁅⁅Q R c,Ltilde R c⁆,⁅Q R c,Ltilde R c⁆⁆:Subgroup (FreeAmalgam R))≤2)
    (hCC : ⁅⁅Q R c,Ltilde R c⁆,⁅Q R c,Ltilde R c⁆⁆≤centralizer (Q R t:Set (FreeAmalgam R)))
    (hcomm : ⁅D,⁅Q R c,Ltilde R c⁆⁆≤⁅⁅Q R c,Ltilde R c⁆,⁅Q R c,Ltilde R c⁆⁆) :
    ⁅D,D⁆≤centralizer (Ltilde R c:Set (FreeAmalgam R)) := by
  obtain ⟨i,hi,hiR,hiQ,hiL⟩ := s.centerTransfer_coordinates hc hct
  let D₀ := D.comap i
  let C₀ := ⁅pCore 2 M,L⁆
  have hDm : D₀.map i=D := map_comap_eq_self (hDQ.trans (hiQ ▸ map_le_range i _))
  have hCm : C₀.map i=⁅Q R c,Ltilde R c⁆ := by rw [map_commutator,hiQ,hiL]
  have hDDm : (⁅D₀,D₀⁆:Subgroup M).map i=⁅D,D⁆ := by rw [map_commutator,hDm]
  have hCCm : (⁅C₀,C₀⁆:Subgroup M).map i=⁅⁅Q R c,Ltilde R c⁆,⁅Q R c,Ltilde R c⁆⁆ := by
    rw [map_commutator,hCm]
  have hD₀Q : D₀≤pCore 2 M := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hDm,hiQ]
  have hD₀N : R≤normalizer (D₀:Set M) :=
    ((map_le_iff_le_comap).mp (hiR ▸ hDN)).trans (le_normalizer_comap i)
  have hD₀card : Nat.card (⁅D₀,D₀⁆:Subgroup M)≤2 := by
    rwa [←hDDm,card_map_of_injective hi] at hDcard
  have hC₀card : Nat.card (⁅C₀,C₀⁆:Subgroup M)≤2 := by
    rwa [←hCCm,card_map_of_injective hi] at hCcard
  have hcentral (A B : Subgroup M)
      (hh : A.map i≤centralizer (B.map i:Set (FreeAmalgam R))) : A≤centralizer (B:Set M) := by
    intro a ha b hb
    apply hi
    simpa only [map_mul] using hh (mem_map_of_mem i ha) (i b) (mem_map_of_mem i hb)
  have hD₀C : ⁅D₀,D₀⁆≤centralizer (R:Set M) := by
    apply hcentral
    rwa [hDDm,hiR]
  have hC₀C : ⁅C₀,C₀⁆≤centralizer (R:Set M) := by
    apply hcentral
    rwa [hCCm,hiR]
  have hcomm₀ : ⁅D₀,C₀⁆≤⁅C₀,C₀⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [map_commutator,hDm,hCm,hCCm]
  have hh := s.derived_fixed_of_two_central_lines u hfull D₀ hD₀Q hD₀N
    hD₀card hD₀C hC₀card hC₀C hcomm₀
  have hm := (map_mono (f:=i) hh).trans (map_centralizer_le_centralizer_image _ _)
  change (⁅D₀,D₀⁆:Subgroup M).map i≤centralizer (L.map i:Set (FreeAmalgam R)) at hm
  rwa [hDDm,hiL] at hm

/-- The opposite selected critical path retains the required endpoint orbit
and the already proved endpoint moving index. -/
private theorem exists_opposite_critical_path_with_orbit
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ∃ m g, ∃ q : CriticalPath R s.geometry (p.walk.getVert 2) m,
      q.walk.getVert 1=p.walk.getVert 1 ∧ q.walk.getVert 2=alpha R ∧
      g∈stabilizer R (alpha R) ∧ m=act R g (p.walk.getVert 2) ∧
      (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R m)=2 := by
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  obtain ⟨c⟩ := s.exists_coordinatedChoice h u hfull p _ hct
  obtain ⟨back,hb1,hb2,hb3⟩ :=
    c.exists_prescribed_backward_path s h u hfull (by omega : 2<s.geometry.b R)
  have hend : p.walk.getVert (p.walk.length-2)=p.walk.getVert 2 := by rw [hl]
  have hcrit := critical_reverse R s.geometry s.edgeCentralizerCondition
    c.alpha1 back.start_color (by rw [s.geometry.distance_constant c.alpha1 back.start_color]; exact s.criticalDistance_pos)
      _ back.end_color back.critical
  let q : CriticalPath R s.geometry (p.walk.getVert 2) c.alpha1 := {
    start_color := hend ▸ back.end_color
    walk := back.walk.reverse.copy hend rfl
    shortest := by rw [SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_reverse,
      back.shortest,SimpleGraph.dist_comm,hend]
    critical := by simpa only [hend] using hcrit }
  have hbl : back.walk.length=4 := back.length_eq_b.trans hb
  refine ⟨c.alpha1,c.transporter,q,?_,?_,c.transporter_mem,c.alpha1_eq,?_⟩
  · change (back.walk.reverse.copy hend rfl).getVert 1=p.walk.getVert 1
    simpa only [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_reverse,hbl,Nat.reduceSub] using hb3
  · change (back.walk.reverse.copy hend rfl).getVert 2=alpha R
    simpa only [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_reverse,hbl,Nat.reduceSub] using hb2
  · have hi := s.forward_moving_index_eq_two_of_distance_four h u hfull hb p
    have hBn : c.transporter⁻¹∈normalizer
        (B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R)) :=
      (Escape.Propagation.Rigidity.B_normalized (by omega : 2<s.geometry.b R) (alpha R) rfl)
        ((stabilizer R (alpha R)).inv_mem c.transporter_mem)
    have hBm : (B R (alpha R) (s.geometry.Z_normal _)).map
        (MulAut.conj c.transporter⁻¹).toMonoidHom=B R (alpha R) (s.geometry.Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp hBn
    rw [c.alpha1_eq,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hi
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem core_derived_bounds_of_central_supplement
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hweak : ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤
      U R (alpha R)⊔forwardMovedSpan R (p.walk.getVert 2)) :
    let C := ⁅Q R (alpha R),Ltilde R (alpha R)⁆
    Nat.card (⁅C,C⁆:Subgroup (FreeAmalgam R))=2 ∧
      ⁅C,C⁆≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) ∧
      ⁅Q R (alpha R)⊓Q R (p.walk.getVert 2),C⁆≤⁅C,C⁆ := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let P₀ := forwardMovedSpan R (p.walk.getVert 2)
  let C := ⁅Q R (alpha R),Ltilde R (alpha R)⁆
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  have hspan := s.forward_span_derived_eq_line h u hfull hb p
  have hmove := s.forward_moved_span_derived_eq h u hfull hsq hb p
  have hP₀P : P₀≤P := forwardMovedSpan_le R _
  have hPT : P≤T₀ := s.forward_span_le_hyperplane_kernel (by omega) p
  have hPQ : P≤Q R (alpha R) := hPT.trans inf_le_left
  have hP₀Q := hP₀P.trans hPQ
  have hP₀C : P₀≤C := commutator_mono hPQ le_rfl
  have hUQ : U R (alpha R)≤Q R (alpha R) := by
    rw [h.U_eq_module,Q_alpha R s.two_group s.core_le]
    exact map_mono s.module_le_core
  have hUC : U R (alpha R)≤centralizer (Q R (alpha R):Set (FreeAmalgam R)) :=
    (DistanceEight.U_le_Z R _).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R _ rfl))
  have hHC : ⁅P₀,P₀⁆≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) :=
    hmove.1.le.trans hspan.2.2.1
  have hHN : Q R (alpha R)≤normalizer ((⁅P₀,P₀⁆:Subgroup (FreeAmalgam R)):Set (FreeAmalgam R)) :=
    ((show Q R (alpha R)≤stabilizer R (alpha R) from fun _ hx => hx.1).trans
      (le_centralizer_iff.mp hHC)).trans (Subgroup.centralizer_le_normalizer _)
  have hUz (A : Subgroup (FreeAmalgam R)) (hA : A≤Q R (alpha R)) : ⁅U R (alpha R),A⁆≤⁅P₀,P₀⁆ := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr (hUC.trans (centralizer_le hA))]
    exact bot_le
  have hSS : ⁅U R (alpha R)⊔P₀,U R (alpha R)⊔P₀⁆≤⁅P₀,P₀⁆ := by
    apply commutator_sup_le_of_relative_normal (Q R (alpha R)) _ _ _ _ hHN hUQ hP₀Q
    · exact hUz _ (sup_le hUQ hP₀Q)
    · rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal (Q R (alpha R)) _ _ _ _
        hHN hUQ hP₀Q (hUz _ hP₀Q) le_rfl
  have he : ⁅C,C⁆=⁅P₀,P₀⁆ := le_antisymm
    ((commutator_mono hweak hweak).trans hSS) (commutator_mono hP₀C hP₀C)
  refine ⟨?_,he.le.trans hHC,?_⟩
  · rw [he]
    exact hmove.2
  ·
    rw [he,commutator_comm]
    apply le_trans (commutator_mono hweak le_rfl)
    apply commutator_sup_le_of_relative_normal (Q R (alpha R)) _ _ _ _ hHN hUQ hP₀Q
    · exact hUz _ inf_le_left
    · have hc : color R (p.walk.getVert 2)=false :=
        (p.vertex_color (by have hl:=p.length_eq_b; omega)).mpr (by decide)
      have hQT : Q R (alpha R)⊓Q R (p.walk.getVert 2)≤T₀ := by
        apply le_inf inf_le_left
        exact (inf_le_right.trans (le_centralizer_iff.mp
          (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R _ hc)))).trans
            (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z R _)))
      have hi := s.forward_moving_index_eq_two_of_distance_four h u hfull hb p
      have hs := s.critical_forward_span_commutator_le_line_of_two_lt h u hfull (by omega) p hi.le
      exact (((commutator_mono hP₀P hQT).trans hs.2).trans_eq hspan.1.symm).trans_eq hmove.1.symm

private theorem core_derived_bounds_of_central_supplement_at
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {a e : Vertex R}
    (p : CriticalPath R s.geometry a e)
    (hweak : ⁅Q R a,Ltilde R a⁆≤
      U R a⊔⁅localZSpan R (p.walk.getVert 2) a,Ltilde R a⁆) :
    let C := ⁅Q R a,Ltilde R a⁆
    Nat.card (⁅C,C⁆:Subgroup (FreeAmalgam R))=2 ∧
      ⁅C,C⁆≤centralizer (stabilizer R a:Set (FreeAmalgam R)) ∧
      ⁅Q R a⊓Q R (p.walk.getVert 2),C⁆≤⁅C,C⁆ := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R p.start_color
  have hbase : act R g⁻¹ (mVertex R g)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := s.core_derived_bounds_of_central_supplement h u hfull hsq hb
    (e:=act R g⁻¹ e)
  dsimp only [forwardMovedSpan] at base
  rw [←hbase] at base
  have hweak' : ⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆≤
      U R (act R g⁻¹ (mVertex R g))⊔
        ⁅localZSpan R ((p.act g⁻¹).walk.getVert 2) (act R g⁻¹ (mVertex R g)),
          Ltilde R (act R g⁻¹ (mVertex R g))⁆ := by
    change ⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆≤
      U R (act R g⁻¹ (mVertex R g))⊔
        ⁅localZSpan R ((actWalk R g⁻¹ p.walk).getVert 2) (act R g⁻¹ (mVertex R g)),
          Ltilde R (act R g⁻¹ (mVertex R g))⁆
    rw [actWalk_getVert,Q_act,Ltilde_act,U_act,
      LocalCommutator.CriticalCase.localZSpan_act,←map_commutator,←map_commutator,←Subgroup.map_sup]
    exact map_mono hweak
  obtain ⟨hcard,hcentral,hcross⟩ := base (p.act g⁻¹) hweak'
  have hrestore (v : Vertex R) : act R g (act R g⁻¹ v)=v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hcard' : Nat.card (⁅⁅Q R (mVertex R g),Ltilde R (mVertex R g)⁆,
      ⁅Q R (mVertex R g),Ltilde R (mVertex R g)⁆⁆:Subgroup (FreeAmalgam R))=2 := by
    rw [Q_act,Ltilde_act,←map_commutator,←map_commutator,
      card_map_of_injective (MulAut.conj _).injective] at hcard
    exact hcard
  have hcentral' := (map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hcentral).trans
    (map_centralizer_le_centralizer_image _ _)
  change (⁅⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆,
      ⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆⁆).map
      (MulAut.conj g⁻¹).toMonoidHom≤centralizer
        ((stabilizer R (act R g⁻¹ (mVertex R g))).map (MulAut.conj g⁻¹).toMonoidHom:Set (FreeAmalgam R)) at hcentral'
  rw [map_commutator,map_commutator,←Q_act,←Ltilde_act,←stabilizer_act,hrestore] at hcentral'
  have hcross' := map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hcross
  change (⁅Q R (act R g⁻¹ (mVertex R g))⊓Q R ((actWalk R g⁻¹ p.walk).getVert 2),
      ⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆⁆).map
      (MulAut.conj g⁻¹).toMonoidHom≤
      (⁅⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆,
        ⁅Q R (act R g⁻¹ (mVertex R g)),Ltilde R (act R g⁻¹ (mVertex R g))⁆⁆).map
        (MulAut.conj g⁻¹).toMonoidHom at hcross'
  rw [actWalk_getVert,map_commutator,map_commutator,
    Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,map_commutator,←Q_act,←Q_act,←Ltilde_act,
    hrestore,hrestore] at hcross'
  rw [map_commutator,←Q_act,←Ltilde_act,hrestore] at hcross'
  exact ⟨hcard',hcentral',hcross'⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem forward_span_terminal_false_of_derived_fixed
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hfixed : let P := localZSpan R (p.walk.getVert 2) (alpha R)
      ⁅P,P⁆≤centralizer (Ltilde R (p.walk.getVert 2):Set (FreeAmalgam R))) : False := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have ht : color R (p.walk.getVert 1)=true := by
    have hn := adjacent_color_ne R hat
    change false≠color R (p.walk.getVert 1) at hn
    cases hh:color R (p.walk.getVert 1) <;> simp_all
  have hTG : T₀≤stabilizer R (p.walk.getVert 2) :=
    (inf_le_left.trans (Q_le_adjacent_h R ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm R hct))
  have hHU : ⁅U R (p.walk.getVert 2),T₀⁆≤U R (p.walk.getVert 2) :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized _))
  have hd := s.forward_span_derived_eq_line h u hfull hb p
  have hDU : ⁅P,P⁆≤U R (p.walk.getVert 2) := hd.1.le.trans hHU
  have hzero : U R (p.walk.getVert 2)⊓centralizer
      (Ltilde R (p.walk.getVert 2):Set (FreeAmalgam R))=⊥ := by
    obtain ⟨g,hg⟩ := exists_mVertex_of_color R hc
    have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
      (s.movingLayer_inf_component_centralizer_eq_bot h)
    rw [←map_inf_centralizer_of_injective _ (MulAut.conj g⁻¹).injective,
      ←U_act,←Ltilde_act,Subgroup.map_bot] at hh
    rw [hg]
    simpa only [alpha,act_mVertex,one_mul] using hh
  have hz : ⁅P,P⁆=⊥ := le_bot_iff.mp ((le_inf hDU hfixed).trans_eq hzero)
  have hcard := hd.2.1
  change Nat.card (⁅P,P⁆:Subgroup (FreeAmalgam R))=2 at hcard
  rw [hz,card_bot] at hcard
  omega
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

private theorem terminal_false_of_opposite_core_supplement
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R=4) {e m : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (q : CriticalPath R s.geometry (p.walk.getVert 2) m)
    (_hq1 : q.walk.getVert 1=p.walk.getVert 1)
    (hq2 : q.walk.getVert 2=alpha R)
    (hweak : ⁅Q R (p.walk.getVert 2),Ltilde R (p.walk.getVert 2)⁆≤
      U R (p.walk.getVert 2)⊔⁅localZSpan R (alpha R) (p.walk.getVert 2),Ltilde R (p.walk.getVert 2)⁆) :
    False := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let D := P⊓Q R (p.walk.getVert 2)
  let C := ⁅Q R (p.walk.getVert 2),Ltilde R (p.walk.getVert 2)⁆
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hQa : Q R (p.walk.getVert 1)≤stabilizer R (alpha R) :=
    fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hQc : Q R (p.walk.getVert 1)≤stabilizer R (p.walk.getVert 2) :=
    fun _ hx => hx.2 _ (adjacent_symm R hct)
  have hPQ : P≤Q R (alpha R) :=
    (s.forward_span_le_hyperplane_kernel (by omega) p).trans inf_le_left
  have hder := s.forward_span_kernel_derived_eq h u hfull hb p
  have hspan := s.forward_span_derived_eq_line h u hfull hb p
  have hDcard : Nat.card (⁅D,D⁆:Subgroup (FreeAmalgam R))≤2 := by
    rw [hder,hspan.2.1]
  have hDC : ⁅D,D⁆≤centralizer (Q R (p.walk.getVert 1):Set (FreeAmalgam R)) :=
    (hder.le.trans hspan.2.2.1).trans (centralizer_le hQa)
  have hDN : Q R (p.walk.getVert 1)≤normalizer (D:Set (FreeAmalgam R)) :=
    (le_inf (hQa.trans (localZSpan_normalized R _ _))
      (hQc.trans (Q_normalized R _))).trans inf_normalizer_le_normalizer_inf
  have hbounds := s.core_derived_bounds_of_central_supplement_at h u hfull hsq hb q
  rw [hq2] at hbounds
  obtain ⟨hCcard,hCC,hcross⟩ := hbounds hweak
  have hcomm : ⁅D,C⁆≤⁅C,C⁆ :=
    (commutator_mono (le_inf inf_le_right (inf_le_left.trans hPQ)) le_rfl).trans hcross
  have hfixed := s.derived_fixed_of_two_central_lines_at u hfull hc hct D inf_le_right
    hDN hDcard hDC hCcard.le (hCC.trans (centralizer_le hQc)) hcomm
  rw [hder] at hfixed
  exact s.forward_span_terminal_false_of_derived_fixed h u hfull hb p hfixed

private theorem central_supplement_at_of_orbit
    (hb : s.geometry.b R=4)
    (hbase : ∀ {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e) (g : FreeAmalgam R),
      g∈stabilizer R (p.walk.getVert 2) → act R g (alpha R)=e →
      (B R (p.walk.getVert 2) (s.geometry.Z_normal _)).relIndex (U R e)≤2 →
      ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤
        U R (alpha R)⊔⁅localZSpan R (p.walk.getVert 2) (alpha R),Ltilde R (alpha R)⁆)
    {a e : Vertex R} (p : CriticalPath R s.geometry a e) (g : FreeAmalgam R)
    (hg : g∈stabilizer R (p.walk.getVert 2)) (he : act R g a=e)
    (hindex : (B R (p.walk.getVert 2) (s.geometry.Z_normal _)).relIndex (U R e)≤2) :
    ⁅Q R a,Ltilde R a⁆≤U R a⊔⁅localZSpan R (p.walk.getVert 2) a,Ltilde R a⁆ := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color R p.start_color
  have hxbase : act R x⁻¹ (mVertex R x)=alpha R := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := hbase (e:=act R x⁻¹ e)
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex R) : act R x (act R x⁻¹ v)=v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k∈stabilizer R ((p.act x⁻¹).walk.getVert 2) := by
    change k∈stabilizer R ((actWalk R x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act R k (act R x⁻¹ (mVertex R x))=act R x⁻¹ e := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color R (p.walk.getVert 2)=false :=
    (p.vertex_color (by have hl:=p.length_eq_b; omega)).mpr (by decide)
  have hki : (B R ((p.act x⁻¹).walk.getVert 2) (s.geometry.Z_normal _)).relIndex
      (U R (act R x⁻¹ e))≤2 := by
    change (B R ((actWalk R x⁻¹ p.walk).getVert 2) (s.geometry.Z_normal _)).relIndex
      (U R (act R x⁻¹ e))≤2
    rw [actWalk_getVert,Escape.PairingControl.FirstPairing.B_act (by omega : 2<s.geometry.b R) _ _ hci,
      U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hindex
  have hh := base (p.act x⁻¹) k hkg hke hki
  change ⁅Q R (act R x⁻¹ (mVertex R x)),Ltilde R (act R x⁻¹ (mVertex R x))⁆≤
    U R (act R x⁻¹ (mVertex R x))⊔⁅localZSpan R ((actWalk R x⁻¹ p.walk).getVert 2)
      (act R x⁻¹ (mVertex R x)),Ltilde R (act R x⁻¹ (mVertex R x))⁆ at hh
  rw [actWalk_getVert] at hh
  have hm := map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) hh
  simpa only [map_commutator,Subgroup.map_sup,←Q_act,←Ltilde_act,←U_act,
    ←LocalCommutator.CriticalCase.localZSpan_act,hrestore] using hm


private theorem criticalDistance_ne_four_of_orbit_supplement
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hsource : s.geometry.b R=4 →
      ∀ {e : Vertex R} (p : CriticalPath R s.geometry (alpha R) e) (g : FreeAmalgam R),
      g∈stabilizer R (p.walk.getVert 2) → act R g (alpha R)=e →
      (B R (p.walk.getVert 2) (s.geometry.Z_normal _)).relIndex (U R e)≤2 →
      ⁅Q R (alpha R),Ltilde R (alpha R)⁆≤
        U R (alpha R)⊔⁅localZSpan R (p.walk.getVert 2) (alpha R),Ltilde R (alpha R)⁆) :
    s.geometry.b R≠4 := by
  intro hb
  obtain ⟨e,⟨p⟩⟩ := CriticalPath.exists_from (R:=R) (geometry:=s.geometry) (a:=alpha R) rfl
  obtain ⟨m,g,q,hq1,hq2,hg,he,hindex⟩ := s.exists_opposite_critical_path_with_orbit h u hfull hb p
  have hweak := s.central_supplement_at_of_orbit hb (hsource hb) q g
    (by rwa [hq2]) he.symm (by rw [hq2]; exact hindex.le)
  rw [hq2] at hweak
  exact s.terminal_false_of_opposite_core_supplement h u hfull hsq hb p q hq1 hq2 hweak

/-- The full point-core symplectic source cannot have critical distance four. -/
theorem criticalDistance_ne_four
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hsq : IsSQTK KnownSimple.IsKnownSimple M) : s.geometry.b R≠4 := by
  apply s.criticalDistance_ne_four_of_orbit_supplement h u hfull hsq
  intro hb e p g hg he hindex
  exact s.core_commutator_le_moving_sup_forward_moved_span_of_orbit
    h u hfull hsq hb p g hg he hindex
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
