module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexShift

/-!
# The two complete orbit spans in the central strict-index branch

Keep the original source conjugator y and H₂ = H^y. If H₂ moves the
endpoint radius, the shifted-pair exclusion puts the endpoint seed in
Q_mu. An escaping seed of V = <Z_c^(G_mu)> would then be critical with
the penultimate vertex. Equality of the full quotient images identifies
its displacement with H₂ and forces H₂ to centralize the endpoint radius.
Thus V lies in the penultimate kernel. Natural fixed-index saturation
then makes V centralize the entire endpoint seed, giving V <= Q_endpoint.

Every element of C_(G_c)(H₂) leaves H₂ unchanged. Applying the same
argument to y times that element puts both literal second spans
Z = <Z_mu^(C_(G_c)(H₂))> and W = <V^(C_(G_c)(H₂))> in the endpoint
kernel, with all central attachments and original quotient kernels kept.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9), printed pp.920--921, through the placement of Z and W.
The selection in (**), its generation clause, the following displacement
comparison, strict-index and terminal exclusions, and the distance-two
replacement remain required. The movement hypothesis belongs to that
same source selector; no distance-two conclusion is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem central_seed_span_endpoint
    {geometry : Geometry d.radical} {a z mu c t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hmu : color d.radical mu=false)
    (hmut : Adjacent d.radical mu t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical mu (geometry.Z_normal mu)).relIndex (U d.radical c) ≤ Nat.card F)
    (hdmu : (cosetGraph d.radical).dist mu
      (path.walk.getVert (path.walk.length-2)) ≤ geometry.b d.radical-2)
    (hpT : Z d.radical (path.walk.getVert (path.walk.length-2)) ≤ kernelCentralizer geometry mu c)
    (hzT : Z d.radical z ≤ kernelCentralizer geometry mu c)
    (hcentral : kernelCommutator geometry mu c ≤
      centralizer (stabilizer d.radical mu : Set (FreeAmalgam d.radical)))
    (hmove : ¬ kernelCommutator geometry mu c ≤
      centralizer (V d.radical z : Set (FreeAmalgam d.radical))) :
    sourceSeedSpan d.radical c mu ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      sourceSeedSpan d.radical c mu ≤ Q d.radical z := by
  let p := path.walk.getVert (path.walk.length-2)
  let W := sourceSeedSpan d.radical c mu
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; omega
  have hp : color d.radical p=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.length_eq_b]
      exact geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at he ⊢
    omega
  have hpz : (cosetGraph d.radical).dist p z=2 := by
    rw [path.dist_end]
    omega
  have hZpC : Z d.radical p ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) := by
    apply (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p hp)).trans
    apply centralizer_le
    apply V_le_Q_of_dist_add_two_lt d.radical path.end_color
    rw [SimpleGraph.dist_comm,hpz]
    exact hb
  have hZzC : Z d.radical z ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)).trans
      (centralizer_le (geometry.V_le_Q (by omega) z path.end_color))
  have hlocal (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical mu) :
      let c' := act d.radical k⁻¹ c
      let t' := act d.radical k⁻¹ t
      Adjacent d.radical mu t' ∧ Adjacent d.radical c' t' ∧
      color d.radical c'=false ∧
      kernelCentralizer geometry mu c'=kernelCentralizer geometry mu c ∧
      kernelCommutator geometry mu c'=kernelCommutator geometry mu c ∧
      (B d.radical mu (geometry.Z_normal mu)).relIndex (U d.radical c') ≤ Nat.card F := by
    dsimp only
    have hki := (stabilizer d.radical mu).inv_mem hk
    have hfix : act d.radical k⁻¹ mu=mu := hki
    have hm : Adjacent d.radical mu (act d.radical k⁻¹ t) := by
      have hh := (adjacent_act_iff d.radical k⁻¹ _ _).mpr hmut
      rwa [hfix] at hh
    have hc' := (adjacent_act_iff d.radical k⁻¹ _ _).mpr hct
    have hcol : color d.radical (act d.radical k⁻¹ c)=false := by
      have h₁ := adjacent_color_ne d.radical hm
      have h₂ := adjacent_color_ne d.radical hc'
      rw [hmu] at h₁
      cases hc : color d.radical (act d.radical k⁻¹ c) <;>
        cases ht : color d.radical (act d.radical k⁻¹ t) <;> simp_all
    obtain ⟨hT,hH⟩ := h.replacement_kernel_conjugate_at_edge d geometry (by omega)
      hmu hmut hct k⁻¹ hki
    have hn := (le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _)
    simp only [inv_inv] at hH
    rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hn hk)] at hH
    refine ⟨hm,hc',hcol,hT,hH,?_⟩
    rw [movingIndex_act geometry (by omega) hmu k⁻¹ hki]
    exact hsmall
  have hWQ : W ≤ Q d.radical p := by
    apply (closure_le _).mpr
    rintro _ ⟨k,hk,u,hu,rfl⟩
    obtain ⟨hm,hc',hcol,hT,hH,hsmall'⟩ := hlocal k hk
    let c' := act d.radical k⁻¹ c
    have htrap : Z d.radical c' ≤ Q d.radical p := by
      by_contra hn
      have hmin := criticalDistance_le d.radical c' (geometry.exists_critical c' hcol) hn
      have hdc := neighbor_distance_le_two hm hc'
      have htri := (cosetGraph_connected d.radical).dist_triangle (u := c') (v := mu) (w := p)
      have hpair : CriticalPair d.radical c' p (geometry.exists_critical c' hcol) := by
        refine ⟨?_,hn⟩
        rw [geometry.distance_constant c' hcol] at hmin ⊢
        change geometry.b d.radical ≤ _ at hmin
        change _=geometry.b d.radical
        apply le_antisymm ?_ hmin
        calc
          (cosetGraph d.radical).dist c' p ≤ _ := htri
          _ ≤ 2+(geometry.b d.radical-2) := Nat.add_le_add hdc hdmu
          _ = geometry.b d.radical := by omega
      let back := CriticalPath.ofPair (geometry := geometry) hcol hpair
      have he := h.replacement_kernel_critical_seed_saturation d back hb.le hmu hm hc'
        hsmall' (by rw [hT]; exact hpT)
      rw [hH] at he
      apply hmove
      rw [he]
      exact (le_normalizer_iff_commutator_le_right.mp
        ((Z_le_stabilizer_of_dist_le c' (geometry.exists_critical c' hcol)
          hpair.1.le).trans (Z_normalized d.radical p))).trans hZpC
    apply htrap
    rw [Z_act]
    exact ⟨u,hu,by simp only [inv_inv]; rfl⟩
  have hWz : W ≤ stabilizer d.radical z := hWQ.trans
    (Q_le_stabilizer_of_dist_le_two p z hp path.end_color hpz.le)
  have hWfix : W ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
    apply (closure_le _).mpr
    rintro _ ⟨k,hk,u,hu,rfl⟩
    obtain ⟨hm,hc',hcol,hT,hH,hsmall'⟩ := hlocal k hk
    let c' := act d.radical k⁻¹ c
    have hseed : Z d.radical c' ≤ W := by
      rw [Z_act]
      rintro _ ⟨v,hv,rfl⟩
      apply Subgroup.subset_closure
      exact ⟨k,hk,v,hv,by simp only [inv_inv]; rfl⟩
    have ht' : color d.radical (act d.radical k⁻¹ t)=true := by
      have hh := adjacent_color_ne d.radical hm
      rw [hmu] at hh
      cases ht : color d.radical (act d.radical k⁻¹ t) <;> simp_all
    have hTS : kernelCentralizer geometry mu c' ≤ stabilizer d.radical c' :=
      inf_le_left.trans ((Q_le_adjacent_h d.radical ht' hm).trans
        (fun _ hv => hv.2 c' (adjacent_symm d.radical hc')))
    have hZT : Z d.radical z ≤ kernelCentralizer geometry mu c' := by rw [hT]; exact hzT
    have hZS := hZT.trans hTS
    have hzero : ⁅Z d.radical c',Z d.radical z⁆=⊥ := by
      by_contra hn
      have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))=⊤ := by
        apply eq_top_iff.mpr
        intro x _ v hv
        have hv1 : v=1 := mem_bot.mp hv
        simp only [hv1,one_mul,mul_one]
      have hlo := h.replacement_fixed_Z_moving_index_lower d geometry hb.le path.end_color
        (Z d.radical c') ⊥ (hseed.trans hWz) bot_le (by rwa [hbot,inf_top_eq])
      rw [hbot,inf_top_eq] at hlo
      have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c' hcol
      have hidx : (centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).relIndex (Z d.radical z)=
          (Q d.radical c').relIndex (Z d.radical z) := by
        rw [←hC]
        change ((centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical z)).index=
          ((stabilizer d.radical c' ⊓ centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical z)).index
        congr 1
        ext v
        exact ⟨fun hv => ⟨hZS v.property,hv⟩,fun hv => hv.2⟩
      rw [hidx] at hlo
      have he := (h.replacement_field_index_actor_saturates d geometry hb.le hcol
        (Z d.radical z) (kernelCentralizer geometry mu c') hZT hTS
        ((kernelCentralizer_moving_index_le geometry mu c').trans hsmall') hlo).2
      rw [h.replacement_kernel_full_seed_commutator d geometry hb.le hmu hm hc',hH] at he
      apply hmove
      rw [←he]
      exact (le_normalizer_iff_commutator_le_right.mp
        ((hseed.trans hWz).trans (Z_normalized d.radical z))).trans hZzC
    apply commutator_eq_bot_iff_le_centralizer.mp hzero
    rw [Z_act]
    exact ⟨u,hu,by simp only [inv_inv]; rfl⟩
  refine ⟨hWQ,?_⟩
  rw [←MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color]
  exact le_inf hWz hWfix


/-- For the same source y, the complete first orbit lies in both terminal
kernels. Its displacement is not replaced by a central quotient. -/
theorem Input.replacement_strict_index_conjugated_span_endpoint
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (path.walk.getVert 2))
    (hmove : ¬ conjugatedKernelCommutator geometry a (path.walk.getVert 2) y ≤
      centralizer (V d.radical z : Set (FreeAmalgam d.radical))) :
    sourceSeedSpan d.radical (path.walk.getVert 2) (act d.radical y a) ≤
      Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
    sourceSeedSpan d.radical (path.walk.getVert 2) (act d.radical y a) ≤ Q d.radical z := by
  let c := path.walk.getVert 2
  let p := path.walk.getVert (path.walk.length-2)
  let mu := act d.radical y a
  let t := act d.radical y (path.walk.getVert 1)
  have hyfix : act d.radical y c=c := hy
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; omega
  have hmu : color d.radical mu=false := by rw [action_preserves_color]; exact path.start_color
  have hc : color d.radical c=false := (path.vertex_color (by omega : 2 ≤ path.walk.length)).mpr (by decide)
  have hp : color d.radical p=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.length_eq_b]
      exact geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at he ⊢
    omega
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical c (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hmut : Adjacent d.radical mu t := (adjacent_act_iff d.radical y _ _).mpr hat
  have hct' : Adjacent d.radical c t := by
    have hh := (adjacent_act_iff d.radical y _ _).mpr hct
    rwa [hyfix] at hh
  have hsmall' : (B d.radical mu (geometry.Z_normal mu)).relIndex (U d.radical c) ≤ Nat.card F := by
    rw [Escape.PairingControl.FirstPairing.B_act (by omega) y a path.start_color,
      ←hyfix,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hsmall
  have hcp : (cosetGraph d.radical).dist c p ≤ path.walk.length-4 := by
    have hh := SimpleGraph.dist_le ((path.walk.drop 2).take (path.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_getVert,
      show 2+(path.walk.length-4)=path.walk.length-2 by omega] at hh
    exact hh.trans (min_le_left _ _)
  have hmup : (cosetGraph d.radical).dist mu p ≤ geometry.b d.radical-2 := by
    have hdc : (cosetGraph d.radical).dist mu c ≤ 2 := by
      rw [SimpleGraph.dist_comm]
      exact neighbor_distance_le_two hmut hct'
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := mu) (v := c) (w := p)
    have he := path.length_eq_b
    omega
  have hpQ : Z d.radical p ≤ Q d.radical mu := by
    apply Z_le_Q_of_dist_lt d.radical p (geometry.exists_critical p hp)
    rw [geometry.distance_constant p hp,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist mu p < geometry.b d.radical
    omega
  have hpQc : Z d.radical p ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical p (geometry.exists_critical p hp)
    rw [geometry.distance_constant p hp,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist c p < geometry.b d.radical
    have he := path.length_eq_b
    omega
  have hzQc : Z d.radical z ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end]
    change path.walk.length-2 < geometry.b d.radical
    have he := path.length_eq_b
    omega
  have hzQ := (h.replacement_strict_index_shifted_critical_exclusion d path hb hsmall y hy hmove).2
  have hQC : Q d.radical c ≤ centralizer
      ((U d.radical c ⊓ B d.radical mu (geometry.Z_normal mu) : Subgroup _) : Set _) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc))).trans
      (centralizer_le (inf_le_left.trans (U_le_Z c)))
  obtain ⟨_,hH,_,_,_,_,_,_,_,hcent⟩ :=
    h.replacement_strict_index_conjugated_span d path hb hsmall y hy
  exact central_seed_span_endpoint h d path hb hmu hmut hct' hsmall' hmup
    (le_inf hpQ (hpQc.trans hQC)) (le_inf hzQ (hzQc.trans hQC))
    (by rw [hH]; exact hcent) (by rw [hH]; exact hmove)

/-- Both original source spans, under the full centralizer of the same H₂,
lie in the original endpoint kernel. The first span contains the entire
conjugated starting seed, so the smaller second orbit is retained too. -/
theorem Input.replacement_strict_index_second_spans_endpoint
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical (path.walk.getVert 2))
    (hmove : ¬ conjugatedKernelCommutator geometry a (path.walk.getVert 2) y ≤
      centralizer (V d.radical z : Set (FreeAmalgam d.radical))) :
    let c := path.walk.getVert 2
    let mu := act d.radical y a
    let H₂ := conjugatedKernelCommutator geometry a c y
    let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
    let Z₀ := conjugateSpanBy (Z d.radical mu) C₀
    let W := sourceCentralizerSpan d.radical c mu H₂
    Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      W ≤ Q d.radical z := by
  dsimp only
  let c := path.walk.getVert 2
  let H₂ := conjugatedKernelCommutator geometry a c y
  let C₀ := stabilizer d.radical c ⊓ centralizer (H₂ : Set (FreeAmalgam d.radical))
  have hZmu := (h.replacement_strict_index_conjugated_span d path hb hsmall y hy).2.2.2.1
  have hc : color d.radical c=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist c (act d.radical y a) ≤ 2 := by
    have hh := dist_act d.radical y c a
    rw [show act d.radical y c=c from hy] at hh
    calc
      (cosetGraph d.radical).dist c (act d.radical y a) =
          (cosetGraph d.radical).dist c a := hh
      _ = 2 := by rw [SimpleGraph.dist_comm]; exact path.dist_start (by rw [path.length_eq_b]; omega)
      _ ≤ 2 := le_rfl
  refine ⟨conjugateSpanBy_mono hZmu le_rfl,
    sourceCentralizerSpan_le_Q geometry hb hc hd H₂,?_⟩
  have hconj (g : FreeAmalgam d.radical) (hg : g ∈ C₀) :
      (sourceSeedSpan d.radical c (act d.radical y a)).map (MulAut.conj g).toMonoidHom ≤
        Q d.radical (path.walk.getVert (path.walk.length-2)) ⊓ Q d.radical z := by
    have hginv := (stabilizer d.radical c).inv_mem hg.1
    have hyg : y*g⁻¹ ∈ stabilizer d.radical c := (stabilizer d.radical c).mul_mem hy hginv
    have hH : conjugatedKernelCommutator geometry a c (y*g⁻¹)=H₂ := by
      change (kernelCommutator geometry a c).map (MulAut.conj (y*g⁻¹)⁻¹).toMonoidHom=H₂
      have he : (MulAut.conj (y*g⁻¹)⁻¹).toMonoidHom=
          (MulAut.conj g).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change (y*g⁻¹)⁻¹*x*((y*g⁻¹)⁻¹)⁻¹=g*(y⁻¹*x*(y⁻¹)⁻¹)*g⁻¹
        group
      rw [he,←map_map]
      exact mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) hg.2)
    have hmap : (sourceSeedSpan d.radical c (act d.radical y a)).map (MulAut.conj g).toMonoidHom=
        sourceSeedSpan d.radical c (act d.radical (y*g⁻¹) a) := by
      change (conjugateSpanBy _ _).map _=conjugateSpanBy _ _
      rw [map_conjugateSpanBy]
      have hcfix : act d.radical g⁻¹ c=c := hginv
      have hZ := Z_act d.radical g⁻¹ c
      have hS := stabilizer_act d.radical g⁻¹ (act d.radical y a)
      simp only [inv_inv,hcfix,←act_mul] at hZ hS
      rw [←hZ,←hS]
    rw [hmap]
    obtain ⟨hp,hz⟩ := h.replacement_strict_index_conjugated_span_endpoint d path hb hsmall
      (y*g⁻¹) hyg (by rw [hH]; exact hmove)
    exact le_inf hp hz
  have hW : sourceCentralizerSpan d.radical c (act d.radical y a) H₂ ≤
      Q d.radical (path.walk.getVert (path.walk.length-2)) ⊓ Q d.radical z := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    exact hconj g hg (mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
  exact ⟨hW.trans inf_le_left,hW.trans inf_le_right⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
