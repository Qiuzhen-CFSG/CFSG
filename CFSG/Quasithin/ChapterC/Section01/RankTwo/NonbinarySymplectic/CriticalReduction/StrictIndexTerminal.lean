module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexSaturation

/-!
# Vanishing of the complete terminal displacement

For the same escaping element in source (5.9)(*), a centralizer-conjugate
seed moving the penultimate layer would form a backward critical pair.
Reciprocal critical indices make its image equal to the full T₀-image.
Its displacement would therefore contain the escaping element inside the
penultimate radius, a contradiction. Thus the full orbit span lies in
the penultimate kernel.

The same argument applies to the actual endpoint intersection: any
nonzero displacement has index at least q and hence the same T₀-image.
It would again put that same element in the forbidden radius. The span
therefore centralizes both factors of the full terminal subgroup.
The actual two-step selector supplies every premise on its original
witnesses, including centralizer generation and endpoint movement.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9), first orbit span, printed p.920.
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

/-- A critical endpoint contained in T₀ has exactly its full seed displacement. -/
theorem Input.replacement_kernel_critical_seed_saturation
    {geometry : Geometry d.radical} {a c t v : Vertex d.radical}
    (back : CriticalPath d.radical geometry c v) (hb : 4 ≤ geometry.b d.radical)
    (ha : color d.radical a=false) (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (hVT : Z d.radical v ≤ kernelCentralizer geometry a c) :
    kernelCommutator geometry a c=⁅Z d.radical c,Z d.radical v⁆ := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    cases ht : color d.radical t <;> simp_all
  have hTS : kernelCentralizer geometry a c ≤ stabilizer d.radical c :=
    inf_le_left.trans ((Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hx => hx.2 c (adjacent_symm d.radical hct)))
  have hs := h.replacement_field_index_actor_saturates d geometry hb back.start_color
    (Z d.radical v) (kernelCentralizer geometry a c) hVT hTS
    ((kernelCentralizer_moving_index_le geometry a c).trans hsmall)
    (h.replacement_critical_indices_ge_field d back (by omega)).2
  exact (h.replacement_kernel_full_seed_commutator d geometry hb ha hat hct).symm.trans hs.2.symm

/-- Every centralizer-conjugate seed is trapped in the penultimate kernel; otherwise its displacement contains the same escaping element. -/
theorem Input.replacement_kernel_orbit_le_penultimate_kernel
    {geometry : Geometry d.radical} {a z c t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (hPT : Z d.radical (path.walk.getVert (path.walk.length-2)) ≤ kernelCentralizer geometry a c)
    (x : FreeAmalgam d.radical) (hx : x ∈ kernelCommutator geometry a c)
    (hescape : x ∉ V d.radical (path.walk.getVert (path.walk.length-2))) :
    let C₀ := stabilizer d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    let W := conjugateSpanBy (Z d.radical c) C₀
    W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      ⁅W,Z d.radical (path.walk.getVert (path.walk.length-2))⁆=⊥ := by
  dsimp only
  let p := path.walk.getVert (path.walk.length-2)
  let C₀ := stabilizer d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
  let W := conjugateSpanBy (Z d.radical c) C₀
  have hp : color d.radical p=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.length_eq_b]
      exact geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at he ⊢
    omega
  have hW : W ≤ Q d.radical p := by
    apply (closure_le _).mpr
    rintro _ ⟨k,hk,u,hu,rfl⟩
    let c' := act d.radical k⁻¹ c
    let t' := act d.radical k⁻¹ t
    have hkfix : act d.radical k⁻¹ a=a := (stabilizer d.radical a).inv_mem hk.1
    have hat' : Adjacent d.radical a t' := by
      have hh := (adjacent_act_iff d.radical k⁻¹ a t).mpr hat
      rwa [hkfix] at hh
    have hct' : Adjacent d.radical c' t' := (adjacent_act_iff d.radical k⁻¹ c t).mpr hct
    obtain ⟨hT,hH⟩ := h.replacement_kernel_conjugate_at_edge d geometry (by omega)
      path.start_color hat hct k⁻¹ ((stabilizer d.radical a).inv_mem hk.1)
    simp only [inv_inv] at hH
    have hx' : x ∈ kernelCommutator geometry a c' := by
      rw [hH]
      refine ⟨x,hx,?_⟩
      change k*x*k⁻¹=x
      rw [mem_centralizer_singleton_iff.mp hk.2,mul_inv_cancel_right]
    have hsmall' : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ≤ Nat.card F := by
      rw [movingIndex_act geometry (by omega) path.start_color k⁻¹
        ((stabilizer d.radical a).inv_mem hk.1)]
      exact hsmall
    have htrap : Z d.radical c' ≤ Q d.radical p := by
      by_contra hn
      obtain ⟨back,_,_⟩ := exists_backward_path_of_not_le geometry (by omega) path hat' hct' hn
      have he := h.replacement_kernel_critical_seed_saturation d back hb.le path.start_color
        hat' hct' hsmall' (by rw [hT]; exact hPT)
      rw [he] at hx'
      have hZp : ⁅Z d.radical c',Z d.radical p⁆ ≤ Z d.radical p :=
        le_normalizer_iff_commutator_le_right.mp
          ((Z_le_stabilizer_of_dist_le c' (geometry.exists_critical c' back.start_color)
            back.critical.1.le).trans (Z_normalized d.radical p))
      exact hescape (Z_le_VBall d.radical p 2 (hZp hx'))
    apply htrap
    rw [Z_act]
    exact ⟨u,hu,by simp only [inv_inv]; rfl⟩
  refine ⟨hW,commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  exact hW.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (geometry.centralizes p hp)))

/-- The complete orbit span centralizes both factors of the actual terminal subgroup. -/
theorem Input.replacement_kernel_orbit_terminal_centralizes
    {geometry : Geometry d.radical} {a z c t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (htail : Z d.radical (path.walk.getVert (path.walk.length-2)) ⊔
      (Z d.radical z ⊓ Q d.radical a) ≤ kernelCentralizer geometry a c)
    (x : FreeAmalgam d.radical) (hx : x ∈ kernelCommutator geometry a c)
    (hescape : x ∉ V d.radical (path.walk.getVert (path.walk.length-2))) :
    let C₀ := stabilizer d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    let W := conjugateSpanBy (Z d.radical c) C₀
    W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      ⁅W,Z d.radical (path.walk.getVert (path.walk.length-2)) ⊔
        (Z d.radical z ⊓ Q d.radical a)⁆=⊥ := by
  dsimp only
  let p := path.walk.getVert (path.walk.length-2)
  let C₀ := stabilizer d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
  let W := conjugateSpanBy (Z d.radical c) C₀
  let A := Z d.radical z ⊓ Q d.radical a
  obtain ⟨hWQ,hWP⟩ := h.replacement_kernel_orbit_le_penultimate_kernel d path hb hat hct hsmall
    (le_sup_left.trans htail) x hx hescape
  have hp : color d.radical p=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.length_eq_b]
      exact geometry.even (alpha d.radical) rfl
    rw [Nat.even_iff] at he ⊢
    omega
  have hpz : (cosetGraph d.radical).dist p z=2 := by
    rw [path.dist_end]
    have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
    omega
  have hWz : W ≤ stabilizer d.radical z := hWQ.trans
    (Q_le_stabilizer_of_dist_le_two p z hp path.end_color hpz.le)
  have hZzV : Z d.radical z ≤ V d.radical p := by
    apply le_iSup_of_le z
    apply le_iSup_of_le (show (cosetGraph d.radical).dist z p ≤ 2 from by
      rw [SimpleGraph.dist_comm,hpz])
    exact le_rfl
  have hWA : W ≤ centralizer (A : Set (FreeAmalgam d.radical)) := by
    apply (closure_le _).mpr
    rintro _ ⟨k,hk,u,hu,rfl⟩
    let c' := act d.radical k⁻¹ c
    let t' := act d.radical k⁻¹ t
    have hkfix : act d.radical k⁻¹ a=a := (stabilizer d.radical a).inv_mem hk.1
    have hat' : Adjacent d.radical a t' := by
      have hh := (adjacent_act_iff d.radical k⁻¹ a t).mpr hat
      rwa [hkfix] at hh
    have hct' : Adjacent d.radical c' t' := (adjacent_act_iff d.radical k⁻¹ c t).mpr hct
    have ht' : color d.radical t'=true := by
      have hh := adjacent_color_ne d.radical hat'
      rw [path.start_color] at hh
      cases ht' : color d.radical t' <;> simp_all
    have hc' : color d.radical c'=false := by
      have hh := adjacent_color_ne d.radical hct'
      rw [ht'] at hh
      cases hc' : color d.radical c' <;> simp_all
    obtain ⟨hT,hH⟩ := h.replacement_kernel_conjugate_at_edge d geometry (by omega)
      path.start_color hat hct k⁻¹ ((stabilizer d.radical a).inv_mem hk.1)
    simp only [inv_inv] at hH
    have hx' : x ∈ kernelCommutator geometry a c' := by
      rw [hH]
      refine ⟨x,hx,?_⟩
      change k*x*k⁻¹=x
      rw [mem_centralizer_singleton_iff.mp hk.2,mul_inv_cancel_right]
    have hsmall' : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ≤ Nat.card F := by
      rw [movingIndex_act geometry (by omega) path.start_color k⁻¹
        ((stabilizer d.radical a).inv_mem hk.1)]
      exact hsmall
    have hseed : Z d.radical c' ≤ W := by
      rw [Z_act]
      rintro _ ⟨v,hv,rfl⟩
      apply Subgroup.subset_closure
      exact ⟨k,hk,v,hv,by simp only [inv_inv]; rfl⟩
    have hTS : kernelCentralizer geometry a c' ≤ stabilizer d.radical c' :=
      inf_le_left.trans ((Q_le_adjacent_h d.radical ht' hat').trans
        (fun _ hv => hv.2 c' (adjacent_symm d.radical hct')))
    have hAT : A ≤ kernelCentralizer geometry a c' := by rw [hT]; exact le_sup_right.trans htail
    have hAS := hAT.trans hTS
    have hzero : ⁅Z d.radical c',A⁆=⊥ := by
      by_contra hn
      have hlo := h.replacement_critical_intersection_moving_index_lower d path hb.le
        (Z d.radical c') (hseed.trans hWz) hn
      have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) c' hc'
      have hidx : (centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).relIndex A=
          (Q d.radical c').relIndex A := by
        rw [←hC]
        change ((centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).subgroupOf A).index=
          ((stabilizer d.radical c' ⊓ centralizer (Z d.radical c' : Set (FreeAmalgam d.radical))).subgroupOf A).index
        congr 1
        ext v
        exact ⟨fun hv => ⟨hAS v.property,hv⟩,fun hv => hv.2⟩
      rw [hidx] at hlo
      have he := (h.replacement_field_index_actor_saturates d geometry hb.le hc' A
        (kernelCentralizer geometry a c') hAT hTS
        ((kernelCentralizer_moving_index_le geometry a c').trans hsmall') hlo).2
      rw [←h.replacement_kernel_full_seed_commutator d geometry hb.le path.start_color hat' hct',←he] at hx'
      have hcomm : ⁅Z d.radical c',A⁆ ≤ Z d.radical z := by
        rw [commutator_comm]
        exact (commutator_mono inf_le_left le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp ((hseed.trans hWz).trans (Z_normalized d.radical z)))
      exact hescape (hZzV (hcomm hx'))
    apply (commutator_eq_bot_iff_le_centralizer.mp hzero)
    rw [Z_act]
    exact ⟨u,hu,by simp only [inv_inv]; rfl⟩
  refine ⟨hWQ,commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  exact le_centralizer_iff.mpr (sup_le
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hWP))
    (le_centralizer_iff.mp hWA))

/-- The original two-step selector supplies terminal vanishing on the same conjugator, escaping element, full kernel and centralizer generation. -/
theorem Input.replacement_strict_index_noncentral_terminal
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hD : ¬ kernelCommutator geometry a (path.walk.getVert 2) ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    let c := path.walk.getVert 2
    let T₀ := kernelCentralizer geometry a c
    let p := path.walk.getVert (path.walk.length-2)
    let T := Z d.radical p ⊔ (Z d.radical z ⊓ Q d.radical a)
    stabilizer d.radical a ≤ normalizer (T₀ : Set _) ∧
      V d.radical a ≤ T₀ ∧ T ≤ T₀ ∧
      ∃ g ∈ stabilizer d.radical a, ∃ x ∈ kernelCommutator geometry a c,
        let c₁ := act d.radical g⁻¹ c
        let t₁ := act d.radical g⁻¹ (path.walk.getVert 1)
        let x₁ := g*x*g⁻¹
        let C₀ := stabilizer d.radical a ⊓ centralizer ({x₁} : Set (FreeAmalgam d.radical))
        let W := conjugateSpanBy (Z d.radical c₁) C₀
        Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
        kernelCentralizer geometry a c₁ = T₀ ∧
        (kernelCommutator geometry a c).map (MulAut.conj g).toMonoidHom =
          kernelCommutator geometry a c₁ ∧
        Z d.radical c₁ ≤ W ∧ W ≤ V d.radical a ∧
        Q d.radical a ≤ C₀ ∧ C₀ ≤ normalizer (W : Set _) ∧
        C₀ ⊔ Z d.radical z = stabilizer d.radical a ∧
        ⁅W,T₀⁆ = conjugateSpanBy (kernelCommutator geometry a c₁) C₀ ∧
        ⁅W,T₀⁆ ≤ Z d.radical a ∧ x₁ ∈ ⁅W,T₀⁆ ∧
        x₁ ∉ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        x₁ ∉ V d.radical p ∧
        W ≤ Q d.radical p ∧ ⁅W,T⁆ = ⊥ ∧ T < T₀ := by
  dsimp only
  obtain ⟨hn,hV,htail,g,hg,x,hx,hat₁,hct₁,hT₁,hHmap,hH₁,hxH,hgen,hm,hescape⟩ :=
    h.replacement_strict_index_noncentral_selection d path hb hsmall hD
  let c₁ := act d.radical g⁻¹ (path.walk.getVert 2)
  let x₁ := g*x*g⁻¹
  let C₀ := stabilizer d.radical a ⊓ centralizer ({x₁} : Set (FreeAmalgam d.radical))
  let W := conjugateSpanBy (Z d.radical c₁) C₀
  let T₀ := kernelCentralizer geometry a (path.walk.getVert 2)
  let T := Z d.radical (path.walk.getVert (path.walk.length-2)) ⊔ (Z d.radical z ⊓ Q d.radical a)
  have hx₁ : x₁ ∈ kernelCommutator geometry a c₁ := by
    change x₁ ∈ ⁅U d.radical c₁,kernelCentralizer geometry a c₁⁆
    rw [hT₁]
    exact hxH
  have hsmall₁ : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c₁) ≤ Nat.card F := by
    rw [movingIndex_act geometry (by omega) path.start_color g⁻¹ ((stabilizer d.radical a).inv_mem hg)]
    exact hsmall
  obtain ⟨hZW,hWV,hQC,hCN,he,hbound,hxW⟩ :=
    h.replacement_kernel_orbit_displacement d geometry hb path.start_color hat₁ hct₁ hsmall₁ x₁ hx₁
  rw [hT₁] at he hbound hxW
  have hmap : (kernelCommutator geometry a (path.walk.getVert 2)).map (MulAut.conj g).toMonoidHom =
      kernelCommutator geometry a c₁ := by
    change _ = ⁅U d.radical c₁,kernelCentralizer geometry a c₁⁆
    rwa [hT₁]
  obtain ⟨hWQ,hzero⟩ := h.replacement_kernel_orbit_terminal_centralizes d path hb hat₁ hct₁
    hsmall₁ (by rw [hT₁]; exact htail) x₁ hx₁ hescape
  change ⁅W,T⁆ = ⊥ at hzero
  have hTstrict : T < T₀ := lt_of_le_of_ne htail (by
    intro heq
    have hxzero : x₁ ∈ (⊥ : Subgroup (FreeAmalgam d.radical)) := by
      rw [←hzero,heq]
      exact hxW
    apply hm
    change x₁ ∈ _
    rw [mem_bot.mp hxzero]
    exact one_mem _)
  exact ⟨hn,hV,htail,g,hg,x,hx,hat₁,hct₁,hT₁,hmap,hZW,hWV,hQC,hCN,hgen,
    he,hbound,hxW,hm,hescape,hWQ,hzero,hTstrict⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
