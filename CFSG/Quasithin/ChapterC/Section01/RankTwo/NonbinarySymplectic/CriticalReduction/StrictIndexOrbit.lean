module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusImages
public import Theory.GroupTheory.Commutator.NormalSpan

/-!
# The literal first orbit span in the strict-index countercase

The edge decomposition of (5.3), applied to every incident edge, writes
the whole vertex Z-layer as U times its entire vertex-fixed subgroup.
Consequently its commutator with any local actor is the U-commutator;
no complement to the central attachment is chosen.

For the same escaping element selected in (5.9)(*), take the orbit span
of the full neighboring Z-layer under its centralizer. Relative normality
of the original T₀ identifies the span's T₀-displacement with the orbit
span of the whole H. This displacement lies in Z_alpha and contains the
escaping element. In contrast, the full terminal subgroup's displacement
lies in the penultimate radius and centralizes the critical endpoint.
It is therefore a proper subgroup of the T₀-displacement.

The source argument excluding this proper-displacement alternative, H <= D,
the central-H branch and the distance-two replacement remain to be proved.
In particular, the natural fixed-index bound is not used to discard any
central part of H or to assert displacement saturation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.3) and the first orbit span in (5.9), printed pp.915 and920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
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

/-- The whole Z-layer is the moving layer times its full vertex-fixed part.
The intersection of those factors is retained. -/
theorem Input.replacement_Z_eq_U_sup_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Z d.radical a = U d.radical a ⊔
      (Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  apply le_antisymm ?_ (sup_le (U_le_Z a) inf_le_left)
  conv_lhs => rw [Z,if_pos ha]
  apply iSup_le
  intro t
  apply iSup_le
  intro hat
  have ht : color d.radical t ≠ false := by
    simpa only [ha] using (adjacent_color_ne d.radical hat).symm
  simpa only [Z,if_neg ht] using
    h.replacement_edge_seed_le_U_sup_fixed d geometry hb ha hat

/-- Every local actor has exactly the same displacement on the whole Z-layer
as on U, even when their full central attachment is nontrivial. -/
theorem Input.replacement_Z_commutator_eq_U
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical a) :
    ⁅Z d.radical a,A⁆ = ⁅U d.radical a,A⁆ := by
  apply le_antisymm ?_ (commutator_mono (U_le_Z a) le_rfl)
  apply commutator_le.mpr
  intro z hz y hy
  let D := Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  have hD : D ≤ normalizer (U d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans (Z_le_stabilizer d.radical a)).trans (U_normalized a)
  have hzprod : z ∈ (U d.radical a : Set (FreeAmalgam d.radical)) * (D : Set _) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hD]
    exact h.replacement_Z_eq_U_sup_fixed d geometry hb ha ▸ hz
  obtain ⟨u,hu,c,hc,rfl⟩ := hzprod
  have hcy : ⁅c,y⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 y (hA hy)).symm
  simpa only [commutatorElement_mul_left_eq_conj_mul,hcy,mul_one,mul_inv_cancel,one_mul]
    using commutator_mem_commutator hu hy

/-- Source (5.9)'s literal H is also the displacement of the full neighboring
Z-layer under the same centralizer T₀. -/
theorem Input.replacement_kernel_full_seed_commutator
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a c t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    ⁅Z d.radical c,kernelCentralizer geometry a c⁆ = kernelCommutator geometry a c := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    cases ht : color d.radical t <;> simp_all
  have hc : color d.radical c=false := by
    have hh := adjacent_color_ne d.radical hct
    cases hc : color d.radical c <;> simp_all
  exact h.replacement_Z_commutator_eq_U d geometry hb hc _
    (inf_le_left.trans ((Q_le_adjacent_h d.radical ht hat).trans
      (fun _ hx => hx.2 c (adjacent_symm d.radical hct))))

/-- The full first orbit span is contained in the radius, normalized by the
element's local centralizer, and has precisely the orbit span of H as its
T₀-displacement. This displacement contains the original chosen element. -/
theorem Input.replacement_kernel_orbit_displacement
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a c t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (x : FreeAmalgam d.radical) (hx : x ∈ kernelCommutator geometry a c) :
    let C₀ := stabilizer d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
    let W := conjugateSpanBy (Z d.radical c) C₀
    Z d.radical c ≤ W ∧ W ≤ V d.radical a ∧
      Q d.radical a ≤ C₀ ∧ C₀ ≤ normalizer (W : Set _) ∧
      ⁅W,kernelCentralizer geometry a c⁆ =
        conjugateSpanBy (kernelCommutator geometry a c) C₀ ∧
      ⁅W,kernelCentralizer geometry a c⁆ ≤ Z d.radical a ∧
      x ∈ ⁅W,kernelCentralizer geometry a c⁆ := by
  dsimp only
  let C₀ := stabilizer d.radical a ⊓ centralizer ({x} : Set (FreeAmalgam d.radical))
  let W := conjugateSpanBy (Z d.radical c) C₀
  have hH := h.replacement_field_index_kernel_commutator_le_edge_seed d geometry hb.le ha hat hct hsmall
  have hxZa := adjacent_Z_le d.radical ha hat (hH hx)
  have hQC : Q d.radical a ≤ C₀ := by
    intro q hq
    refine ⟨hq.1,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)) hxZa q hq
  have hZV : Z d.radical c ≤ V d.radical a := le_sup_left.trans (neighbor_seed_join_le_radius hat hct)
  have hZC : Z d.radical c ≤ C₀ := hZV.trans ((geometry.V_le_Q (by omega) a ha).trans hQC)
  have hCT : C₀ ≤ normalizer (kernelCentralizer geometry a c : Set _) :=
    inf_le_left.trans (kernelCentralizer_normalized_at_edge geometry (by omega)
      (h.replacement_residual_edge_generation d) ha hat hct)
  have he : ⁅W,kernelCentralizer geometry a c⁆ =
      conjugateSpanBy (kernelCommutator geometry a c) C₀ := by
    rw [commutator_conjugateSpanBy_of_normalized_right _ _ _ hZC hCT,
      h.replacement_kernel_full_seed_commutator d geometry hb.le ha hat hct]
  have hbound : ⁅W,kernelCentralizer geometry a c⁆ ≤ Z d.radical a := by
    rw [he]
    exact conjugateSpanBy_le (hH.trans (adjacent_Z_le d.radical ha hat))
      (inf_le_left.trans (Z_normalized d.radical a))
  refine ⟨le_conjugateSpanBy _ _,
    conjugateSpanBy_le hZV (inf_le_left.trans (DistanceEight.V_normalized d.radical a)),
    hQC,le_normalizer_conjugateSpanBy _ _,he,hbound,?_⟩
  rw [he]
  exact le_conjugateSpanBy _ _ hx

omit h [Finite H] in
private theorem radius_terminal_commutator
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (W : Subgroup (FreeAmalgam d.radical)) (hW : W ≤ V d.radical a) :
    let p := path.walk.getVert (path.walk.length-2)
    let T := Z d.radical p ⊔ (Z d.radical z ⊓ Q d.radical a)
    ⁅W,T⁆ ≤ V d.radical p ∧
      ⁅W,T⁆ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let p := path.walk.getVert (path.walk.length-2)
  have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
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
  have hWS : W ≤ stabilizer d.radical p := hW.trans
    (CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.radius_le_stabilizer_of_distance
      d.radical geometry path.start_color (by
      dsimp only [p]
      rw [path.dist_start (Nat.sub_le _ _),path.length_eq_b]
      omega))
  have hTV : Z d.radical p ⊔ (Z d.radical z ⊓ Q d.radical a) ≤ V d.radical p := by
    refine sup_le (Z_le_VBall d.radical p 2) (inf_le_left.trans ?_)
    apply le_iSup_of_le z
    apply le_iSup_of_le (show (cosetGraph d.radical).dist z p ≤ 2 from by
      rw [SimpleGraph.dist_comm,hpz])
    exact le_rfl
  have hcomm : ⁅W,Z d.radical p ⊔ (Z d.radical z ⊓ Q d.radical a)⁆ ≤ V d.radical p := by
    rw [commutator_comm]
    exact (commutator_mono hTV le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hWS.trans (DistanceEight.V_normalized d.radical p)))
  have hVQ : V d.radical p ≤ Q d.radical z := by
    apply V_le_Q_of_dist_add_two_lt d.radical hp
    rw [hpz]
    exact hb
  exact ⟨hcomm,hcomm.trans (hVQ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))⟩

/-- The actual two-step source application: the same selection generates
the vertex and yields the literal full-Z orbit span. Its entire terminal
displacement centralizes the endpoint and is strictly smaller than its
T₀-displacement. All quotient kernels and central attachments remain. -/
theorem Input.replacement_strict_index_noncentral_orbit
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
        ⁅W,T⁆ ≤ Z d.radical a ⊓ V d.radical p ∧
        ⁅W,T⁆ ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
        ⁅W,T⁆ < ⁅W,T₀⁆ ∧ T < T₀ := by
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
  obtain ⟨hterminal,hterminalC⟩ := radius_terminal_commutator d path hb W hWV
  have hle : ⁅W,T⁆ ≤ ⁅W,T₀⁆ := commutator_mono le_rfl htail
  have hstrict : ⁅W,T⁆ < ⁅W,T₀⁆ := lt_of_le_of_ne hle (by
    intro heq
    exact hm (hterminalC (heq ▸ hxW)))
  have hTstrict : T < T₀ := lt_of_le_of_ne htail (by
    intro heq
    exact (ne_of_lt hstrict) (congrArg (fun A => ⁅W,A⁆) heq))
  exact ⟨hn,hV,htail,g,hg,x,hx,hat₁,hct₁,hT₁,hmap,hZW,hWV,hQC,hCN,hgen,
    he,hbound,hxW,hm,hescape,le_inf (hle.trans hbound) hterminal,hterminalC,hstrict,hTstrict⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
