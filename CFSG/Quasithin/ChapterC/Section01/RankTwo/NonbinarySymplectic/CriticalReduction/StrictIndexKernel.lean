module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.QuadraticIndex
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Kernel
public import Theory.Representation.SymplecticFourOrthogonalCover.RootNormalizerFixed
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# The literal centralizer kernel in the nonbinary strict-index argument

A fixed index at most q on the full U-layer bounds the natural displacement
by a line. Fixed-vector lifting through the complete central cover then
makes every normalizing two-group centralize the whole displacement.
Applied to T₀ = C_Qa(U_c intersect B_a), this proves [U_c,T₀] <= Z_t.

The centralizer definition gives exactly the same T₀ at both selected
vertices c₁ = c^(v inverse) and c₂ = c₁^(x inverse). Their entire
commutators are transported through the original conjugation maps. On the
literal critical path, T₀ contains V_a and the complete terminal subgroup
Z_(z-2) joined with (Z_z intersect Q_a); the transported H lies in Z_c.

If H is noncentral at a, the original simple quotient supplies a conjugate
of an element of H that moves the critical endpoint and escapes its
penultimate radius. This retains the original T₀ and the full central
attachment. The simultaneous centralizer-generation clause in (*) remains
required; neither H <= D_a nor the strict moving-index inequality is asserted.

Source: Meierfrankenfeld--Stellmacher, "Pushing up weak BN-pairs of rank two"
(1993), (5.9), printed p.920. This T₀ is the centralizer used in (5.9),
not the intersection of smaller movers used earlier in (5.5).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
open Representation.SymplecticFourOrthogonalCover
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit

private theorem displacement_finrank_le_one_of_cover_index
    {E W : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (A : Subgroup (L (K := E)))
    (hsmall : 2 ^ fixedCodim σ A ≤ Nat.card E) :
    Module.finrank E (displacementSpace (A.map (commutator (Sp E)).subtype)) ≤ 1 := by
  let ed : L (K := E) →* Sp E := (commutator (Sp E)).subtype
  rw [fixedCodim_of_binaryCover p hp] at hsmall
  have hfixed : fixedSpace (binaryNatural (K := E)) A =
      (TwoLocalCover.fixedSpace (A.map ed)).restrictScalars (ZMod 2) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨y,hy,rfl⟩ := hx
      exact hv ⟨y,hy⟩
    · intro hv x
      exact hv (ed x.val) (mem_map_of_mem ed x.property)
  have hi : 2 ^ fixedCodim (binaryNatural (K := E)) A =
      Nat.card (Vector E ⧸ TwoLocalCover.fixedSpace (A.map ed)) := by
    change 2 ^ Module.finrank (ZMod 2) (Vector E ⧸ fixedSpace (binaryNatural (K := E)) A) = _
    rw [hfixed]
    have hc := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (TwoLocalCover.fixedSpace (A.map ed))).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
    exact hc
  rw [hi,fixed_quotient_card] at hsmall
  have hq : 1 < Nat.card E := Finite.one_lt_card
  have hh : Nat.card E ^ Module.finrank E (displacementSpace (A.map ed)) ≤
      Nat.card E ^ 1 := by simpa only [pow_one] using hsmall
  exact (Nat.pow_le_pow_iff_right hq).mp hh

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A normalizing two-group fixes the entire covered displacement of any
actor with full-U fixed index at most the original field order. -/
theorem Input.replacement_two_normalizer_centralizes_field_displacement
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    (T P : Subgroup (FreeAmalgam d.radical))
    (hTS : T ≤ stabilizer d.radical a) (hPS : P ≤ stabilizer d.radical a)
    (hP : IsPGroup 2 P) (hn : P ≤ normalizer (T : Set _))
    (hsmall : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F) :
    P ≤ centralizer ((⁅U d.radical a,T⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C = ⊤ := by
    have hpre : C.comap q = ⊤ := by
      rw [show C = (K.subgroupOf d.overgroup).map q from rfl,
        comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hpre]
    rw [←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := T.subgroupOf S
  let P₀ := P.subgroupOf S
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjS : Function.Injective jS := fun v w hvw => hj (congrArg Subtype.val hvw)
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  let σ := MovedSection.coverAction s e
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (σ (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hi := embedded_centralizer_index σ U₀ T₀ jS hjS hjSr
    (γ.comp T₀.subtype) (fun x w => haction x.val w)
  rw [MonoidHom.range_comp,range_subtype] at hi
  have hbound : (centralizer (T₀ : Set S)).relIndex U₀ ≤ Nat.card E.Carrier := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS,E.card_eq,hE,←h.field_card]
    exact hsmall
  have hdim := displacement_finrank_le_one_of_cover_index σ
    (MovedSection.coverProjection s e) he (T₀.map γ) (hi ▸ hbound)
  have hn₀ : P₀ ≤ normalizer (T₀ : Set S) :=
    (comap_mono hn).trans (le_normalizer_comap S.subtype)
  have hfixed := embedded_two_normalizer_centralizes_displacement U₀ T₀ P₀
    hP.comap_subtype hn₀ (MovedSection.coverProjection s e) he jS hjSr γ haction hdim
  have hm := (map_mono (f := S.subtype) hfixed).trans
    (map_centralizer_le_centralizer_image _ S.subtype)
  rw [map_subgroupOf_eq_of_le hPS,←Subgroup.coe_map,map_commutator,
    map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS] at hm
  exact hm

/-- The literal strict-index centralizer has its whole displacement in the
common edge seed, with no assumption that the U-cover is split. -/
theorem Input.replacement_field_index_kernel_commutator_le_edge_seed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F) :
    kernelCommutator geometry a c ≤ Z d.radical t := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    cases ht : color d.radical t <;> simp_all
  have hc : color d.radical c=false := by
    have hh := adjacent_color_ne d.radical hct
    cases hc : color d.radical c <;> simp_all
  have hTS : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hTc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 c (adjacent_symm d.radical hct)
  have hQaT : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hn := kernelCentralizer_normalized_at_edge geometry (by omega)
    (h.replacement_residual_edge_generation d) ha hat hct
  have hfix := h.replacement_two_normalizer_centralizes_field_displacement d geometry hb hc
    (kernelCentralizer geometry a c) (Q d.radical t)
    ((show kernelCentralizer geometry a c ≤ Q d.radical a from inf_le_left).trans (hQaT.trans hTc))
    hTc (by
      obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
        (h.replacement_two_group d) (h.replacement_core_le d) ha hat
      rw [←hjR]
      exact (h.replacement_two_group d).map j)
    (hTS.trans hn) ((kernelCentralizer_moving_index_le geometry a c).trans hsmall)
  have hHU : kernelCommutator geometry a c ≤ U d.radical c :=
    le_normalizer_iff_commutator_le_left.mp
      (((show kernelCentralizer geometry a c ≤ Q d.radical a from inf_le_left).trans
        (hQaT.trans hTc)).trans (U_normalized c))
  have hX := geometry.omega_bound c hc (by
    rw [geometry.distance_constant c hc]
    exact lt_of_lt_of_le (by decide : 0<4) hb)
  intro x hx
  rw [Z,if_neg (by rw [ht]; decide)]
  apply mem_omegaCenter_iff.mpr
  have hxu := hHU hx
  have hxX := hX (U_le_Z c hxu)
  exact ⟨((hX.trans (omegaCenter_le _)).trans
    (Q_le_adjacent_h d.radical ht hct)) (U_le_Z c hxu),
    (mem_omegaCenter_iff.mp hxX).2.1,(le_centralizer_iff.mp hfix) hx⟩

omit [Finite F] [CharP F 2] in
/-- Every local conjugate of the neighboring vertex defines the identical
centralizer kernel; its commutator transports by the original action. -/
theorem Input.replacement_kernel_conjugate_at_edge
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical)
    {a c t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a) :
    kernelCentralizer geometry a (act d.radical g c) = kernelCentralizer geometry a c ∧
      kernelCommutator geometry a (act d.radical g c) =
        (kernelCommutator geometry a c).map (MulAut.conj g⁻¹).toMonoidHom := by
  have hn := kernelCentralizer_normalized_at_edge geometry hb
    (h.replacement_residual_edge_generation d) ha hat hct
  have hT : (kernelCentralizer geometry a c).map (MulAut.conj g⁻¹).toMonoidHom =
      kernelCentralizer geometry a c :=
    mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer d.radical a).inv_mem hg))
  have hQ : (Q d.radical a).map (MulAut.conj g⁻¹).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp
      (Q_normalized d.radical a ((stabilizer d.radical a).inv_mem hg))
  have hB : (B d.radical a (geometry.Z_normal a)).map (MulAut.conj g⁻¹).toMonoidHom =
      B d.radical a (geometry.Z_normal a) := mem_normalizer_iff_map_conj_eq.mp
    (Escape.Propagation.Rigidity.B_normalized hb a ha ((stabilizer d.radical a).inv_mem hg))
  have he : kernelCentralizer geometry a (act d.radical g c) = kernelCentralizer geometry a c := by
    rw [←hT]
    change Q d.radical a ⊓ centralizer
      ((U d.radical (act d.radical g c) ⊓ B d.radical a (geometry.Z_normal a) :
        Subgroup (FreeAmalgam d.radical)) : Set _) =
      (Q d.radical a ⊓ centralizer ((U d.radical c ⊓ B d.radical a (geometry.Z_normal a) :
        Subgroup (FreeAmalgam d.radical)) : Set _)).map (MulAut.conj g⁻¹).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      Theory.GroupTheory.map_centralizer_equiv,hQ]
    change Q d.radical a ⊓ centralizer
      ((U d.radical (act d.radical g c) ⊓ B d.radical a (geometry.Z_normal a) :
        Subgroup (FreeAmalgam d.radical)) : Set _) = Q d.radical a ⊓ centralizer
      (((U d.radical c ⊓ B d.radical a (geometry.Z_normal a)).map
        (MulAut.conj g⁻¹).toMonoidHom : Subgroup (FreeAmalgam d.radical)) : Set _)
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,hB,U_act]
  refine ⟨he,?_⟩
  change ⁅U d.radical (act d.radical g c),kernelCentralizer geometry a (act d.radical g c)⁆ =
    (⁅U d.radical c,kernelCentralizer geometry a c⁆).map (MulAut.conj g⁻¹).toMonoidHom
  rw [he,map_commutator,hT,U_act]

/-- At the exact v and x conventions of the contained paired selector, both
source kernels are the original T₀ and both full displacements lie in their
respective edge seeds. No new selector is chosen. -/
theorem Input.replacement_paired_field_index_kernel
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a c t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (v x : stabilizer d.radical a) :
    let c₁ := act d.radical v.val⁻¹ c
    let t₁ := act d.radical v.val⁻¹ t
    let c₂ := act d.radical x.val⁻¹ c₁
    let t₂ := act d.radical x.val⁻¹ t₁
    kernelCentralizer geometry a c₁ = kernelCentralizer geometry a c ∧
      kernelCentralizer geometry a c₂ = kernelCentralizer geometry a c ∧
      kernelCommutator geometry a c₁ = (kernelCommutator geometry a c).map
        (MulAut.conj v.val).toMonoidHom ∧
      kernelCommutator geometry a c₂ = ((kernelCommutator geometry a c).map
        (MulAut.conj v.val).toMonoidHom).map (MulAut.conj x.val).toMonoidHom ∧
      kernelCommutator geometry a c₁ ≤ Z d.radical t₁ ∧
      kernelCommutator geometry a c₂ ≤ Z d.radical t₂ := by
  dsimp only
  have hat₁ : Adjacent d.radical a (act d.radical v.val⁻¹ t) := by
    have hh := (adjacent_act_iff d.radical v.val⁻¹ _ _).mpr hat
    simpa only [show act d.radical v.val⁻¹ a=a from
      (stabilizer d.radical a).inv_mem v.property] using hh
  have hct₁ := (adjacent_act_iff d.radical v.val⁻¹ _ _).mpr hct
  obtain ⟨hT₁,hH₁⟩ := h.replacement_kernel_conjugate_at_edge d geometry (by omega)
    ha hat hct v.val⁻¹ ((stabilizer d.radical a).inv_mem v.property)
  obtain ⟨hT₂,hH₂⟩ := h.replacement_kernel_conjugate_at_edge d geometry (by omega)
    ha hat₁ hct₁ x.val⁻¹ ((stabilizer d.radical a).inv_mem x.property)
  simp only [inv_inv] at hH₁ hH₂
  have hH := h.replacement_field_index_kernel_commutator_le_edge_seed d geometry hb ha hat hct hsmall
  refine ⟨hT₁,hT₂.trans hT₁,hH₁,?_,?_,?_⟩
  · rw [hH₂,hH₁]
  · rw [hH₁,Z_act,inv_inv]
    exact map_mono hH
  · rw [hH₂,hH₁,Z_act,Z_act,inv_inv,inv_inv]
    exact map_mono (map_mono hH)

/-- The actual two-step vertex in the countercase to (5.9) supplies the
normal centralizer, whole radius, whole terminal subgroup and edge
displacement. This discharges the original H <= Z_beta premise before
transporting H by an arbitrary element of the two-step stabilizer. -/
theorem Input.replacement_strict_index_kernel_at_two_step
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    let c := path.walk.getVert 2
    let t := path.walk.getVert 1
    let T₀ := kernelCentralizer geometry a c
    stabilizer d.radical a ≤ normalizer (T₀ : Set _) ∧
      V d.radical a ≤ T₀ ∧
      Z d.radical (path.walk.getVert (path.walk.length-2)) ⊔
        (Z d.radical z ⊓ Q d.radical a) ≤ T₀ ∧
      kernelCommutator geometry a c ≤ Z d.radical t ∧
      ∀ y ∈ stabilizer d.radical c,
        conjugatedKernelCommutator geometry a c y ≤ Z d.radical c := by
  dsimp only
  have hlength := path.length_eq_b
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; omega
  have hc : color d.radical (path.walk.getVert 2)=false :=
    (path.vertex_color (by omega : 2 ≤ path.walk.length)).mpr (by decide)
  have hp : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.shortest,path.critical.1]
      exact geometry.even a path.start_color
    rw [Nat.even_iff] at he ⊢
    omega
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hH := h.replacement_field_index_kernel_commutator_le_edge_seed d geometry hb.le
    path.start_color hat hct hsmall
  refine ⟨kernelCentralizer_normalized_at_edge geometry (by omega)
    (h.replacement_residual_edge_generation d) path.start_color hat hct,
    radius_le_kernelCentralizer_at_edge geometry hb path.start_color hat hct,?_,hH,?_⟩
  · have hpa : Z d.radical (path.walk.getVert (path.walk.length-2)) ≤ Q d.radical a := by
      apply Z_le_Q_of_dist_lt d.radical _ (geometry.exists_critical _ hp)
      rw [geometry.distance_constant _ hp,SimpleGraph.dist_comm,path.dist_start (Nat.sub_le _ _)]
      change path.walk.length-2 < geometry.b d.radical
      omega
    have hpc : Z d.radical (path.walk.getVert (path.walk.length-2)) ≤
        Q d.radical (path.walk.getVert 2) := by
      apply Z_le_Q_of_dist_lt d.radical _ (geometry.exists_critical _ hp)
      rw [geometry.distance_constant _ hp,SimpleGraph.dist_comm]
      have hh := SimpleGraph.dist_le ((path.walk.drop 2).take (path.walk.length-4))
      rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_getVert,
        show 2+(path.walk.length-4)=path.walk.length-2 by omega] at hh
      have hi := hh.trans (min_le_right _ _)
      change (cosetGraph d.radical).dist (path.walk.getVert 2)
        (path.walk.getVert (path.walk.length-2)) < geometry.b d.radical
      omega
    have hzc : Z d.radical z ≤ Q d.radical (path.walk.getVert 2) := by
      apply Z_le_Q_of_dist_lt d.radical z (geometry.exists_critical z path.end_color)
      rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end]
      change path.walk.length-2 < geometry.b d.radical
      omega
    have hQC : Q d.radical (path.walk.getVert 2) ≤ centralizer
        ((U d.radical (path.walk.getVert 2) ⊓ B d.radical a (geometry.Z_normal a) :
          Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes _ hc))).trans (centralizer_le (inf_le_left.trans (U_le_Z _)))
    exact le_inf (sup_le hpa inf_le_right) ((sup_le hpc (inf_le_left.trans hzc)).trans hQC)
  · intro y hy
    exact conjugated_kernel_commutator_le_next_seed geometry (by omega) path y hy hH

omit h d in
private theorem conjugate_escape_of_simple_image
    {G J : Type*} [Group G] [Group J] [IsSimpleGroup J]
    (S Q Z A D : Subgroup G) (f : S →* J) (hf : Function.Surjective f)
    (hk : f.ker.map S.subtype = Q)
    (hZS : Z ≤ S) (hZn : S ≤ normalizer (Z : Set G))
    (hZQ : Z ≤ centralizer (Q : Set G))
    (hAS : A ≤ S) (hAQ : ¬ A ≤ Q) (hDZ : D ≤ Z)
    (hD : ¬ D ≤ centralizer (S : Set G)) :
    ∃ g ∈ S, ∃ x ∈ D, g*x*g⁻¹ ∉ centralizer (A : Set G) := by
  classical
  by_contra! hno
  let W := conjugateSpanBy D S
  have hWZ : W ≤ Z := conjugateSpanBy_le hDZ hZn
  have hWS : W ≤ S := hWZ.trans hZS
  have hWn : S ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy D S
  have hWA : W ≤ centralizer (A : Set G) := by
    apply (closure_le _).mpr
    rintro _ ⟨g,hg,x,hx,rfl⟩
    exact hno g hg x hx
  let W₀ := W.subgroupOf S
  let N := centralizer (W₀ : Set S)
  let : W₀.Normal := normal_subgroupOf_of_le_normalizer hWn
  let : N.Normal := inferInstance
  have hker : f.ker ≤ N := by
    intro k hk₀ w hw
    apply Subtype.val_injective
    have hkQ : k.val∈Q := hk ▸ mem_map_of_mem S.subtype hk₀
    exact (hZQ (hWZ hw) k.val hkQ).symm
  have hAN : A.subgroupOf S ≤ N := by
    intro x hx w hw
    apply Subtype.val_injective
    exact (hWA hw x.val hx).symm
  have hnker : ¬ N ≤ f.ker := by
    intro hNk
    apply hAQ
    intro x hx
    exact hk ▸ mem_map_of_mem S.subtype
      (hNk (hAN (show (⟨x,hAS hx⟩ : S) ∈ A.subgroupOf S from hx)))
  have hmap : N.map f=⊤ := by
    rcases (Normal.map (inferInstance : N.Normal) f hf).eq_bot_or_eq_top with hz | ht
    · exact False.elim (hnker ((map_eq_bot_iff N).mp hz))
    · exact ht
  have hNtop : N=⊤ := by
    have hh := congrArg (Subgroup.comap f) hmap
    simpa only [comap_map_eq,comap_top,sup_eq_left.mpr hker] using hh
  apply hD
  intro x hx y hy
  have hxy : (⟨y,hy⟩ : S) ∈ N := hNtop ▸ mem_top _
  exact (congrArg Subtype.val (hxy (⟨x,hWS (le_conjugateSpanBy D S hx)⟩ : S)
    (le_conjugateSpanBy D S hx))).symm

/-- A noncentral subgroup of the full starting seed has an element whose
local conjugate moves the original critical endpoint. The same original
quotient kernel is used to exclude a central normal orbit. -/
theorem Input.replacement_noncentral_seed_conjugate_escape
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (D : Subgroup (FreeAmalgam d.radical)) (hDZ : D ≤ Z d.radical a)
    (hD : ¬ D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ g ∈ stabilizer d.radical a, ∃ x ∈ D,
      g*x*g⁻¹ ∉ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) := by
  obtain ⟨E,hE,f,hf,hfQ,_⟩ := h.replacement_inner_natural_action d geometry hb path.start_color
  have hlarge : 3 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 3 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup hlarge
  let : IsSimpleGroup (Sp E.Carrier) :=
    Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.isSimpleGroup
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hzQ := (critical_reverse d.radical geometry hedge a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; exact lt_of_lt_of_le (by decide : 0<4) hb)
    z path.end_color path.critical).2
  exact conjugate_escape_of_simple_image (stabilizer d.radical a) (Q d.radical a)
    (Z d.radical a) (Z d.radical z) D f hf hfQ (Z_le_stabilizer d.radical a)
    (Z_normalized d.radical a)
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color))
    (path.endpoint_Z_le_start_stabilizer (by omega)) hzQ hDZ hD

/-- The noncentral-H branch supplies a moved element in a conjugate of H
with the original T₀ unchanged. The element escapes the whole terminal
radius. The further centralizer-generation clause of source (*) is not
part of this conclusion. -/
theorem Input.replacement_field_index_kernel_escape
    {geometry : Geometry d.radical} {a z c t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F)
    (hD : ¬ kernelCommutator geometry a c ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ g ∈ stabilizer d.radical a, ∃ x ∈ kernelCommutator geometry a c,
      let c₁ := act d.radical g⁻¹ c
      let t₁ := act d.radical g⁻¹ t
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      (kernelCommutator geometry a c).map (MulAut.conj g).toMonoidHom =
        ⁅U d.radical c₁,kernelCentralizer geometry a c⁆ ∧
      ⁅U d.radical c₁,kernelCentralizer geometry a c⁆ ≤ Z d.radical t₁ ∧
      g*x*g⁻¹ ∈ ⁅U d.radical c₁,kernelCentralizer geometry a c⁆ ∧
      g*x*g⁻¹ ∉ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) ∧
      g*x*g⁻¹ ∉ V d.radical (path.walk.getVert (path.walk.length-2)) := by
  have hH := h.replacement_field_index_kernel_commutator_le_edge_seed d geometry hb.le
    path.start_color hat hct hsmall
  obtain ⟨g,hg,x,hx,hescape⟩ := h.replacement_noncentral_seed_conjugate_escape d path hb.le
    (kernelCommutator geometry a c) (hH.trans (adjacent_Z_le d.radical path.start_color hat)) hD
  have hga : act d.radical g⁻¹ a=a := (stabilizer d.radical a).inv_mem hg
  have hat₁ : Adjacent d.radical a (act d.radical g⁻¹ t) := by
    rw [←hga]
    exact (adjacent_act_iff d.radical g⁻¹ _ _).mpr hat
  have hct₁ := (adjacent_act_iff d.radical g⁻¹ _ _).mpr hct
  have hn := kernelCentralizer_normalized_at_edge geometry (by omega)
    (h.replacement_residual_edge_generation d) path.start_color hat hct
  have hT : (kernelCentralizer geometry a c).map (MulAut.conj g).toMonoidHom =
      kernelCentralizer geometry a c := mem_normalizer_iff_map_conj_eq.mp (hn hg)
  have he : (kernelCommutator geometry a c).map (MulAut.conj g).toMonoidHom =
      ⁅U d.radical (act d.radical g⁻¹ c),kernelCentralizer geometry a c⁆ := by
    change (⁅U d.radical c,kernelCentralizer geometry a c⁆).map _ = _
    rw [map_commutator,hT,U_act,inv_inv]
  have hH₁ : ⁅U d.radical (act d.radical g⁻¹ c),kernelCentralizer geometry a c⁆ ≤
      Z d.radical (act d.radical g⁻¹ t) := by
    rw [←he,Z_act,inv_inv]
    exact map_mono hH
  refine ⟨g,hg,x,hx,hat₁,hct₁,he,hH₁,?_,hescape,?_⟩
  · rw [←he]
    exact mem_map_of_mem _ hx
  · intro hbad
    have hlen : 2 ≤ path.walk.length := by rw [path.length_eq_b]; omega
    have hp : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
      apply (path.vertex_color (Nat.sub_le _ _)).mpr
      have heven : Even path.walk.length := by
        rw [path.shortest,path.critical.1]
        exact geometry.even a path.start_color
      rw [Nat.even_iff] at heven ⊢
      omega
    have hpQ : V d.radical (path.walk.getVert (path.walk.length-2)) ≤ Q d.radical z := by
      apply V_le_Q_of_dist_add_two_lt d.radical hp
      rw [path.dist_end]
      change path.walk.length-(path.walk.length-2)+2<geometry.b d.radical
      omega
    exact hescape ((le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))) (hpQ hbad))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
