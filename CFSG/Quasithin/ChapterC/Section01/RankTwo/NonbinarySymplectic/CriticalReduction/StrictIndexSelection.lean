module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexSecondSpan

/-!
# Whole-displacement centralizers and the same terminal selector

If a small-index actor has natural displacement of dimension at most one,
a moved commutator element determines the centralizer of its entire
commutator subgroup. Its nonzero projection spans that line; fixed-vector
lifting through the full natural cover fixes every other commutator,
including all central attachments. The existing element-centralizer
generation theorem therefore gives generation by the whole displacement
centralizer and any two-group moving that displacement.

For the literal H₂ and the same source conjugator y, movement of the
endpoint radius selects a seed Z_e at distance exactly two from the
endpoint. It is critical with c = a+2. Append its two-edge tail to the
original path with its first two edges removed, retaining every overlap.
The full centralizer of H₂ and Z_e generate G_c. Both original second
spans retain their placement in Q_c and both original terminal kernels.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9)(**), printed pp.920--921. This proves the simultaneous
terminal selection and generation for the same radius-moving y. Existence
of that y, the following displacement comparison, strict-index and later
terminal exclusions, and the minimum-replacement distance-two witness
remain to be proved. No central complement or field-degree restriction
is assumed.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative Pointwise

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

private theorem displacement_centralizer_eq_element
    {F W G : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W] [Group G]
    {σ : Representation (ZMod 2) (L (K := F)) W}
    (p : σ.IntertwiningMap (binaryNatural (K := F))) (hp : IsCover p)
    (j : Multiplicative W →* G) (hj : Function.Injective j)
    (γ : G →* L (K := F))
    (hact : ∀ (g : G) (w : W), j (Multiplicative.ofAdd (σ (γ g) w)) =
      g*j (Multiplicative.ofAdd w)*g⁻¹)
    (T A : Subgroup G)
    (hd : Module.finrank F
      (displacementSpace ((T.map γ).map (commutator (Sp F)).subtype)) ≤ 1)
    (hm : ¬ ⁅j.range,T⁆ ≤ centralizer (A : Set G)) :
    ∃ u ∈ ⁅j.range,T⁆, u ∈ j.range ∧ u ∉ centralizer (A : Set G) ∧
      centralizer ({u} : Set G)=centralizer ((⁅j.range,T⁆ : Subgroup G) : Set G) := by
  have hn : ∃ t ∈ T, ∃ u ∈ j.range, ⁅t,u⁆ ∉ centralizer (A : Set G) := by
    by_contra! hn
    apply hm
    rw [commutator_comm]
    exact commutator_le.mpr hn
  obtain ⟨t,ht,u,⟨v,rfl⟩,hmv⟩ := hn
  let w := σ (γ t) v.toAdd-v.toAdd
  have hw : j (Multiplicative.ofAdd w)=⁅t,j v⁆ := by
    dsimp only [w]
    rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
    rfl
  let D := displacementSpace ((T.map γ).map (commutator (Sp F)).subtype)
  have hmem (t' : G) (ht' : t' ∈ T) (v' : W) :
      p (σ (γ t') v'-v') ∈ D := by
    rw [map_sub,p.isIntertwining]
    exact Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp ((T.map γ).map (commutator (Sp F)).subtype).subtype)
      ⟨(γ t').val,mem_map_of_mem _ (mem_map_of_mem γ ht')⟩ (p v')
  have hw0 : p w ≠ 0 := by
    intro hz
    apply hmv
    rw [←hw]
    intro g hg
    have hf := cover_fixed_of_projection_fixed p hp (γ g) w (by rw [hz,map_zero])
    have he := congrArg (fun v => j (Multiplicative.ofAdd v)) hf
    rw [hact,mul_inv_eq_iff_eq_mul] at he
    exact he
  have hline : D=F ∙ p w := by
    have hpos : 0 < Module.finrank F D := by
      by_contra! hz
      have he : D=⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hz)
      have hv := hmem t ht v.toAdd
      rw [he] at hv
      exact hw0 hv
    change Module.finrank F D ≤ 1 at hd
    exact eq_span_singleton_of_mem_of_finrank_eq_one (by omega : Module.finrank F D=1)
      (hmem t ht v.toAdd) hw0
  have hcomm : j (Multiplicative.ofAdd w) ∈ ⁅j.range,T⁆ := by
    rw [hw,commutator_comm]
    exact commutator_mem_commutator ht ⟨v,rfl⟩
  refine ⟨j (Multiplicative.ofAdd w),hcomm,⟨_,rfl⟩,hw ▸ hmv,?_⟩
  apply le_antisymm
  · intro g hg
    have hgw : σ (γ g) w=w := by
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hact,mem_centralizer_singleton_iff.mp hg,mul_inv_cancel_right]
    have hgp : (γ g).val • p w=p w := by
      exact (LinearMap.congr_fun (p.isIntertwining' (γ g)) w).symm.trans (congrArg p hgw)
    have hfix : ⁅j.range,T⁆ ≤ centralizer ({g} : Set G) := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro t' ht' u' hu'
      obtain ⟨v',rfl⟩ := hu'
      let w' := σ (γ t') v'.toAdd-v'.toAdd
      have hw' : j (Multiplicative.ofAdd w')=⁅t',j v'⁆ := by
        dsimp only [w']
        rw [ofAdd_sub,div_eq_mul_inv,map_mul,map_inv,hact]
        rfl
      have hproj : (γ g).val • p w'=p w' := by
        have hv' := hmem t' ht' v'.toAdd
        rw [hline] at hv'
        obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv'
        change c • p w=p w' at hc
        change symplecticNatural 2 (γ g).val (p w')=p w'
        rw [←hc,map_smul]
        change c • ((γ g).val • p w)=c • p w
        rw [hgp]
      have hf := cover_fixed_of_projection_fixed p hp (γ g) w' hproj
      have he := congrArg (fun v => j (Multiplicative.ofAdd v)) hf
      rw [hact,hw',mul_inv_eq_iff_eq_mul] at he
      exact mem_centralizer_singleton_iff.mpr he.symm
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hfix hx)
  · exact centralizer_le (Set.singleton_subset_iff.mpr hcomm)

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A two-group moving the complete field-sized displacement generates the
vertex with its full centralizer, including every central attachment. -/
theorem Input.replacement_field_displacement_centralizer_generation
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (T A : Subgroup (FreeAmalgam d.radical))
    (hTS : T ≤ stabilizer d.radical a) (hAS : A ≤ stabilizer d.radical a)
    (hA : IsPGroup 2 A)
    (hsmall : (centralizer (T : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F)
    (hm : ¬ ⁅U d.radical a,T⁆ ≤ centralizer (A : Set (FreeAmalgam d.radical))) :
    (stabilizer d.radical a ⊓ centralizer ((⁅U d.radical a,T⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) ⊔ A =
      stabilizer d.radical a := by
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
  have hmap : (⁅U₀,T₀⁆).map S.subtype=⁅U d.radical a,T⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS]
  have hm₀ : ¬ ⁅jS.range,T₀⁆ ≤ centralizer (A.subgroupOf S : Set S) := by
    rw [hjSr]
    intro hh
    apply hm
    have hh' := (map_mono (f := S.subtype) hh).trans
      (map_centralizer_le_centralizer_image _ S.subtype)
    rwa [hmap,←Subgroup.coe_map,map_subgroupOf_eq_of_le hAS] at hh'
  obtain ⟨u,hu,huU,hum,hcentral⟩ := displacement_centralizer_eq_element
    (MovedSection.coverProjection s e) he jS hjS γ haction T₀ (A.subgroupOf S) hdim hm₀
  have huUa : u.val ∈ U d.radical a := by
    rw [hjSr] at huU
    exact huU
  have hmA : u.val ∉ centralizer (A : Set (FreeAmalgam d.radical)) := by
    intro hh
    apply hum
    intro x hx
    apply Subtype.ext
    exact hh x.val hx
  have hC : S ⊓ centralizer ({u.val} : Set (FreeAmalgam d.radical)) ≤
      S ⊓ centralizer ((⁅U d.radical a,T⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rintro g ⟨hg,hgu⟩
    refine ⟨hg,?_⟩
    have hgc : (⟨g,hg⟩ : S) ∈ centralizer ((⁅jS.range,T₀⁆ : Subgroup S) : Set S) := by
      rw [←hcentral]
      apply mem_centralizer_singleton_iff.mpr
      apply Subtype.ext
      exact mem_centralizer_singleton_iff.mp hgu
    intro x hx
    rw [←hmap] at hx
    obtain ⟨x,hx,rfl⟩ := hx
    rw [hjSr] at hgc
    exact congrArg Subtype.val (hgc x hx)
  have hgen := h.replacement_U_element_centralizer_generation d geometry hb ha A hAS hA
    u.val huUa hmA
  apply le_antisymm (sup_le inf_le_left hAS)
  calc
    stabilizer d.radical a = (S ⊓ centralizer ({u.val} : Set (FreeAmalgam d.radical))) ⊔ A := hgen.symm
    _ ≤ _ := sup_le_sup hC le_rfl

/-- On the same source conjugator that moves the endpoint radius, select
its actual terminal seed. This seed and the centralizer of the whole H₂
generate G_c, and the two original second spans retain their full kernels. -/
theorem Input.replacement_strict_index_second_span_selection
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
    ∃ e, ∃ selected : CriticalPath d.radical geometry c e,
      (cosetGraph d.radical).dist e z=2 ∧
      (∀ i ≤ path.walk.length-2, selected.walk.getVert i=path.walk.getVert (i+2)) ∧
      ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) ∧
      C₀ ⊔ Z d.radical e=stabilizer d.radical c ∧
      Z₀ ≤ W ∧ W ≤ Q d.radical c ∧
      W ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧ W ≤ Q d.radical z := by
  dsimp only
  let c := path.walk.getVert 2
  let mu := act d.radical y a
  let H₂ := conjugatedKernelCommutator geometry a c y
  have hc : color d.radical c=false :=
    (path.vertex_color (by rw [path.length_eq_b]; omega)).mpr (by decide)
  have hmu : color d.radical mu=false := by rw [action_preserves_color]; exact path.start_color
  obtain ⟨hT,hH,_,_,_,_,_,_,hHZ,_⟩ :=
    h.replacement_strict_index_conjugated_span d path hb hsmall y hy
  have hmV : ¬ V d.radical z ≤ centralizer (H₂ : Set (FreeAmalgam d.radical)) :=
    fun hh => hmove (le_centralizer_iff.mpr hh)
  obtain ⟨e,hecol,hed,hem⟩ : ∃ e, color d.radical e=false ∧
      (cosetGraph d.radical).dist e z ≤ 2 ∧
      ¬ Z d.radical e ≤ centralizer (H₂ : Set (FreeAmalgam d.radical)) := by
    simpa only [V_le_iff d.radical path.end_color,not_forall,exists_prop] using hmV
  have hEm : ¬ H₂ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    fun hh => hem (le_centralizer_iff.mp hh)
  have hEQ : ¬ Z d.radical e ≤ Q d.radical c := by
    intro hh
    exact hEm (hHZ.trans ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes c hc)).trans (centralizer_le hh)))
  have hmin := criticalDistance_le d.radical e (geometry.exists_critical e hecol) hEQ
  rw [geometry.distance_constant e hecol] at hmin
  change geometry.b d.radical ≤ _ at hmin
  have hzc : (cosetGraph d.radical).dist z c=geometry.b d.radical-2 := by
    rw [SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
  have htri := (cosetGraph_connected d.radical).dist_triangle (u := e) (v := z) (w := c)
  have hez : (cosetGraph d.radical).dist e z=2 := by omega
  have hec : CriticalPair d.radical e c (geometry.exists_critical e hecol) := by
    refine ⟨?_,hEQ⟩
    rw [geometry.distance_constant e hecol]
    change _=geometry.b d.radical
    omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  have hce := critical_reverse d.radical geometry hedge e hecol
    (by rw [geometry.distance_constant e hecol]; change 0 < geometry.b d.radical; omega) c hc hec
  obtain ⟨tail,htail⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist z e
  have htlen : tail.length=2 := by rw [htail,SimpleGraph.dist_comm,hez]
  let walk := (path.walk.drop 2).append tail
  have hwlen : walk.length=geometry.b d.radical := by
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.drop_length,htlen,path.length_eq_b]
    omega
  have hdce : (cosetGraph d.radical).dist c e=geometry.b d.radical :=
    hce.1.trans (geometry.distance_constant c hc)
  let selected : CriticalPath d.radical geometry c e := ⟨hc,walk,hwlen.trans hdce.symm,hce⟩
  have hover (i : ℕ) (hi : i ≤ path.walk.length-2) :
      selected.walk.getVert i=path.walk.getVert (i+2) := by
    change ((path.walk.drop 2).append tail).getVert i=_
    rw [SimpleGraph.Walk.getVert_append',if_pos (by rwa [SimpleGraph.Walk.drop_length]),
      SimpleGraph.Walk.drop_getVert,Nat.add_comm 2 i]
  have hES : Z d.radical e ≤ stabilizer d.radical c :=
    Z_le_stabilizer_of_dist_le e (geometry.exists_critical e hecol) hec.1.le
  have hTS : kernelCentralizer geometry mu c ≤ stabilizer d.radical c := by
    rw [hT]
    exact kernelCentralizer_conjugate_le_stabilizer geometry path (by omega) y hy
  have hsmall' : (B d.radical mu (geometry.Z_normal mu)).relIndex (U d.radical c) ≤ Nat.card F := by
    rw [Escape.PairingControl.FirstPairing.B_act (by omega) y a path.start_color,
      ←show act d.radical y c=c from hy,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hsmall
  let : IsElementaryAbelian 2 (Z d.radical e) := geometry.Z_elementary (by omega) e hecol
  have hgen := h.replacement_field_displacement_centralizer_generation d geometry hb.le hc
    (kernelCentralizer geometry mu c) (Z d.radical e) hTS hES
    (IsElementaryAbelian.isPGroup 2 (Z d.radical e))
    ((kernelCentralizer_moving_index_le geometry mu c).trans hsmall')
    (by change ¬ kernelCommutator geometry mu c ≤ _; rw [hH]; exact hEm)
  change (stabilizer d.radical c ⊓ centralizer (kernelCommutator geometry mu c : Set _)) ⊔
    Z d.radical e=stabilizer d.radical c at hgen
  rw [hH] at hgen
  exact ⟨e,selected,hez,hover,hEm,hgen,
    h.replacement_strict_index_second_spans_endpoint d path hb hsmall y hy hmove⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
