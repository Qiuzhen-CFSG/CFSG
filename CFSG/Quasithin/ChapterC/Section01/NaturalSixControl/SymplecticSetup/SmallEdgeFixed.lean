module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeLayer
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.MaximalOffenders
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.SmallImage
public import Theory.GroupTheory.FixedSupplementCentralizer
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Fixed subgroups on a small natural symplectic edge

A nontrivial image in the point core with fixed index at most two is a
transposition group. On the natural four-dimensional module its fixed
hyperplane is moved by the point core into the transposition's moved line,
and its pointwise fixer in the point core is precisely that image.

The source coordinates transfer these two facts to W. The proved edge-layer
decomposition Zα = Uα Zβ extends the commutator bound because Qβ centralizes
the edge seed. An injective source embedding followed by conjugation gives
both bounds on every actual graph edge. The ambient amalgam need not be finite.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7), printed p.919, using the
natural-layer and edge-seed identities in (3.2), (3.6).
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

omit [Finite M] in
private theorem smallEdge_fixed_iff (A:Subgroup M) (w:W) :
    (s.coordinates w).toAdd ∈ fixedSpace Model.rho (A.map s.projection) ↔
      (w:M)∈centralizer (A:Set M) := by
  constructor
  · intro hw a ha
    have hx := hw ⟨s.projection a,mem_map_of_mem _ ha⟩
    change Model.rho (s.projection a) (s.coordinates w).toAdd = (s.coordinates w).toAdd at hx
    rw [←s.action] at hx
    have hy := s.coordinates.injective (Multiplicative.toAdd.injective hx)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hy)
  · intro hw a
    obtain ⟨b,hb,he⟩ := a.property
    change Model.rho (a:Model.S) (s.coordinates w).toAdd = (s.coordinates w).toAdd
    rw [←he,←s.action]
    congr 2
    apply Subtype.ext
    change b*(w:M)*b⁻¹=w
    rw [hw b hb,mul_inv_cancel_right]

omit [Finite M] in
private theorem smallEdge_moved_iff (hq:Function.Surjective s.projection)
    (A:Subgroup M) (w:W) :
    (s.coordinates w).toAdd ∈ subspaceCommutator Model.rho ⊤ (A.map s.projection) ↔
      (w:M)∈⁅W,A⁆ := by
  let := s.module_elementary
  let d : NaturalAction W := ⟨s.projection,hq,s.projection_kernel,s.coordinates,s.action⟩
  have he := subspaceCommutator_map_embedding Model.rho d.ρ (MonoidHom.id Model.S)
    d.linearCoordinates.toLinearMap (fun g w => (d.equivariant g w).symm) (A.map d.q) ⊤
  rw [Submodule.map_top,LinearMap.range_eq_top.mpr d.linearCoordinates.surjective,
    map_id] at he
  change subspaceCommutator Model.rho ⊤ (A.map d.q) =
    (subspaceCommutator (Representation.NormalElementaryQuotient.representation W d.q d.onto d.kernel_centralizer) ⊤ (A.map d.q)).map d.linearCoordinates.toLinearMap at he
  rw [←Representation.NormalElementaryQuotient.commutatorSpace_eq] at he
  change d.linearCoordinates (Additive.ofMul w) ∈ subspaceCommutator Model.rho ⊤ (A.map d.q) ↔ _
  rw [he]
  constructor
  · rintro ⟨v,hv,he⟩
    have hvw : v=Additive.ofMul w := d.linearCoordinates.injective he
    rw [hvw] at hv
    exact hv
  · intro hw
    exact ⟨Additive.ofMul w,hw,rfl⟩

/-- The natural source module satisfies the displacement and pointwise-fixer
bounds for a nontrivial image of fixed index at most two. -/
theorem module_small_edge_fixed (u:Model.S)
    (hfull:R.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (A:Subgroup M) (hA:A≤R) (hne:¬A≤pCore 2 M)
    (hindex:(centralizer (A:Set M)).relIndex W≤2) :
    ⁅W⊓centralizer (A:Set M),R⁆≤⁅W,A⁆ ∧
      R⊓centralizer (W⊓centralizer (A:Set M):Set M)≤pCore 2 M⊔A := by
  let := s.module_elementary
  have hE : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom := by
    rwa [Model.pointCore_eq_exceptional] at hfull
  have hq := s.projection_surjective_of_radical_image_le_conjugate u hE.le
  let d : NaturalAction W := ⟨s.projection,hq,s.projection_kernel,s.coordinates,s.action⟩
  have hAm : A.map s.projection≤pointCore.map (MulAut.conj u).toMonoidHom :=
    (map_mono hA).trans_eq hfull
  have hAn : A.map s.projection≠⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hsmall : fixedCodim Model.rho (A.map s.projection)≤1 := by
    rw [s.fixed_index] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hindex
  have hmove := PointCoreTranspositionFixed.small_image_fixed_displacement_le
    u (A.map s.projection) hAm hAn hsmall
  constructor
  · apply commutator_le.mpr
    intro w hw r hr
    have hcw : ⁅w,r⁆∈W := (commutator_le_left W R) (commutator_mem_commutator hw.1 hr)
    apply (s.smallEdge_moved_iff hq A ⟨⁅w,r⁆,hcw⟩).mp
    have hm : Model.rho (s.projection r) (s.coordinates ⟨w,hw.1⟩).toAdd-
        (s.coordinates ⟨w,hw.1⟩).toAdd ∈
          subspaceCommutator Model.rho ⊤ (A.map s.projection) :=
      hmove (Submodule.subset_span ⟨s.projection r,hfull ▸ mem_map_of_mem _ hr,
        (s.coordinates ⟨w,hw.1⟩).toAdd,(s.smallEdge_fixed_iff A ⟨w,hw.1⟩).mpr hw.2,rfl⟩)
    have hc := congrArg d.linearCoordinates
      (Representation.NormalElementaryQuotient.vector_commutator W d.q d.onto
        d.kernel_centralizer ⟨w,hw.1⟩ r)
    rw [map_sub] at hc
    change d.linearCoordinates (Additive.ofMul ⟨⁅w,r⁆,hcw⟩) =
      d.linearCoordinates (Additive.ofMul ⟨w,hw.1⟩)-
      d.linearCoordinates (d.ρ (d.q r) (Additive.ofMul ⟨w,hw.1⟩)) at hc
    rw [d.equivariant] at hc
    change (s.coordinates ⟨⁅w,r⁆,hcw⟩).toAdd =
      (s.coordinates ⟨w,hw.1⟩).toAdd-Model.rho (s.projection r) (s.coordinates ⟨w,hw.1⟩).toAdd at hc
    rw [hc]
    simpa only [neg_sub] using (subspaceCommutator Model.rho ⊤ (A.map s.projection)).neg_mem hm
  · intro r hr
    have hfix : ∀v∈fixedSpace Model.rho (A.map s.projection),Model.rho (s.projection r) v=v := by
      intro v hv
      let w := s.coordinates.symm (Multiplicative.ofAdd v)
      have hw : (w:M)∈W⊓centralizer (A:Set M) :=
        ⟨w.property,(s.smallEdge_fixed_iff A w).mp (by
          change (s.coordinates (s.coordinates.symm (Multiplicative.ofAdd v))).toAdd ∈ _
          rw [s.coordinates.apply_symm_apply]
          exact hv)⟩
      have he : MulAut.conjNormal r w=w := by
        apply Subtype.ext
        change r*(w:M)*r⁻¹=(w:M)
        rw [←hr.2 w hw,mul_inv_cancel_right]
      have hh := s.action r w
      rw [he] at hh
      change (s.coordinates (s.coordinates.symm (Multiplicative.ofAdd v))).toAdd =
        Model.rho (s.projection r) (s.coordinates (s.coordinates.symm (Multiplicative.ofAdd v))).toAdd at hh
      rw [s.coordinates.apply_symm_apply] at hh
      exact hh.symm
    have hmem := (PointCoreTranspositionFixed.small_image_fixes_iff u (A.map s.projection)
      hAm hAn hsmall (s.projection r) (hfull ▸ mem_map_of_mem _ hr.1)).mp hfix
    have hh : r∈(A.map s.projection).comap s.projection := hmem
    rwa [comap_map_eq,s.projection_kernel,sup_comm] at hh

/-- Adjoining the edge seed preserves the displacement bound; its pointwise
fixer can only decrease. -/
theorem seedHull_small_edge_fixed (h:NativeCentralLayer s) (u:Model.S)
    (hfull:R.map s.projection=pointCore.map (MulAut.conj u).toMonoidHom)
    (A:Subgroup M) (hA:A≤R) (hne:¬A≤pCore 2 M)
    (hindex:(centralizer (A:Set M)).relIndex W≤2) :
    ⁅normalClosure (omegaCenter R:Set M)⊓centralizer (A:Set M),R⁆≤⁅W,A⁆ ∧
      R⊓centralizer (normalClosure (omegaCenter R:Set M)⊓centralizer (A:Set M):Set M)≤pCore 2 M⊔A := by
  obtain ⟨hmove,hfix⟩ := s.module_small_edge_fixed u hfull A hA hne hindex
  have hseed : omegaCenter R≤centralizer (R:Set M) :=
    fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hdecomp : normalClosure (omegaCenter R:Set M)⊓centralizer (A:Set M)=
      (W⊓centralizer (A:Set M))⊔omegaCenter R := by
    rw [s.seedHull_eq_module_sup_seed h,sup_comm W,
      inf_centralizer_sup_of_centralizing _ _ _ le_normalizer_of_normal hseedA,sup_comm]
  constructor
  · rw [hdecomp]
    apply commutator_le.mpr
    intro x hx r hr
    have hn : omegaCenter R≤normalizer (W⊓centralizer (A:Set M):Set M) :=
      (le_inf le_normalizer_of_normal (hseedA.trans (centralizer (A:Set M)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hx' : x∈(W⊓centralizer (A:Set M):Set M)*(omegaCenter R:Set M) := by
      have hp := coe_mul_of_right_le_normalizer_left (W⊓centralizer (A:Set M)) (omegaCenter R) hn
      exact hp ▸ hx
    obtain ⟨w,hw,z,hz,rfl⟩ := hx'
    have hzcomm : ⁅z,r⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hseed hz r hr).symm
    rw [commutatorElement_mul_left_eq_conj_mul,hzcomm,mul_one,mul_inv_cancel,one_mul]
    exact hmove (commutator_mem_commutator hw hr)
  · have hWH : W≤normalClosure (omegaCenter R:Set M) := by
      rw [s.seedHull_eq_module_sup_seed h]
      exact le_sup_left
    exact (inf_le_inf_left R (centralizer_le (show (W⊓centralizer (A:Set M):Set M) ⊆
      (normalClosure (omegaCenter R:Set M)⊓centralizer (A:Set M):Set M) from
      fun _ hx => ⟨hWH hx.1,hx.2⟩))).trans hfix


private theorem smallEdge_coordinates (h : NativeCentralLayer s) {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t) :
    ∃ i : M →* FreeAmalgam R, Function.Injective i ∧
      R.map i = Q R t ∧ (pCore 2 M).map i = Q R c ∧ W.map i = U R c ∧
      (normalClosure (omegaCenter R : Set M)).map i = Z R c := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
    · have he := Q_act R g (beta R)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act R g (alpha R)
      rw [Q_alpha R s.two_group s.core_le] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := U_act R g (alpha R)
      rw [h.U_eq_module] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Z_act R g (alpha R)
      rw [SymplecticSeed.Z_eq_seedHull] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc

/-- The small fixed-index edge case on the literal `Z` layer: its fixed part
has commutator in the natural moved line, and its pointwise fixer in the edge
radical is contained in the core times the acting subgroup. -/
theorem small_edge_fixed_at (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R t) (hne : ¬A ≤ Q R c)
    (hindex : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R c) ≤ 2) :
    ⁅Z R c ⊓ centralizer (A : Set (FreeAmalgam R)),Q R t⁆ ≤ ⁅U R c,A⁆ ∧
      Q R t ⊓ centralizer (Z R c ⊓ centralizer (A : Set (FreeAmalgam R)) :
        Set (FreeAmalgam R)) ≤ Q R c ⊔ A := by
  obtain ⟨i,hi,hiR,hiQ,hiW,hiZ⟩ := s.smallEdge_coordinates h hc hct
  have hAi : A ≤ i.range := hA.trans (hiR ▸ map_le_range i R)
  have hAm : (A.comap i).map i = A := map_comap_eq_self hAi
  have hAr : A.comap i ≤ R := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hAm,hiR]
  have hAn : ¬A.comap i ≤ pCore 2 M := by
    intro he
    apply hne
    have hm := map_mono (f := i) he
    rwa [hAm,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set M)).relIndex W ≤ 2 := by
    have he : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R c) =
        (centralizer (A.comap i : Set M)).relIndex W := by
      rw [←hiW,←hAm,←inf_relIndex_right,inf_comm,
        map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
        inf_relIndex_left,comap_map_eq_self_of_injective hi]
    rwa [he] at hindex
  obtain ⟨hm,hf⟩ := s.seedHull_small_edge_fixed h u hfull (A.comap i) hAr hAn hidx
  constructor
  · have he := map_mono (f := i) hm
    rw [map_commutator,←map_inf_centralizer_of_injective i hi,hiZ,hAm,hiR,
      map_commutator,hiW,hAm] at he
    exact he
  · intro x hx
    obtain ⟨r,hr,rfl⟩ := hiR.symm ▸ hx.1
    have hsup : (pCore 2 M⊔A.comap i).map i = Q R c⊔A := by
      rw [Subgroup.map_sup,hiQ,hAm]
    rw [←hsup]
    apply mem_map_of_mem i
    apply hf
    refine ⟨hr,?_⟩
    intro y hy
    apply hi
    have hy' : i y∈Z R c⊓centralizer (A:Set (FreeAmalgam R)) := by
      refine ⟨hiZ ▸ mem_map_of_mem i hy.1,?_⟩
      intro a ha
      obtain ⟨b,hb,rfl⟩ := hAm.symm ▸ ha
      simpa only [map_mul] using congrArg i (hy.2 b hb)
    simpa only [map_mul] using hx.2 (i y) hy'

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
