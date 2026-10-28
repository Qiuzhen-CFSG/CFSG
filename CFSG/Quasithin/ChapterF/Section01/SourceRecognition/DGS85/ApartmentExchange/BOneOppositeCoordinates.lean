module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRootCoordinates
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalKernelMarking

/-!
# Opposite path-root coordinates in the same original actor

The chosen whole-Cartan reflection is nontrivial modulo the endpoint core
because it moves the marked neighbor. In the full diagonal marking already
constructed from the source Borel, its image is anti-diagonal. Its conjugate
of the canonical path radical is the radical of the actual reflected path,
and its image contains every lower unipotent parameter. Both roots and the
full Cartan are therefore marked simultaneously in the original actor.

In the centerless source branch, the full kernel is natural and every upper
parameter lifts to an involution in the canonical path root. Actual opposite
root elements form cubic pairs with trivial common centralizer in the core,
and their braid correction uses the same chosen reflection and full Cartan.
The reflection is conjugate inside the actor to an involution of the canonical
root, without aligning the profile's separately supplied path. The source
parameter is exactly three. This does not yet construct NaturalPathCoordinates
on the canonical length-six exchange paths: the remaining step transports
this path pair, actor, quotient, and reversing reflection to their midpoints.
No assertion about a natural full kernel in the r=4 central branch is made.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156--157,
and (14.12)--(14.13), pp.217--218.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
/-- The same chosen source reflection has an anti-diagonal image in the constructed marking. -/
theorem fullCartanReflections_marked_image (j : Bool) (m : SL(2,(ds j).F))
    (hdiag : ∀ k : universalBOneActor h j (ds j).data, (k:(reducedAmalgam L S).Universal)∈cartan c →
      ∃ a : (ds j).F, ∃ ha : a≠0, m*universalBOneQuotient h j (ds j).data k*m⁻¹=
        Matrix.SpecialLinearGroup.diag2 a ha)
    (hfull : ∀ a : (ds j).F, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
      ((cartan c).subgroupOf (universalBOneActor h j (ds j).data)).map
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data))) :
    ∃ a : (ds j).F, a≠0 ∧
      ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data))
        ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩=
          upper a*lower a⁻¹*upper a := by
  let A := reducedAmalgam L S
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let t : H := ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩
  have htt : t*t=1 := Subtype.ext (fullCartanReflections_square ds j)
  have hπt : π t≠1 := by
    intro he
    have htQ : t∈π.ker := he
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq] at htQ
    have hvQ : (t:A.Universal)∈(MulAction.stabilizer A.Universal
        (base (Universal.cosetFamily A) j)).pCoreIn 2 := by
      rw [stabilizer_base]
      exact htQ
    apply fullCartanReflections_move ds j
    exact universal_vertex_core_fixes_neighbors h _ _
      ⟨by change j≠!j; cases j <;> decide,incident_base _ _ _⟩ hvQ
  obtain ⟨k,hk,hπk⟩ := hfull (ds j).diagonal_parameter (ds j).diagonal_ne_zero
  have hkt : ((t*k*t⁻¹ : H):A.Universal)∈cartan c :=
    (mem_normalizer_iff.mp (fullCartanReflections_normalize ds j) k).mp hk
  obtain ⟨b,hb,he⟩ := hdiag (t*k*t⁻¹) hkt
  apply braid_of_diagonal_normalizing_involution (π t)
    (by rw [←map_mul,htt,map_one]) hπt (ds j).diagonal_parameter
      (ds j).diagonal_ne_zero (ds j).diagonal_ne_one b hb
  change π (t*k*t⁻¹)=Matrix.SpecialLinearGroup.diag2 b hb at he
  change π k=Matrix.SpecialLinearGroup.diag2 (ds j).diagonal_parameter (ds j).diagonal_ne_zero at hπk
  simpa only [map_mul,map_inv,hπk] using he


/-- Reflect the actual canonical path using its own chosen endpoint reflection. -/
def fullCartanOppositePath (j : Bool) :=
  let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
    (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
    (fullCartanPathLength ds) (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) j
  (p.walk.map (⟨(fullCartanReflections ds j • ·),
    source_action (reducedAmalgam L S) (fullCartanReflections ds j)⟩ :
      sourceGraph (reducedAmalgam L S) →g sourceGraph (reducedAmalgam L S))).copy
        rfl (fullCartanReflections_fix ds j)

/-- The opposite subgroup is literally the radical of the reflected path. -/
theorem fullCartanOppositePath_root (j : Bool) :
    pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j) =
      ((fullCartanPathRoots ds j).root).map (MulAut.conj (fullCartanReflections ds j)).toMonoidHom := by
  rw [fullCartanRoots_root]
  symm
  apply pathRoot_map_conj
  · simp only [fullCartanOppositePath,SimpleGraph.Walk.length_copy,SimpleGraph.Walk.length_map]
  · intro k _
    simp only [fullCartanOppositePath,SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_map]
    rfl

/-- Construct both full opposite root images and the full Cartan in one original actor marking. -/
theorem fullCartanRoots_opposite_coordinates (j : Bool) :
    ∃ m : SL(2,(ds j).F),
      (((fullCartanPathRoots ds j).root).subgroupOf (universalBOneActor h j (ds j).data)).map
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)) =
          Matrix.SpecialLinearGroup.upperUnipotent (ds j).F ∧
      (∀ a : (ds j).F, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
        ((cartan c).subgroupOf (universalBOneActor h j (ds j).data)).map
          ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data))) ∧
      pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j) ≤
        universalBOneActor h j (ds j).data ∧
      (∀ y : universalBOneActor h j (ds j).data,
        (y:(reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal)
          (fullCartanOppositePath ds j) →
        ∃ a : (ds j).F, ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)) y=lower a) ∧
      (∀ a : (ds j).F, ∃ y : universalBOneActor h j (ds j).data,
        (y:(reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal)
          (fullCartanOppositePath ds j) ∧
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)) y=lower a) ∧
      (∃ a : (ds j).F, a≠0 ∧
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data))
          ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩=
            upper a*lower a⁻¹*upper a) := by
  obtain ⟨hR,hdis,m,himage,hfull,hdiag⟩ := fullCartanRoots_source_coordinates ds j
  obtain ⟨a,ha,ht⟩ := fullCartanReflections_marked_image ds j m hdiag hfull
  let A := reducedAmalgam L S
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let t : H := ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩
  have htπ : π t=upper a*lower a⁻¹*upper a := ht
  have image (x : H) (b : (ds j).F) (hx : π x=upper b) :
      π (t*x*t⁻¹)=lower (a⁻¹^2*b) := by
    rw [map_mul,map_mul,map_inv,hx,htπ,braid_conjugates_upper _ ha]
  have hxroot (x : H) (hx : (x:A.Universal)∈(fullCartanPathRoots ds j).root) :
      ((t*x*t⁻¹ : H):A.Universal)∈pathRoot (X := A.Universal) (fullCartanOppositePath ds j) := by
    rw [fullCartanOppositePath_root]
    exact ⟨x,hx,rfl⟩
  refine ⟨m,himage,hfull,?_,?_,?_,a,ha,htπ⟩
  · rw [fullCartanOppositePath_root]
    rintro y ⟨x,hx,rfl⟩
    exact H.mul_mem (H.mul_mem t.property (hR hx)) (H.inv_mem t.property)
  · intro y hy
    rw [fullCartanOppositePath_root] at hy
    obtain ⟨x,hx,hxy⟩ := hy
    let xH : H := ⟨x,hR hx⟩
    have hyH : t*xH*t⁻¹=y := Subtype.ext hxy
    have hm : π xH∈Matrix.SpecialLinearGroup.upperUnipotent (ds j).F := by
      rw [←himage]
      exact mem_map_of_mem π hx
    obtain ⟨b,hb⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mp hm
    exact ⟨a⁻¹^2*b,hyH ▸ image xH b hb.symm⟩
  · intro b
    have hm : upper (a^2*b)∈(((fullCartanPathRoots ds j).root).subgroupOf H).map π := by
      rw [show (((fullCartanPathRoots ds j).root).subgroupOf H).map π=
        Matrix.SpecialLinearGroup.upperUnipotent (ds j).F from himage]
      exact (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨a^2*b,rfl⟩
    obtain ⟨x,hx,hπx⟩ := hm
    refine ⟨t*x*t⁻¹,hxroot x hx,?_⟩
    rw [image x (a^2*b) hπx]
    congr 1
    rw [←mul_assoc,←mul_pow,inv_mul_cancel₀ ha,one_pow,one_mul]

/-- In the centerless r=3 branch, construct the natural kernel and actual involution lifts of every upper parameter. -/
theorem fullCartanRoots_source_natural_coordinates
    (hcenter : ∀ j, centerIn (ds j).data.actor=⊥) (j : Bool) :
    fullCartanPathLength ds=3 ∧
    ∃ m : SL(2,(ds j).F),
      Nonempty (NaturalKernel ((MulAut.conj m).toMonoidHom.comp
        (universalBOneQuotient h j (ds j).data))) ∧
      (∀ a : (ds j).F, ∃ x : universalBOneActor h j (ds j).data,
        (x:(reducedAmalgam L S).Universal)∈(fullCartanPathRoots ds j).root ∧
          ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)) x=upper a ∧
          x*x=1) ∧
      (∀ a : (ds j).F, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
        ((cartan c).subgroupOf (universalBOneActor h j (ds j).data)).map
          ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data))) := by
  obtain ⟨hR,hdis,m,himage,hfull,hdiag⟩ := fullCartanRoots_source_coordinates ds j
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
  have hcore : CFSG.Quasithin.ChapterF.Source.DGS85.Q (reducedFamily L S) (base (reducedFamily L S) j)=
      Z (reducedFamily L S) (base (reducedFamily L S) j) := by
    cases j
    · exact hc.1
    · exact hc.2
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let R := ((fullCartanPathRoots ds j).root).subgroupOf H
  have hker : R ⊓ π.ker=⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq]
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hx' : (x:(reducedAmalgam L S).Universal)∈(fullCartanPathRoots ds j).root ⊓
        (Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2 := ⟨hx.1,hx.2⟩
    rwa [hdis,mem_bot] at hx'
  refine ⟨fullCartanPathLength_eq_three_of_center_eq_bot ds (hcenter false),m,
    ⟨(universalBOneNaturalKernel h j (ds j).data hcore (hcenter j) (ds j).dimension).marking m⟩,?_,hfull⟩
  intro a
  have ha : upper a∈R.map π := by
    rw [show R.map π=Matrix.SpecialLinearGroup.upperUnipotent (ds j).F from himage]
    exact (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨a,rfl⟩
  obtain ⟨x,hx,hπx⟩ := ha
  exact ⟨x,hx,hπx,square_of_image_upper π R hker x hx a hπx⟩

/-- The actual opposite path radicals supply the cubic pair and trivial
common centralizer used in DGS (14.12)--(14.13), including the correction
relative to the same chosen reflection and full Cartan. -/
theorem fullCartanRoots_source_cubic_pairs (j : Bool)
    (hcenter : centerIn (ds j).data.actor=⊥)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hxne : x≠1) :
    ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j),
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      (x*y*x)*(fullCartanReflections ds j)⁻¹∈
        (Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2 ⊔ cartan c ∧
      ∀ z∈(Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2,
        Commute x z → Commute y z → z=1 := by
  obtain ⟨hR,hdis,_⟩ := fullCartanRoots_source_coordinates ds j
  obtain ⟨m,himage,hfull,hS,_,hlower,b,hb,ht⟩ := fullCartanRoots_opposite_coordinates ds j
  let A := reducedAmalgam L S
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let Q := (Universal.cosetFamily A j).pCoreIn 2
  let R := ((fullCartanPathRoots ds j).root).subgroupOf H
  let R' := (pathRoot (X := A.Universal) (fullCartanOppositePath ds j)).subgroupOf H
  let t : H := ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩
  have hker : π.ker=Q.subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq]
  have hQH : Q≤H := universalBOne_core_le h j (ds j).data
  have disjoint_kernel (U : Subgroup A.Universal) (hU : U⊓Q=⊥) :
      U.subgroupOf H ⊓ π.ker=⊥ := by
    rw [hker]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hh : (z:A.Universal)∈U⊓Q := ⟨hz.1,hz.2⟩
    rwa [hU,mem_bot] at hh
  have htQ : (t:A.Universal)∈normalizer (Q : Set A.Universal) := by
    have hn := vertexCore_normalized (X := A.Universal) (base (Universal.cosetFamily A) j)
    rw [stabilizer_base] at hn
    exact hn t.property.2
  have hQmap : Q.map (MulAut.conj (t:A.Universal)).toMonoidHom=Q :=
    mem_normalizer_iff_map_conj_eq.mp htQ
  have hSdis : pathRoot (X := A.Universal) (fullCartanOppositePath ds j) ⊓ Q=⊥ := by
    rw [fullCartanOppositePath_root]
    calc
      _ = (((fullCartanPathRoots ds j).root) ⊓ Q).map
          (MulAut.conj (t:A.Universal)).toMonoidHom := by
        rw [Subgroup.map_inf _ _ _ (MulAut.conj (t:A.Universal)).injective,hQmap]
      _ = ⊥ := by rw [show ((fullCartanPathRoots ds j).root) ⊓ Q=⊥ from hdis,Subgroup.map_bot]
  have hupper (u : H) (hu : u∈R) : ∃ a : (ds j).F, π u=upper a := by
    have hm : π u∈Matrix.SpecialLinearGroup.upperUnipotent (ds j).F := by
      rw [←himage]
      exact mem_map_of_mem π hu
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mp hm
    exact ⟨a,ha.symm⟩
  have hcore : CFSG.Quasithin.ChapterF.Source.DGS85.Q (reducedFamily L S) (base (reducedFamily L S) j)=
      Z (reducedFamily L S) (base (reducedFamily L S) j) := by
    have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
    cases j
    · exact hc.1
    · exact hc.2
  let nat := (universalBOneNaturalKernel h j (ds j).data hcore hcenter (ds j).dimension).marking m
  let xx : H := ⟨x,hR hx⟩
  obtain ⟨a,ha,hπx,y,hy,hπy,hxx,hyy,horder,hcentral⟩ :=
    pair_of_opposite_images π nat R R' (disjoint_kernel _ hdis)
      (disjoint_kernel _ hSdis) hupper hlower xx hx
      (fun he => hxne (congrArg H.subtype he))
  have hcor := correction_mem π ((cartan c).subgroupOf H) a b ha hb xx y t hπx hπy ht hfull
  have hcorX : (x*(y:A.Universal)*x)*(fullCartanReflections ds j)⁻¹∈Q⊔cartan c := by
    have hm := mem_map_of_mem H.subtype hcor
    rw [Subgroup.map_sup,hker,map_subgroupOf_eq_of_le hQH] at hm
    exact (sup_le_sup_left (show ((cartan c).subgroupOf H).map H.subtype≤cartan c by
      rw [subgroupOf_map_subtype]; exact inf_le_left) Q) hm
  refine ⟨y,hy,congrArg H.subtype hxx,congrArg H.subtype hyy,?_,hcorX,?_⟩
  · exact (orderOf_injective H.subtype Subtype.coe_injective (xx*y)).trans horder
  · intro z hz hxz hyz
    let zz : H := ⟨z,hQH hz⟩
    have hzker : zz∈π.ker := by rw [hker]; exact hz
    have hxz' : Commute xx zz := Subtype.ext hxz.eq
    have hyz' : Commute y zz := Subtype.ext hyz.eq
    exact congrArg H.subtype (hcentral zz hzker hxz' hyz')

/-- In the original centerless branch, the chosen reflection is conjugate
inside the same actor to an involution of its actual canonical path root.
No alignment of the profile's separately supplied path is needed. -/
theorem fullCartanRoots_source_conjugacy_of_center_eq_bot (j : Bool)
    (hcenter : centerIn (ds j).data.actor=⊥) :
    ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
      ∃ g∈universalBOneActor h j (ds j).data,
        g*x*g⁻¹=fullCartanReflections ds j := by
  obtain ⟨hR,hdis,_⟩ := fullCartanRoots_source_coordinates ds j
  obtain ⟨m,himage,_,_,_,hlower,b,hb,ht⟩ := fullCartanRoots_opposite_coordinates ds j
  let A := reducedAmalgam L S
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let R := ((fullCartanPathRoots ds j).root).subgroupOf H
  let t : H := ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩
  have htt : t*t=1 := Subtype.ext (fullCartanReflections_square ds j)
  have hker : R⊓π.ker=⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hh : (z:A.Universal)∈(fullCartanPathRoots ds j).root ⊓
        (Universal.cosetFamily A j).pCoreIn 2 := ⟨hz.1,hz.2⟩
    rwa [hdis,mem_bot] at hh
  have hu : upper b∈R.map π := by
    rw [show R.map π=Matrix.SpecialLinearGroup.upperUnipotent (ds j).F from himage]
    exact (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨b,rfl⟩
  obtain ⟨x,hx,hπx⟩ := hu
  have hxx := square_of_image_upper π R hker x hx b hπx
  have hxne : x≠1 := by
    intro he
    have hh := congrArg (fun z : SL(2,(ds j).F) => z.val 0 1) hπx
    rw [he,map_one] at hh
    exact hb (by simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh.symm)
  obtain ⟨y,_,hπy⟩ := hlower b⁻¹
  let v := y*x*y⁻¹
  have hvv : v*v=1 := by
    dsimp [v]
    calc
      _ = y*(x*x)*y⁻¹ := by group
      _ = 1 := by rw [hxx,mul_one,mul_inv_cancel]
  have hπv : π v=upper b*lower b⁻¹*upper b := by
    change π (y*x*y⁻¹)=_
    rw [map_mul,map_mul,map_inv,hπx,hπy,lower_conjugates_upper _ hb]
  have hcore : Q (reducedFamily L S) (base (reducedFamily L S) j)=
      Z (reducedFamily L S) (base (reducedFamily L S) j) := by
    have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
    cases j
    · exact hc.1
    · exact hc.2
  let nat := (universalBOneNaturalKernel h j (ds j).data hcore hcenter (ds j).dimension).marking m
  obtain ⟨z,hz⟩ := nat.reflection_fiber_conjugate v t hvv htt (ht.trans hπv.symm) b hb hπv
  have hg : ((z:H)*y)*x*((z:H)*y)⁻¹=t := by
    calc
      _ = (z:H)*v*(z:H)⁻¹ := by dsimp [v]; group
      _ = t := hz
  refine ⟨x,hx,?_,((z:H)*y),((z:H)*y).property,congrArg H.subtype hg⟩
  rw [Subgroup.orderOf_coe]
  exact orderOf_eq_prime (by simpa only [pow_two] using hxx) hxne

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
