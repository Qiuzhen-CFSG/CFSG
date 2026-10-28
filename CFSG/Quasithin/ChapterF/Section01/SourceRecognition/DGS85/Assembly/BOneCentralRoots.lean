module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneOppositeCoordinates
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCentralCubic

/-!
# Canonical b=1 roots with the full central natural quotient

Keep the original endpoint actor and its literal two-core quotient. The
canonical path radical is disjoint from that kernel, so each upper parameter
lifts to an involution. Adjust the chosen whole-Cartan reflection inside
its Cartan coset to match this parameter. Its reflected root then forms
an actual cubic pair, using the sixth-power calculation in the central
natural extension. The braid has an explicit central involution defect.

For the original chosen reflection, this also constructs conjugacy to a
central translate of an involution in the same long-path root. The natural
coordinate kernel is exactly the full actor center; in the r=4 source
alternative that center has order q. Thus the common core centralizer of
the cubic pair is retained, and no natural action on the full core or
centerless exchange conclusion is asserted.

BOneCentralGeometry applies all four results to the original nonsolvable
critical pair, and BOneCentralGeometryConsumers to Chapter 12.
Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157,
and the local calculations of (14.12)--(14.15), pp.217--220.
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
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S

include ds in
private theorem source_core_eq_center (j : Bool) :
    Q (reducedFamily L S) (base (reducedFamily L S) j)=
      Z (reducedFamily L S) (base (reducedFamily L S) j) := by
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
  cases j
  · exact hc.1
  · exact hc.2

private theorem source_kernel_square (j : Bool) (m : SL(2,(ds j).F))
    (z : ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)).ker) :
    z*z=1 := by
  let H := universalBOneActor h j (ds j).data
  let e := universalBOneActorEquiv h j (ds j).data
  have hzker : e (z:H)∈(ds j).data.quotient.ker := by
    apply (MulAut.conj m).injective
    exact z.property.trans (map_one _).symm
  rw [(ds j).data.kernel,source_core_eq_center ds j] at hzker
  have hs := ((mem_omegaCenterIn_iff _ _).mp
    ((source_Z_Q_U (reduced_triple h) (base (reducedFamily L S) j)).1 hzker)).2.2
  apply Subtype.ext
  apply e.injective
  apply Subtype.ext
  simpa only [Subgroup.coe_mul,Subgroup.coe_one,map_mul,map_one,pow_two,Subgroup.subtype_apply] using hs

private theorem source_root_normalized (j : Bool) :
    cartan c≤normalizer ((fullCartanPathRoots ds j).root : Set (reducedAmalgam L S).Universal) := by
  let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
    (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
    (fullCartanPathLength ds) (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) j
  rw [fullCartanRoots_root]
  have hn := (pCore 2 (pathFixer (X := (reducedAmalgam L S).Universal) p.walk)).le_normalizer_map
    (pathFixer (X := (reducedAmalgam L S).Universal) p.walk).subtype
  have hn' : pathFixer (X := (reducedAmalgam L S).Universal) p.walk≤
      normalizer (pathRoot (X := (reducedAmalgam L S).Universal) p.walk : Set (reducedAmalgam L S).Universal) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,pathRoot,pCoreIn] using hn
  exact p.fixed.trans hn'

/-- Every actual canonical root involution has an opposite cubic partner.
The braid retains its actual central correction and the whole source Cartan;
the common centralizer in the endpoint core is exactly the actor center. -/
theorem central_root_pairs (j : Bool) (x : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hxne : x≠1) :
    ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j),
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      (∃ z∈centerIn (universalBOneActor h j (ds j).data),
        z∈(Universal.cosetFamily A j).pCoreIn 2 ∧ z*z=1 ∧
        ∃ k∈cartan c, x*y*x=z*k*fullCartanReflections ds j) ∧
      ∀ z∈(Universal.cosetFamily A j).pCoreIn 2,
        (Commute x z ∧ Commute y z ↔ z∈centerIn (universalBOneActor h j (ds j).data)) := by
  obtain ⟨hR,hdis,m,himage,hfull,hdiag⟩ := fullCartanRoots_source_coordinates ds j
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let R := ((fullCartanPathRoots ds j).root).subgroupOf H
  let K := (cartan c).subgroupOf H
  let t : H := ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩
  have htt : t*t=1 := Subtype.ext (fullCartanReflections_square ds j)
  have hker : π.ker=((Universal.cosetFamily A j).pCoreIn 2).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq]
  have hRker : R⊓π.ker=⊥ := by
    rw [hker]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hh : (z:(reducedAmalgam L S).Universal)∈(fullCartanPathRoots ds j).root ⊓
        (Universal.cosetFamily A j).pCoreIn 2 := ⟨hz.1,hz.2⟩
    rwa [hdis,mem_bot] at hh
  let nat := (universalBOneNaturalCentralKernel h j (ds j).data
    (source_core_eq_center ds j) (ds j).dimension).conj m
  let : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  let : Finite (ds j).data.actor := Finite.of_injective
    (inclusion (ds j).data.actor_le) (inclusion_injective _)
  let : Finite H := Finite.of_equiv (ds j).data.actor
    (universalBOneActorEquiv h j (ds j).data).symm.toEquiv
  have hKker : K⊓π.ker=⊥ := by
    have hodd : Nat.Coprime 2 (Nat.card K) := by
      apply (cartan_odd c).of_dvd_right
      have he := card_map_of_injective (f := H.subtype) (K := K) H.subtype_injective
      rw [←he,subgroupOf_map_subtype]
      exact card_dvd_of_le inf_le_left
    obtain ⟨n,hn⟩ := nat.isTwo.exists_card_eq
    exact (disjoint_of_coprime_natCard (by rw [hn]; exact hodd.symm.pow_right n)).eq_bot
  have htN : t∈normalizer (K : Set H) :=
    (cartan c).le_normalizer_comap H.subtype (fullCartanReflections_normalize ds j)
  obtain ⟨b,hb,ht⟩ := fullCartanReflections_marked_image ds j m hdiag hfull
  let xx : H := ⟨x,hR hx⟩
  have hm : π xx∈Matrix.SpecialLinearGroup.upperUnipotent (ds j).F := by
    rw [←himage]
    exact mem_map_of_mem π hx
  obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mp hm
  have hπx : π xx=upper a := ha.symm
  have ha0 : a≠0 := by
    intro he
    exact hxne (congrArg H.subtype (eq_one_of_root_kernel π R hRker xx hx
      (by simpa [he,upper,Matrix.SpecialLinearGroup.transvection_coeff_zero] using hπx)))
  have hxx := square_of_image_upper π R hRker xx hx a hπx
  obtain ⟨k,hk,huu,hπu⟩ := reflection_with_parameter π K hKker t htN htt b hb ht hfull a ha0
  let u := k*t
  let y := u*xx*u⁻¹
  obtain ⟨hyy,hπy,horder,hcentral,hcent⟩ := nat.reflected_pair
    (source_kernel_square ds j m) xx u hxx huu a ha0 hπx hπu
  have hy : (y:(reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j) := by
    rw [fullCartanOppositePath_root]
    let k' := t⁻¹*k*t
    have hk' : k'∈K := by
      have hh := (mem_normalizer_iff.mp ((normalizer (K : Set H)).inv_mem htN) k).mp hk
      simpa only [inv_inv] using hh
    have hr : ((k'*xx*k'⁻¹ : H):(reducedAmalgam L S).Universal)∈(fullCartanPathRoots ds j).root :=
      (mem_normalizer_iff.mp (source_root_normalized ds j hk') x).mp hx
    refine ⟨k'*xx*k'⁻¹,hr,?_⟩
    change (t:(reducedAmalgam L S).Universal)*((k'*xx*k'⁻¹:H):(reducedAmalgam L S).Universal)*(t:(reducedAmalgam L S).Universal)⁻¹=(y:(reducedAmalgam L S).Universal)
    simp only [y,u,k',Subgroup.coe_mul,Subgroup.coe_inv]
    group
  let z := (xx*y*xx)*u⁻¹
  have hzQ : (z:(reducedAmalgam L S).Universal)∈(Universal.cosetFamily A j).pCoreIn 2 := by
    have hz : z∈π.ker := hcentral.1
    rwa [hker] at hz
  have hzC : (z:(reducedAmalgam L S).Universal)∈centerIn H := by
    rw [centerIn_eq_map_center]
    exact mem_map_of_mem H.subtype hcentral.2
  have hzsq := congrArg (fun w : π.ker => ((w:H):(reducedAmalgam L S).Universal))
    (source_kernel_square ds j m ⟨z,hcentral.1⟩)
  refine ⟨y,hy,congrArg H.subtype hxx,congrArg H.subtype hyy,
    (orderOf_injective H.subtype Subtype.coe_injective (xx*y)).trans horder,?_,?_⟩
  · refine ⟨z,hzC,hzQ,hzsq,k,hk,?_⟩
    change (xx:H).val*(y:H).val*(xx:H).val=(z:H).val*(k:H).val*(t:H).val
    simp only [z,u,Subgroup.coe_mul,Subgroup.coe_inv]
    group
  · intro w hw
    let ww : H := ⟨w,universalBOne_core_le h j (ds j).data hw⟩
    have hwker : ww∈π.ker := by rw [hker]; exact hw
    constructor
    · rintro ⟨hxw,hyw⟩
      have hc := (hcent ww hwker).mp ⟨Subtype.ext hxw.eq,Subtype.ext hyw.eq⟩
      rw [centerIn_eq_map_center]
      exact mem_map_of_mem H.subtype hc
    · intro hc
      exact ⟨hc.2 x (hR hx),hc.2 y y.property⟩



/-- The original chosen reflection is conjugate to a central translate of
an involution in its literal canonical path root. No alignment of the
profile's initial edge with the long path is assumed. -/
theorem central_root_conjugacy (j : Bool) :
    ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
      ∃ z∈centerIn (universalBOneActor h j (ds j).data),
        z∈(Universal.cosetFamily A j).pCoreIn 2 ∧ z*z=1 ∧
        ∃ g∈universalBOneActor h j (ds j).data,
          g*(z*x)*g⁻¹=fullCartanReflections ds j := by
  obtain ⟨hR,hdis,m,himage,hfull,hdiag⟩ := fullCartanRoots_source_coordinates ds j
  obtain ⟨a,ha,ht⟩ := fullCartanReflections_marked_image ds j m hdiag hfull
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let R := ((fullCartanPathRoots ds j).root).subgroupOf H
  let t : H := ⟨fullCartanReflections ds j,(fullCartanReflections_source_clauses ds j).1⟩
  have hker : π.ker=((Universal.cosetFamily A j).pCoreIn 2).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq]
  have hRker : R⊓π.ker=⊥ := by
    rw [hker]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    have hh : (z:(reducedAmalgam L S).Universal)∈(fullCartanPathRoots ds j).root ⊓
        (Universal.cosetFamily A j).pCoreIn 2 := ⟨hz.1,hz.2⟩
    rwa [hdis,mem_bot] at hh
  have hu : upper a∈R.map π := by
    rw [show R.map π=Matrix.SpecialLinearGroup.upperUnipotent (ds j).F from himage]
    exact (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨a,rfl⟩
  obtain ⟨x,hx,hπx⟩ := hu
  have hxx := square_of_image_upper π R hRker x hx a hπx
  have hxne : x≠1 := by
    intro he
    have hh := congrArg (fun w : SL(2,(ds j).F) => w.val 0 1) hπx
    rw [he,map_one] at hh
    exact ha (by simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh.symm)
  let nat := (universalBOneNaturalCentralKernel h j (ds j).data
    (source_core_eq_center ds j) (ds j).dimension).conj m
  have htt : t*t=1 := Subtype.ext (fullCartanReflections_square ds j)
  obtain ⟨_,_,_,hc,_⟩ := nat.reflected_pair (source_kernel_square ds j m) x t hxx htt a ha hπx ht
  let z := (x*(t*x*t⁻¹)*x)*t⁻¹
  have hzker : z∈π.ker := hc.1
  have hzsq : z*z=1 := congrArg (fun w : π.ker => (w:H)) (source_kernel_square ds j m ⟨z,hzker⟩)
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right hxx
  have hzcomm : (x*t)*z=z*(x*t) := Subgroup.mem_center_iff.mp hc.2 (x*t)
  have hg : (x*t)*(z*x)*(x*t)⁻¹=t := by
    calc
      _ = ((x*t)*z)*x*(x*t)⁻¹ := by group
      _ = (z*(x*t))*x*(x*t)⁻¹ := by rw [hzcomm]
      _ = z*((x*t)*x*(x*t)⁻¹) := by group
      _ = z*(x*(t*x*t⁻¹)*x) := by rw [_root_.mul_inv_rev,hxi]; group
      _ = z*(z*t) := by dsimp [z]; group
      _ = t := by rw [←mul_assoc,hzsq,one_mul]
  have hzC : (z:(reducedAmalgam L S).Universal)∈centerIn H := by
    rw [centerIn_eq_map_center]
    exact mem_map_of_mem H.subtype hc.2
  have hzQ : (z:(reducedAmalgam L S).Universal)∈(Universal.cosetFamily A j).pCoreIn 2 := by
    rwa [hker] at hzker
  exact ⟨x,hx,(Subgroup.orderOf_coe x).trans (orderOf_eq_prime
    (by simpa only [pow_two] using hxx) hxne),z,hzC,hzQ,congrArg H.subtype hzsq,
    x*t,(x*t).property,congrArg H.subtype hg⟩

/-- The coordinates have exactly the full actor center as denominator.
They retain the original quotient, core and natural action, including r=4. -/
theorem central_kernel_coordinates (j : Bool) :
    ∃ d : NaturalCentralKernel (universalBOneQuotient h j (ds j).data),
      ∀ z : (universalBOneQuotient h j (ds j).data).ker,
        d.coordinates z=1 ↔ (z:universalBOneActor h j (ds j).data)∈
          center (universalBOneActor h j (ds j).data) := by
  let d := universalBOneNaturalCentralKernel h j (ds j).data
    (source_core_eq_center ds j) (ds j).dimension
  refine ⟨d,?_⟩
  intro z
  constructor
  · exact d.central z
  · intro hz
    obtain ⟨k,hk⟩ := ((ds j).data.onto.comp (universalBOneActorEquiv h j (ds j).data).surjective)
      (Matrix.SpecialLinearGroup.diag2 (ds j).diagonal_parameter (ds j).diagonal_ne_zero)
    exact d.coordinates_eq_one_of_commute_diagonal z k (ds j).diagonal_parameter
      (ds j).diagonal_ne_zero (ds j).diagonal_ne_one hk (Subgroup.mem_center_iff.mp hz k)

/-- In the r=4 alternative both actual universal actor centers retain
order q. In particular the central denominator cannot be discarded. -/
theorem central_actor_card_of_r_four
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5)
    (j : Bool) : Nat.card (centerIn (universalBOneActor h j (ds j).data))=Nat.card (ds j).F := by
  have hc : ∀ j, Nat.card (centerIn (ds j).data.actor)=Nat.card (ds j).F := by
    rcases original_bOne_tree_path_alternatives h (ds false).data (ds true).data
      (ds false).actor_eq (ds true).actor_eq (ds false).dimension (ds true).dimension with
      ⟨_,_,hp,_,_⟩ | ⟨hc₀,hc₁,_,_,_⟩
    · have he := hr.1.unique hp.1
      omega
    · rw [←reduced_actor_center_map,card_map_of_injective (G₀ L S).subtype_injective] at hc₀ hc₁
      intro i
      cases i
      · exact hc₀
      · exact hc₁
  rw [centerIn_eq_map_center,card_map_of_injective Subtype.coe_injective]
  rw [Nat.card_congr (Subgroup.centerCongr (universalBOneActorEquiv h j (ds j).data)).toEquiv]
  have hh := hc j
  rwa [centerIn_eq_map_center,card_map_of_injective Subtype.coe_injective] at hh

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
