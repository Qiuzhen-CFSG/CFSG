module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralRoots
public import Theory.GroupTheory.WeakBNPair.RegularTree.RootCartanTransitivity

/-!
# Vanishing of the central braid correction in the original natural branch

The full centers lie in both adjacent two-cores and meet trivially by the
faithfulness of the original pair. A nonidentity diagonal from the opposite
actor therefore fixes no nonidentity element of the first center.

Adjust that diagonal by the first actor Cartan to centralize one nonzero
path-root element. Cartan transitivity makes it centralize the entire root,
so it fixes all neighbors and commutes with the chosen reflection by its
full local-kernel clause. The cubic braid then makes it centralize its own
central correction. The opposite diagonal argument kills that correction.
The r=4 center of order q and its Q/Z natural action remain unchanged.

The parameter-matched braid also proves actual root-reflection conjugacy.
BOneCentralExchange applies the resulting exact braid to actual apartment
paths. This is the characteristic-two natural branch of DGS (14.15),
using (10.5) and the local algebra of (14.5), (14.12): Groups and Graphs
(1985), pp.156--157,213--214,217--219. Other source rows are not asserted.
-/

@[expose] public noncomputable section
open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

open Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S

include ds in
private theorem core_eq_Z (j : Bool) :
    Q (reducedFamily L S) (base (reducedFamily L S) j)=
      Z (reducedFamily L S) (base (reducedFamily L S) j) := by
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
  cases j
  · exact hc.1
  · exact hc.2

private theorem center_image (j : Bool) (z : (reducedAmalgam L S).Universal)
    (hz : z∈centerIn ((universalBOneActor h j (ds j).data))) : bOne_tree_map h z∈centerIn (ds j).data.actor := by
  let e := universalBOneActorEquiv h j (ds j).data
  have hz' : (⟨z,hz.1⟩ : (universalBOneActor h j (ds j).data))∈center ((universalBOneActor h j (ds j).data)) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (hz.2 y y.property)
  have he := MulEquivClass.apply_mem_center e hz'
  refine ⟨hz.1.1,?_⟩
  intro y hy
  exact congrArg (ds j).data.actor.subtype (Subgroup.mem_center_iff.mp he ⟨y,hy⟩)

theorem universal_centers_disjoint : Disjoint (centerIn ((universalBOneActor h false (ds false).data))) (centerIn ((universalBOneActor h true (ds true).data))) := by
  have hn (j : Bool) : (B₀ L S).subgroupOf (G₀ L S)≤normalizer ((ds j).data.actor : Set (G₀ L S)) := by
    rw [(ds j).actor_eq]
    exact reduced_borel_normalizes_source_actor h _
  have hd := paired_actor_centers_disjoint (reduced_triple h) (ds false).data (ds true).data
    (hn false) (hn true)
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  intro z hz
  have he : bOne_tree_map h z=1 := hd.le_bot ⟨center_image ds false z hz.1,center_image ds true z hz.2⟩
  have hh := (bOne_tree_cover h).injective false
    (a₁ := ⟨z,hz.1.1.2⟩) (a₂ := 1) (he.trans (map_one _).symm)
  exact congrArg Subtype.val hh

theorem universal_center_le_cores (j : Bool) :
    centerIn ((universalBOneActor h j (ds j).data))≤(Universal.cosetFamily A j).pCoreIn 2 ⊓
      (Universal.cosetFamily A (!j)).pCoreIn 2 := by
  intro z hz
  have hm := actor_center_le_cores (ds j).data (reduced_triple h) (core_eq_Z ds j)
    (center_image ds j z hz)
  have hzQ := (universalBOne_mem_core_iff h j z hz.1.2).mp hm.1
  have hzN : z∈Universal.cosetFamily A (!j) := by
    rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !j)]
    exact universal_vertex_core_fixes_neighbors h _ _
      (show (sourceGraph A).Adj (base (Universal.cosetFamily A) j)
        (base (Universal.cosetFamily A) (!j)) from
        ⟨by change j≠!j; cases j <;> decide,incident_base _ _ _⟩)
      (by simpa only [stabilizer_base] using hzQ)
  exact ⟨hzQ,(universalBOne_mem_core_iff h (!j) z hzN).mp hm.2⟩

/-- A nonidentity opposite diagonal has no fixed element in the actual center. -/
theorem opposite_diagonal_centralizer (j : Bool) (k : (universalBOneActor h (!j) (ds (!j)).data))
    (hk : universalBOneQuotient h (!j) (ds (!j)).data k=
      diag2 (ds (!j)).diagonal_parameter (ds (!j)).diagonal_ne_zero)
    (z : (reducedAmalgam L S).Universal) (hz : z∈centerIn ((universalBOneActor h j (ds j).data))) (hcomm : Commute (k:(reducedAmalgam L S).Universal) z) : z=1 := by
  have hzQ := (universal_center_le_cores ds j hz).2
  let zz : (universalBOneActor h (!j) (ds (!j)).data) := ⟨z,universalBOne_core_le h (!j) (ds (!j)).data hzQ⟩
  have hzker : zz∈(universalBOneQuotient h (!j) (ds (!j)).data).ker := by
    rw [universalBOne_kernel_eq]
    exact hzQ
  let d := universalBOneNaturalCentralKernel h (!j) (ds (!j)).data (core_eq_Z ds (!j))
    (ds (!j)).dimension
  have hc := d.central ⟨zz,hzker⟩ (d.coordinates_eq_one_of_commute_diagonal ⟨zz,hzker⟩ k
    (ds (!j)).diagonal_parameter (ds (!j)).diagonal_ne_zero (ds (!j)).diagonal_ne_one hk
    (Subtype.ext hcomm.eq))
  have hc' : z∈centerIn ((universalBOneActor h (!j) (ds (!j)).data)) := by
    rw [centerIn_eq_map_center]
    exact mem_map_of_mem ((universalBOneActor h (!j) (ds (!j)).data)).subtype hc
  have hd := universal_centers_disjoint ds
  cases j
  · exact hd.le_bot ⟨hz,hc'⟩
  · exact hd.le_bot ⟨hc',hz⟩

private theorem root_normalized (j : Bool) :
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

theorem root_cartan_transitive (j : Bool) (x y : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hy : y∈(fullCartanPathRoots ds j).root)
    (hxn : x≠1) (hyn : y≠1) :
    ∃ k∈cartan c, k∈(universalBOneActor h j (ds j).data) ∧ k*x*k⁻¹=y := by
  obtain ⟨hR,hdis,m,himage,hfull,_⟩ := fullCartanRoots_source_coordinates ds j
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  let R := ((fullCartanPathRoots ds j).root).subgroupOf ((universalBOneActor h j (ds j).data))
  let K := (cartan c).subgroupOf ((universalBOneActor h j (ds j).data))
  have hker : π.ker=((Universal.cosetFamily A j).pCoreIn 2).subgroupOf ((universalBOneActor h j (ds j).data)) := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,universalBOne_kernel_eq]
  have hd : R⊓π.ker=⊥ := by
    rw [hker]
    apply le_bot_iff.mp
    intro z hz
    apply Subtype.ext
    exact hdis.le ⟨hz.1,hz.2⟩
  have hn : K≤normalizer (R : Set ((universalBOneActor h j (ds j).data))) := by
    intro k hk
    exact (fullCartanPathRoots ds j).root.le_normalizer_comap ((universalBOneActor h j (ds j).data)).subtype
      (root_normalized ds j hk)
  obtain ⟨k,hk,he⟩ := upper_root_cartan_transitive π R K hd hn himage hfull
    ⟨x,hR hx⟩ ⟨y,hR hy⟩ hx hy
    (fun hh => hxn (congrArg Subtype.val hh)) (fun hh => hyn (congrArg Subtype.val hh))
  exact ⟨k,hk,k.property,congrArg ((universalBOneActor h j (ds j).data)).subtype he⟩

private theorem cartan_fixes_root_vertices (j : Bool) (k : (reducedAmalgam L S).Universal)
    (hk : k∈cartan c) :
    k • (fullCartanPathRoots ds j).a=(fullCartanPathRoots ds j).a ∧
    k • (fullCartanPathRoots ds j).b=(fullCartanPathRoots ds j).b ∧
    k • (fullCartanPathRoots ds j).c=(fullCartanPathRoots ds j).c := by
  have hf := reflectionApartment_fixed c (fullCartanReflections ds) (fullCartanReflections_normalize ds) k hk
  refine ⟨?_,?_,?_⟩
  · rw [fullCartanRoots_a]
    exact hf _ (cartanApartment_base A _ j)
  · rw [fullCartanRoots_b]
    exact hf _ (cartanApartment_base A _ (!j))
  · rw [←(fullCartanPathRoots ds j).sends_b,fullCartanRoots_b,fullCartanRoots_reflection]
    exact hf _ (cartanApartment_preserves A _ (reflectionGroup_mem c _ j)
      (cartanApartment_base A _ (!j)))

/-- Fixing one nonzero root element forces a Cartan element into the full
local permutation kernel, without identifying that kernel with O₂. -/
theorem cartan_mem_localKernel_of_commute_root (j : Bool)
    (x k : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hxn : x≠1)
    (hk : k∈cartan c) (hcomm : Commute k x) :
    k∈RankTwo.ballKernel (Universal.cosetFamily A) (base (Universal.cosetFamily A) j) 1 := by
  let := cartan_abelian h c
  have hR : ∀ r∈(fullCartanPathRoots ds j).root, Commute k r := by
    intro r hr
    by_cases he : r=1
    · rw [he]
      exact Commute.one_right k
    obtain ⟨a,ha,_,har⟩ := root_cartan_transitive ds j x r hx hr hxn he
    rw [←har]
    have hka : Commute k a := setLike_mul_comm hk ha
    exact (hka.mul_right hcomm).mul_right hka.inv_right
  obtain ⟨hka,hkb,hkc⟩ := cartan_fixes_root_vertices ds j k hk
  intro z hz
  rcases (RankTwo.mem_ball_one (Universal.cosetFamily A) _ _).mp hz with hz | rfl
  · have haz : (sourceGraph A).Adj (fullCartanPathRoots ds j).a z := by
      simpa only [fullCartanRoots_a] using hz
    by_cases he : z=(fullCartanPathRoots ds j).b
    · exact he ▸ hkb
    obtain ⟨r,hr,heq⟩ := (fullCartanPathRoots ds j).transitive z haz he
    rw [←heq,←mul_smul,(hR r hr).eq,mul_smul,hkc]
  · simpa only [fullCartanRoots_a] using hka

/-- Correct any whole-Cartan element inside the local actor Cartan so that
it centralizes both the chosen root involution and the actual reflection. -/
theorem cartan_root_adjustment (j : Bool) (x k : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hxn : x≠1) (hk : k∈cartan c) :
    ∃ a∈cartan c, a∈universalBOneActor h j (ds j).data ∧
      Commute (a⁻¹*k) x ∧ Commute (a⁻¹*k) (fullCartanReflections ds j) := by
  have hy := (mem_normalizer_iff.mp (root_normalized ds j hk) x).mp hx
  have hyn : k*x*k⁻¹≠1 := by
    intro he
    apply hxn
    exact (MulAut.conj k).injective (he.trans (map_one _).symm)
  obtain ⟨a,ha,haH,he⟩ := root_cartan_transitive ds j x (k*x*k⁻¹) hx hy hxn hyn
  have hc : Commute (a⁻¹*k) x := by
    have hh : (a⁻¹*k)*x*(a⁻¹*k)⁻¹=x := by
      calc
        _ = a⁻¹*(k*x*k⁻¹)*a := by group
        _ = a⁻¹*(a*x*a⁻¹)*a := by rw [←he]
        _ = x := by group
    exact (mul_inv_eq_iff_eq_mul.mp hh)
  have hK : a⁻¹*k∈cartan c := (cartan c).mul_mem ((cartan c).inv_mem ha) hk
  exact ⟨a,ha,haH,hc,((fullCartanReflections_source_clauses ds j).2.2 _ hK
    (cartan_mem_localKernel_of_commute_root ds j x (a⁻¹*k) hx hxn hK hc)).symm⟩

/-- The central braid defect vanishes by the opposite diagonal action.
The actor center itself is retained and may have order q. -/
theorem central_braid_defect_eq_one (j : Bool)
    (x y z a : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hxn : x≠1)
    (hxx : x*x=1) (hyy : y*y=1) (horder : orderOf (x*y)=3)
    (hz : z∈centerIn (universalBOneActor h j (ds j).data))
    (ha : a∈cartan c) (hbraid : x*y*x=z*a*fullCartanReflections ds j) : z=1 := by
  let := cartan_abelian h c
  obtain ⟨k,hk,hπk⟩ := (ds (!j)).full_diagonal (ds (!j)).diagonal_parameter (ds (!j)).diagonal_ne_zero
  obtain ⟨b,hb,hbH,hcx,hct⟩ := cartan_root_adjustment ds j x k hx hxn hk
  let v := b⁻¹*(k:(reducedAmalgam L S).Universal)
  let u := a*fullCartanReflections ds j
  have hvK : v∈cartan c := (cartan c).mul_mem ((cartan c).inv_mem hb) hk
  have hcu : Commute v u := (show Commute v a from setLike_mul_comm hvK ha).mul_right hct
  have hzx : Commute x z := hz.2 x ((fullCartanRoots_source_coordinates ds j).1 hx)
  have hcub : (x*y)^3=1 := horder ▸ pow_orderOf_eq_one (x*y)
  have hw := (braid_conjugates x y hxx hyy (braid_of_involutions_cube x y hxx hyy hcub)).1
  have hbu : x*y*x=z*u := by simpa only [u,mul_assoc] using hbraid
  have huy : u⁻¹*x*u=y := by
    rw [hbu] at hw
    have he : (z*u)⁻¹*x*(z*u)=u⁻¹*x*u := by
      calc
        _ = u⁻¹*(z⁻¹*(x*z))*u := by group
        _ = u⁻¹*(z⁻¹*(z*x))*u := by rw [hzx.eq]
        _ = _ := by group
    exact he.symm.trans hw
  have hcy : Commute v y := huy ▸ (hcu.inv_right.mul_right hcx).mul_right hcu
  have hzexpr : z=(x*y*x)*u⁻¹ := by rw [hbu]; group
  have hcz : Commute v z := hzexpr ▸ ((hcx.mul_right hcy).mul_right hcx).mul_right hcu.inv_right
  have hbz : Commute b z := hz.2 b hbH
  have hkz : Commute (k:(reducedAmalgam L S).Universal) z := by
    have hh := hbz.mul_left hcz
    simpa only [v,mul_inv_cancel_left] using hh
  exact opposite_diagonal_centralizer ds j k hπk z hz hkz


/-- Both actual half roots form a cubic pair with an exact Cartan-reflection
braid, including the nontrivial-center alternative. -/
theorem root_pairs_exact (j : Bool) (x : (reducedAmalgam L S).Universal)
    (hx : x∈(fullCartanPathRoots ds j).root) (hxn : x≠1) :
    ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j),
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
      ∃ k∈cartan c, x*y*x=k*fullCartanReflections ds j := by
  obtain ⟨y,hy,hxx,hyy,ho,⟨z,hz,_,_,k,hk,he⟩,_⟩ := central_root_pairs ds j x hx hxn
  have hz1 := central_braid_defect_eq_one ds j x y z k hx hxn hxx hyy ho hz hk he
  exact ⟨y,hy,hxx,hyy,ho,k,hk,by simpa only [hz1,one_mul] using he⟩

private theorem source_kernel_square (j : Bool) (m : SL(2,(ds j).F))
    (z : ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)).ker) :
    z*z=1 := by
  let H := universalBOneActor h j (ds j).data
  let e := universalBOneActorEquiv h j (ds j).data
  have hzker : e (z:H)∈(ds j).data.quotient.ker := by
    apply (MulAut.conj m).injective
    exact z.property.trans (map_one _).symm
  rw [(ds j).data.kernel,core_eq_Z ds j] at hzker
  have hs := ((mem_omegaCenterIn_iff _ _).mp
    ((source_Z_Q_U (reduced_triple h) (base (reducedFamily L S) j)).1 hzker)).2.2
  apply Subtype.ext
  apply e.injective
  apply Subtype.ext
  simpa only [Subgroup.coe_mul,Subgroup.coe_one,map_mul,map_one,pow_two,Subgroup.subtype_apply] using hs

/-- The actual chosen reflection is conjugate inside its original actor to
an involution in the canonical long-path root, also when its center is nontrivial. -/
theorem root_reflection_conjugacy (j : Bool) :
    ∃ x∈(fullCartanPathRoots ds j).root, orderOf x=2 ∧
      ∃ g∈universalBOneActor h j (ds j).data,
        g*x*g⁻¹=fullCartanReflections ds j := by
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
    (core_eq_Z ds j) (ds j).dimension).conj m
  have htt : t*t=1 := Subtype.ext (fullCartanReflections_square ds j)
  obtain ⟨hyy,_,ho,hc,_⟩ := nat.reflected_pair (source_kernel_square ds j m) x t hxx htt a ha hπx ht
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
  have hbraid : (x:(reducedAmalgam L S).Universal)*(t*x*t⁻¹:H)*(x:H)=
      (z:H)*(1:(reducedAmalgam L S).Universal)*fullCartanReflections ds j := by
    simp only [mul_one]
    change ((x*(t*x*t⁻¹)*x):H).val=(z*t).val
    congr 1
    dsimp [z]
    group
  have hz1 : (z:(reducedAmalgam L S).Universal)=1 := central_braid_defect_eq_one ds j
    x (t*x*t⁻¹) z 1 hx (fun he => hxne (Subtype.ext he))
    (congrArg H.subtype hxx) (congrArg H.subtype hyy)
    ((orderOf_injective H.subtype Subtype.coe_injective _).trans ho) hzC (cartan c).one_mem hbraid
  refine ⟨x,hx,(Subgroup.orderOf_coe x).trans (orderOf_eq_prime
    (by simpa only [pow_two] using hxx) hxne),x*t,(x*t).property,?_⟩
  have hh := congrArg H.subtype hg
  simpa only [Subgroup.subtype_apply,Subgroup.coe_mul,Subgroup.coe_inv,hz1,one_mul] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
