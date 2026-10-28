module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicShiftedFullOmega
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreEvenGeneration
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration

/-!
# Paired backward choices in the original cubic point branch

A single even switch fixes the marked critical transposition and carries a
chosen point core to a second one. Each core generates S₆ with the same
transposition, and the two cores generate S₆ together. The no-supplement
argument lifts all three generations through the original projection,
whose kernel is E and whose quotient E/Q has order three.

On the actual cubic graph this supplies two incident edges. Their common
fixed subgroup in the entire seed is its local central part. The same
component switch fixes the critical commutator line pointwise and normalizes
the full critical seed kernel; this is the small-image parabolic placement.
A strict forward slice then constructs both backward critical paths with
endpoints related by that switch. Both shifted kernel commutators equal
the original nonzero forward line, of order two and central at the start.

The whole-core and literal C.1.32 applications use the existing selected
forward path. They retain both moving covers, the plane and Sylow image
branches, and all original quotient maps. These are the simultaneous edge,
fixed-seed and parabolic portions of the source selection. Membership in
its Λ still requires the Thompson-subgroup centralizer and residual
relations for these same choices. The comparison in (5.12)(1), point-branch
contradiction, other image branches and both reconstruction outcomes remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(a), (5.6)(b),(d), the notation on p.919 and (5.12)(1),
pp.915--919,924--925; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull

private def pairSwitch : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 2 4 * Equiv.swap 1 3, by decide⟩

private theorem canonical_pair_generates :
    pointCore ⊔ pointCore.map (MulAut.conj pairSwitch.val).toMonoidHom = ⊤ := by
  have ht : swap45 ∈ pointCore := by
    rw [pointCore_eq_closure]
    exact subset_closure (by simp)
  have hs : Equiv.swap (2 : Fin 6) 5 ∈
      pointCore.map (MulAut.conj pairSwitch.val).toMonoidHom := by
    have he : pairSwitch.val * swap45 * pairSwitch.val⁻¹ = Equiv.swap 2 5 := by decide +kernel
    exact he ▸ mem_map_of_mem (MulAut.conj pairSwitch.val).toMonoidHom ht
  have hg := PointCoreGeneration.canonical_crossing_generate (Equiv.swap (2:Fin 6) 5)
    ⟨2,5,by decide,rfl⟩ (by
      change swap45 * Equiv.swap 2 5 ≠ Equiv.swap 2 5 * swap45
      decide +kernel)
  apply top_unique
  rw [←hg]
  exact sup_le le_sup_left ((zpowers_le.mpr hs).trans le_sup_right)

private theorem paired_point_core_choices (u a : S) (ha : a.IsSwap) :
    ∃ k x : alternatingGroup (Fin 6),
      let P := (pointCore.map (MulAut.conj u).toMonoidHom).map
        (MulAut.conj k.val).toMonoidHom
      let P' := P.map (MulAut.conj x.val).toMonoidHom
      P ⊔ zpowers a = ⊤ ∧ P' ⊔ zpowers a = ⊤ ∧ P ⊔ P' = ⊤ ∧
        x.val * a * x.val⁻¹ = a := by
  let b := u⁻¹*a*u
  have hb : b.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ha
    change (u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
  obtain ⟨c,hc⟩ := PointCoreEvenGeneration.exists_even_swap_conjugator b hb
  let w := u*c.val
  let k : alternatingGroup (Fin 6) := MulAut.conjNormal u c
  let x : alternatingGroup (Fin 6) := MulAut.conjNormal w pairSwitch
  let f := (MulAut.conj w).toMonoidHom
  have ha' : f (Equiv.swap 0 5) = a := by
    change (u*c.val)*Equiv.swap 0 5*(u*c.val)⁻¹ = a
    calc
      _ = u*(c.val*Equiv.swap 0 5*c.val⁻¹)*u⁻¹ := by group
      _ = a := by rw [hc]; dsimp [b]; group
  have hP : (pointCore.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom = pointCore.map f := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    change (u*c.val*u⁻¹)*(u*y*u⁻¹)*(u*c.val*u⁻¹)⁻¹ = (u*c.val)*y*(u*c.val)⁻¹
    group
  have hP' : (pointCore.map f).map (MulAut.conj x.val).toMonoidHom =
      (pointCore.map (MulAut.conj pairSwitch.val).toMonoidHom).map f := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    change (w*pairSwitch.val*w⁻¹)*(w*y*w⁻¹)*(w*pairSwitch.val*w⁻¹)⁻¹ =
      w*(pairSwitch.val*y*pairSwitch.val⁻¹)*w⁻¹
    group
  have hx0 : pairSwitch.val * Equiv.swap 0 5 * pairSwitch.val⁻¹ = Equiv.swap 0 5 := by
    decide +kernel
  have hx : x.val*a*x.val⁻¹ = a := by
    rw [←ha']
    change (w*pairSwitch.val*w⁻¹)*(w*Equiv.swap 0 5*w⁻¹)*(w*pairSwitch.val*w⁻¹)⁻¹ =
      w*Equiv.swap 0 5*w⁻¹
    calc
      _ = w*(pairSwitch.val*Equiv.swap 0 5*pairSwitch.val⁻¹)*w⁻¹ := by group
      _ = _ := by rw [hx0]
  have hgen : pointCore.map f ⊔ zpowers a = ⊤ := by
    have hh := congrArg (Subgroup.map f) PointCoreEvenGeneration.swap_generates
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,ha',
      map_top_of_surjective f (MulAut.conj w).surjective] using hh
  refine ⟨k,x,?_⟩
  dsimp only
  rw [hP]
  refine ⟨hgen,?_,?_,hx⟩
  · have hh := congrArg (Subgroup.map (MulAut.conj x.val).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,
      show (MulAut.conj x.val).toMonoidHom a = a from hx,
      map_top_of_surjective (MulAut.conj x.val).toMonoidHom (MulAut.conj x.val).surjective] using hh
  · rw [hP',←Subgroup.map_sup,canonical_pair_generates,
      map_top_of_surjective f (MulAut.conj w).surjective]

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf M
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem paired_point_core_lifts (u : S)
    (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup M) (a : S) (ha : a.IsSwap) (hA : A.map π = zpowers a) :
    ∃ g ∈ K, ∃ r ∈ K,
      let T := (Rg).map (MulAut.conj g).toMonoidHom
      let T' := T.map (MulAut.conj r).toMonoidHom
      T ⊔ A = ⊤ ∧ T' ⊔ A = ⊤ ∧ T ⊔ T' = ⊤ ∧
        π r * a * (π r)⁻¹ = a := by
  obtain ⟨k,x,hgen,hgen',hpair,hx⟩ := paired_point_core_choices u a ha
  have hkL : k.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  have hxL : x.val ∈ (K).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact x.property
  obtain ⟨g,hg,hgk⟩ := hkL
  obtain ⟨r,hr,hrx⟩ := hxL
  have map_conj (B : Subgroup M) (v : M) :
      (B.map (MulAut.conj v).toMonoidHom).map π =
        (B.map π).map (MulAut.conj (π v)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    simp only [MonoidHom.comp_apply,MulAut.conj_apply,MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe,map_mul,map_inv]
  have core_conj (v : M) :
      (pCore 2 M).map (MulAut.conj v).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v)
  let T := (Rg).map (MulAut.conj g).toMonoidHom
  let T' := T.map (MulAut.conj r).toMonoidHom
  have hQT : pCore 2 M ≤ T := by
    rw [←core_conj g]
    exact map_mono h.relative_radical.twoCore_le
  have hQT' : pCore 2 M ≤ T' := by
    rw [←core_conj r]
    exact map_mono hQT
  have hmT : T.map π = (pointCore.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom := by
    rw [map_conj,hfull,hgk]
  have hmT' : T'.map π = ((pointCore.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj k.val).toMonoidHom).map (MulAut.conj x.val).toMonoidHom := by
    rw [map_conj,hmT,hrx]
  have lift (F : Subgroup M) (hQF : pCore 2 M ≤ F) (hmap : F.map π = ⊤) : F = ⊤ := by
    have hFE : F ⊔ extensionKernel h = ⊤ := by
      have he := congrArg (Subgroup.comap π) hmap
      rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
    have hEF := extensionKernel_no_supplement h F (hFE ▸ (le_top : K ≤ ⊤))
    rw [extensionKernel_twoCore h,sup_of_le_left hQF] at hEF
    rwa [sup_of_le_left hEF] at hFE
  refine ⟨g,hg,r,hr,?_,?_,?_,?_⟩
  · exact lift (T ⊔ A) (hQT.trans le_sup_left) (by
      rw [Subgroup.map_sup,hmT,hA]; exact hgen)
  · exact lift (T' ⊔ A) (hQT'.trans le_sup_left) (by
      rw [Subgroup.map_sup,hmT',hA]; exact hgen')
  · exact lift (T ⊔ T') (hQT.trans le_sup_left) (by
      rw [Subgroup.map_sup,hmT,hmT']; exact hpair)
  · rwa [hrx]

include h e hz hk in
/-- Simultaneous edges generating with the same full critical seed. Their
kernels also generate the local stabilizer, so their common fixed subgroup
in the full seed is precisely the local central part. -/
theorem point_paired_generating_edges
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ K,
      let x := (embedM Rg r)⁻¹
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
      (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
        centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
          Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
      ((Z Rg z).comap (embedM Rg)).map π ≤ centralizer ({π r} : Set S) := by
  let A := (Z Rg z).comap (embedM Rg)
  have hmapA : A.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  obtain ⟨a,hswap,hA⟩ := small_critical_image_eq_swap h e hz hk p (by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide)
  obtain ⟨g,hg,r,hr,hgen,hgen',hpair,hrfix⟩ := paired_point_core_lifts h e hz hk u
    (full_point_image_of_contained h e hz hk u hR) A a hswap hA
  let f := (embedM Rg g)⁻¹
  let x := (embedM Rg r)⁻¹
  let t := act Rg f (beta Rg)
  have hf : f ∈ stabilizer Rg (alpha Rg) := by
    change f ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act Rg f (alpha Rg) = alpha Rg := hf
  have hat : Adjacent Rg (alpha Rg) t := by
    rw [←hfix]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr (base_adjacent Rg)
  have hm (B₀ : Subgroup M) (v : M) :
      (B₀.map (embedM Rg)).map (MulAut.conj (embedM Rg v)).toMonoidHom =
        (B₀.map (MulAut.conj v).toMonoidHom).map (embedM Rg) := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    simp only [MonoidHom.comp_apply,MulAut.conj_apply,MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe,map_mul,map_inv]
  have ht : ((Rg).map (MulAut.conj g).toMonoidHom).map (embedM Rg) = Q Rg t := by
    change _ = Q Rg (act Rg f (beta Rg))
    rw [Q_act,Q_beta,show f⁻¹ = embedM Rg g from inv_inv _,hm]
  have ht' : (((Rg).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj r).toMonoidHom).map (embedM Rg) = Q Rg (act Rg x t) := by
    rw [Q_act,show x⁻¹ = embedM Rg r from inv_inv _,←ht,hm]
  have map_gen (F : Subgroup M) (he : F = ⊤) :
      F.map (embedM Rg) = stabilizer Rg (alpha Rg) := by
    rw [he,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base Rg).symm
  have hg1 := map_gen _ hgen
  have hg2 := map_gen _ hgen'
  have hg3 := map_gen _ hpair
  rw [Subgroup.map_sup,ht,hmapA] at hg1
  rw [Subgroup.map_sup,ht',hmapA] at hg2
  rw [Subgroup.map_sup,ht,ht'] at hg3
  refine ⟨t,hat,r,hr,hg1,hg2,hg3,?_,?_⟩
  · apply le_antisymm
    · rintro v ⟨⟨hv,hvt⟩,hvt'⟩
      refine ⟨hv,?_⟩
      apply le_centralizer_iff.mp ?_ (show v ∈ zpowers v from mem_zpowers _)
      rw [←hg3]
      exact sup_le
        (le_centralizer_iff.mp (zpowers_le.mpr hvt))
        (le_centralizer_iff.mp (zpowers_le.mpr hvt'))
    · rintro v ⟨hv,hvG⟩
      exact ⟨⟨hv,centralizer_le (show Q Rg t ≤ stabilizer Rg (alpha Rg) from le_sup_left.trans hg3.le) hvG⟩,
        centralizer_le (show Q Rg (act Rg x t) ≤ stabilizer Rg (alpha Rg) from le_sup_right.trans hg3.le) hvG⟩
  · change A.map π ≤ _
    rw [hA]
    apply zpowers_le.mpr
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    exact mul_inv_eq_iff_eq_mul.mp hrfix

private theorem commutator_normalized_of_image_centralized
    {A₀ B₀ : Type*} [Group A₀] [Group B₀] (f : A₀ →* B₀)
    (V A : Subgroup A₀) [V.Normal] (r : A₀)
    (hk : f.ker ≤ centralizer (V : Set A₀))
    (hfix : A.map f ≤ centralizer ({f r} : Set B₀)) :
    r ∈ normalizer ((⁅V,A⁆ : Subgroup A₀) : Set A₀) := by
  let c := (MulAut.conj r).toMonoidHom
  have hm : (A.map c).map f = (A.map f).map (MulAut.conj (f r)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro y
    simp only [c,MonoidHom.comp_apply,MulAut.conj_apply,MulEquiv.toMonoidHom_eq_coe,
      MonoidHom.coe_coe,map_mul,map_inv]
  have hn : f r ∈ normalizer (A.map f : Set B₀) :=
    Subgroup.centralizer_le_normalizer _ (fun y hy => (hfix hy _ (Set.mem_singleton _)).symm)
  have hnmap : (A.map f).map (MulAut.conj (f r)).toMonoidHom = A.map f :=
    mem_normalizer_iff_map_conj_eq.mp hn
  rw [hnmap] at hm
  have he := congrArg (Subgroup.comap f) hm
  rw [comap_map_eq,comap_map_eq] at he
  have hV : V.map c = V := mem_normalizer_iff_map_conj_eq.mp
    (by rw [normalizer_eq_top]; exact mem_top r)
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅V,A⁆ : Subgroup A₀).map c = ⁅V,A⁆
  rw [map_commutator,hV]
  calc
    ⁅V,A.map c⁆ = ⁅V,f.ker ⊔ A.map c⁆ :=
      commutator_eq_of_centralizing_sup rfl hk le_normalizer_of_normal
    _ = ⁅V,f.ker ⊔ A⁆ := by rw [sup_comm f.ker (A.map c),he,sup_comm A f.ker]
    _ = ⁅V,A⁆ :=
      (commutator_eq_of_centralizing_sup rfl hk le_normalizer_of_normal).symm

include h e hz hk in
/-- Centralizing the original marked actor image puts the same component
switch in the pointwise fixer of the critical line and in the setwise
stabilizer of the full critical kernel. The kernel of the projection is E. -/
theorem point_switch_fixes_critical_kernel
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (r : M) (hr : r ∈ K)
    (hactor : ((Z Rg z).comap (embedM Rg)).map π ≤ centralizer ({π r} : Set S)) :
    let x := (embedM Rg r)⁻¹
    x ∈ Ltilde Rg (alpha Rg) ∧
    x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
    x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let A := (Z Rg z).comap (embedM Rg)
  have hker : (π).ker ≤ centralizer (radiusSeed L R : Set M) := by
    rw [CubicAction.projection_kernel h e hz hk,seed_centralizer h e hz hk]
  have hn := commutator_normalized_of_image_centralized π (radiusSeed L R) A r hker hactor
  have hmA : A.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hmZ : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  have hn' := le_normalizer_map (embedM Rg) (mem_map_of_mem (embedM Rg) hn)
  rw [map_commutator,hmZ,hmA] at hn'
  have hxi : (embedM Rg r)⁻¹ ∈ normalizer
      ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := inv_mem hn'
  have hxc := normalizer_le_centralizer_of_card_two _
    (point_image_critical_indices_two h e hz hk u hR p).2.2 hxi
  have hxL : (embedM Rg r)⁻¹ ∈ Ltilde Rg (alpha Rg) := by
    apply inv_mem
    rw [graph_component h]
    exact mem_map_of_mem (embedM Rg) hr
  have hxG : (embedM Rg r)⁻¹ ∈ stabilizer Rg (alpha Rg) := Ltilde_le_stabilizer _ hxL
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  have hkn := small_critical_kernel_normalizer_eq_line_centralizer h e hz hk p hsmall
  exact ⟨hxL,hxc,(hkn.ge ⟨hxG,hxc⟩).2⟩

include h e hz hk in
/-- A strict selected slice supplies two backward critical paths using the
same component switch and the same marked opposite actor. Both shifted
kernel commutators are the original nonzero forward kernel line. -/
theorem point_paired_backward_paths
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ t, ∃ r ∈ K, ∃ g ∈ stabilizer Rg (alpha Rg),
      let x := (embedM Rg r)⁻¹
      let c := p.walk.getVert 2
      let d := act Rg g c
      let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆
      ∃ q : CriticalPath Rg (sourceGeometry h) d c,
      ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
        act Rg g (p.walk.getVert 1) = t ∧
        q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = act Rg x t ∧
        q.walk.getVert 2 = alpha Rg ∧ q'.walk.getVert 2 = alpha Rg ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
          centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
            Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
        x ∈ Ltilde Rg (alpha Rg) ∧
        x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
        x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
        ((Z Rg z).comap (embedM Rg)).map π ≤ centralizer ({π r} : Set S) ∧
        (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) ∧
        (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x d))) ∧
        ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
        ⁅U Rg (act Rg x d) ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
        Nat.card H = 2 ∧
        H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (point_image_distance_eq_four h e hz hk u hR)
  have hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(point_image_critical_indices_two h e hz hk u hR p).1]
    decide
  obtain ⟨t,hat,r,hr,hgen,hgen',hpair,hfixed,hactor⟩ := point_paired_generating_edges h e hz hk u hR p
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by simp only [x,map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hx
  let c := p.walk.getVert 2
  have hct : Adjacent Rg c (p.walk.getVert 1) := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨g,hg,hgt,q,hqt,hover,hdi⟩ := small_image_backward_shift_of_two_lt_slice
    h e hz hk hb u hR p hsmall hct hlarge hat hgen
  have hend : p.walk.getVert (p.walk.length-2) = c := by rw [hl]
  have hq : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g c)
      (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha Rg := by
    refine ⟨q,hqt,?_⟩
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  rw [hend] at hq
  obtain ⟨q,hqt,hqa⟩ := hq
  let d := act Rg g c
  have hdt : Adjacent Rg d t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g c (p.walk.getVert 1)).mpr hct
  have hat' : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←hxa]
    exact (adjacent_act_iff Rg x (alpha Rg) t).mpr hat
  have hdt' : Adjacent Rg (act Rg x d) (act Rg x t) :=
    (adjacent_act_iff Rg x d t).mpr hdt
  have hdi' : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x d)) := by
    have hm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [U_act,←hm,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hdi
  have hbad : ¬ Z Rg (act Rg x d) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) :=
    small_image_backward_not_le h e hz hk hb u hR p hsmall hat' hdt' hgen' hdi'
  let w : (cosetGraph Rg).Walk (act Rg x d) (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hdt')
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat')) .nil)
  have hw : w.length = 2 := rfl
  have hcol : color Rg (act Rg x d) = false := by
    rw [action_preserves_color]
    exact q.start_color
  let q₀ := p.prepend_two (Nat.le_of_lt hb) hcol w hw hbad
  have hq₀t : q₀.walk.getVert 1 = act Rg x t := by
    simp only [q₀,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hq₀a : q₀.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      p.prepend_two_overlap (Nat.le_of_lt hb) hcol w hw hbad (i := 0) (by omega)
  have hq' : ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
      q'.walk.getVert 1 = act Rg x t ∧ q'.walk.getVert 2 = alpha Rg := by
    rw [←hend]
    exact ⟨q₀,hq₀t,hq₀a⟩
  obtain ⟨q',hqt',hqa'⟩ := hq'
  have hline := point_strict_shifted_attachment h e hz hk u hR p q rfl hqa
    (by rwa [hqt]) hdi
  have hline' := point_strict_shifted_attachment h e hz hk u hR p q' rfl hqa'
    (by rwa [hqt']) hdi'
  have hpar := point_switch_fixes_critical_kernel h e hz hk u hR p r hr hactor
  exact ⟨t,r,hr,g,hg,q,q',hgt,hqt,hqt',hqa,hqa',hgen,hgen',hpair,hfixed,hpar.1,hpar.2.1,hpar.2.2,hactor,hdi,hdi',
    hline.2.1,hline'.2.1,hline.2.1 ▸ hline.2.2.1,hline.2.1 ▸ hline.2.2.2.1⟩

omit hk in
include h e hz in
/-- The whole-core application uses the original selected forward path and
constructs the paired backward choices without a new selection premise. -/
theorem coreExhaustion_or_cubic_paired_backward_paths :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
              ∃ t, ∃ r ∈ K, ∃ g ∈ stabilizer Rg (alpha Rg),
                let x := (embedM Rg r)⁻¹
                let c := p.walk.getVert 2
                let d := act Rg g c
                let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆
                ∃ q : CriticalPath Rg (sourceGeometry h) d c,
                ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
                  act Rg g (p.walk.getVert 1) = t ∧
                  q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = act Rg x t ∧
                  q.walk.getVert 2 = alpha Rg ∧ q'.walk.getVert 2 = alpha Rg ∧
                  Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
                  (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
                    centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
                      Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
                  x ∈ Ltilde Rg (alpha Rg) ∧
                  x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  ((Z Rg z).comap (embedM Rg)).map (CubicAction.projection h e hz hk) ≤ centralizer ({(CubicAction.projection h e hz hk) r} : Set S) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x d))) ∧
                  ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  ⁅U Rg (act Rg x d) ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  Nat.card H = 2 ∧
                  H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_shifted_full_omega h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hex
  · rcases hpoint with ⟨hpoint,hb4,hsize,z,p,hstrict,hrest⟩
    exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ⟨hpoint,hb4,hsize,z,p,hstrict,
      point_paired_backward_paths h e hz hk u hpoint.le p hstrict⟩⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the simultaneously chosen backward paths.
The plane and Sylow alternatives, both covers and the cubic kernel remain. -/
theorem rankTwo_or_cubic_paired_backward_paths :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          (∀ a : Vertex Rg, color Rg a = false →
            Nat.card (U Rg a) = 32 ∧
            Nat.card (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) :
              Subgroup (FreeAmalgam Rg)) = 2) ∧
          (∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
              ∃ t, ∃ r ∈ K, ∃ g ∈ stabilizer Rg (alpha Rg),
                let x := (embedM Rg r)⁻¹
                let c := p.walk.getVert 2
                let d := act Rg g c
                let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Q Rg c⁆
                ∃ q : CriticalPath Rg (sourceGeometry h) d c,
                ∃ q' : CriticalPath Rg (sourceGeometry h) (act Rg x d) c,
                  act Rg g (p.walk.getVert 1) = t ∧
                  q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = act Rg x t ∧
                  q.walk.getVert 2 = alpha Rg ∧ q'.walk.getVert 2 = alpha Rg ∧
                  Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
                  Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
                  (Z Rg (alpha Rg) ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg))) ⊓
                    centralizer (Q Rg (act Rg x t) : Set (FreeAmalgam Rg)) =
                      Z Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
                  x ∈ Ltilde Rg (alpha Rg) ∧
                  x ∈ centralizer ((⁅Z Rg (alpha Rg),Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  x ∈ normalizer ((Z Rg (alpha Rg) ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
                  ((Z Rg z).comap (embedM Rg)).map (CubicAction.projection h e hz hk) ≤ centralizer ({(CubicAction.projection h e hz hk) r} : Set S) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) ∧
                  (2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x d))) ∧
                  ⁅U Rg d ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  ⁅U Rg (act Rg x d) ⊓ Q Rg c,X Rg z ⊓ Q Rg (alpha Rg)⁆ = H ∧
                  Nat.card H = 2 ∧
                  H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_paired_backward_paths h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
