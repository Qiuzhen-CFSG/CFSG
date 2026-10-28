module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceCartanPaths
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryAlphaCartanReflection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoPathCartan
public import Theory.GroupTheory.WeakBNPair.RegularTree.CubicRootReflection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathReflectionClass

/-!
# Full-Cartan reflections of the actual binary/eight source

The cubic six-path radical has order two, hence centralizes the prescribed
full Cartan. A Cartan-normalizing neighbor transporter conjugates it into an
involution moving the marked neighbor. At the eight endpoint the same full
Cartan lies in the intrinsic linear actor, so the actual escaping radical
involution has a Cartan-normalizing conjugate. The covering retains the
original endpoint groups and their full two-cores.

Source: DGS (14.1)--(14.2), printed pp.210--211.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTreeReflections
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile SourceCartanPaths
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "P" => Universal.cosetFamily A

private theorem middle_le_endpoint (i : Bool) : originalMiddle A ≤ P i := by
  rw [originalMiddle, ←Universal.overlap_eq A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases i
  · exact inf_le_left
  · exact inf_le_right

private theorem edge_complement (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool) :
    let C := (cartan c).map (bOne_tree_map h)
    let E := stabilizer F (base F i) ⊓ stabilizer F (base F (!i))
    C ≤ E ∧ Odd (Nat.card C) ∧ Disjoint C (E.pCoreIn 2) ∧
      C ⊔ E.pCoreIn 2 = E ∧ (twoGroup L S).map (bOne_tree_map h) ≤ E.pCoreIn 2 := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let U := (twoGroup L S).map φ
  let E := F false ⊓ F true
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ F false from inf_le_left))
    (inclusion_injective _)
  let : Finite (E.pCoreIn 2) := Finite.of_injective (inclusion (pCoreIn_le 2 E))
    (inclusion_injective _)
  have hmapE : (originalMiddle A).map φ = E := by
    rw [originalMiddle, ←Universal.overlap_eq A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))]
    exact cov.map_inf
  have hCE : C ≤ E := hmapE ▸ map_mono (cartan_le c)
  have hUE : U ≤ E := hmapE ▸ map_mono (twoGroup_le (L := L) (S := S))
  have hUnorm : E ≤ normalizer (U : Set (G₀ L S)) := by
    rw [←hmapE]
    exact (map_mono (twoGroup_normalized h)).trans ((twoGroup L S).le_normalizer_map φ)
  have hUcore : U ≤ E.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((twoGroup_isTwo h).map φ) hUE hUnorm
  have ho : Odd (Nat.card C) := (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
    ((cartan c).card_map_dvd φ)
  have hd : Disjoint C (E.pCoreIn 2) := by
    obtain ⟨m,hm⟩ := (isPGroup_pCoreIn 2 E).exists_card_eq
    exact disjoint_of_coprime_natCard (by rw [hm]; exact ho.coprime_two_right.pow_right m)
  have hg : C ⊔ E.pCoreIn 2 = E := by
    apply le_antisymm (sup_le hCE (pCoreIn_le 2 E))
    have he := congrArg (Subgroup.map φ) (factorization c)
    rw [Subgroup.map_sup,hmapE] at he
    calc
      E = U ⊔ C := he.symm
      _ ≤ C ⊔ E.pCoreIn 2 := sup_le (hUcore.trans le_sup_right) le_sup_left
  have hEi : E = stabilizer F (base F i) ⊓ stabilizer F (base F (!i)) := by
    change E = MulAction.stabilizer (G₀ L S) (base F i) ⊓
      MulAction.stabilizer (G₀ L S) (base F (!i))
    rw [Subgroup.CosetGeometry.stabilizer_base F i,Subgroup.CosetGeometry.stabilizer_base F (!i)]
    cases i
    · rfl
    · exact inf_comm _ _
  exact hEi ▸ ⟨hCE,ho,hd,hg,hUcore⟩

private theorem lift_endpoint_normalizer (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (i : Bool)
    (g : G₀ L S) (hg : g ∈ F i)
    (hgC : g ∈ normalizer ((cartan c).map (bOne_tree_map h) : Set (G₀ L S))) :
    ∃ t ∈ P i, bOne_tree_map h t = g ∧
      t ∈ normalizer (cartan c : Set (A).Universal) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  have hgimage : g ∈ (P i).map φ := (cov.map_eq i).symm ▸ hg
  obtain ⟨t,ht,htg⟩ := hgimage
  have hKi : cartan c ≤ P i := (cartan_le c).trans (middle_le_endpoint i)
  let Ki := (cartan c).subgroupOf (P i)
  let f : P i →* G₀ L S := φ.comp (P i).subtype
  have hf : Function.Injective f := cov.injective i
  have hKmap : Ki.map f = (cartan c).map φ := by
    change Ki.map (φ.comp (P i).subtype) = _
    rw [←Subgroup.map_map,map_subgroupOf_eq_of_le hKi]
  have htKi : (⟨t,ht⟩ : P i) ∈ normalizer (Ki : Set (P i)) := by
    have hh : (⟨t,ht⟩ : P i) ∈ (normalizer (Ki.map f : Set (G₀ L S))).comap f := by
      change f ⟨t,ht⟩ ∈ normalizer (Ki.map f : Set (G₀ L S))
      rw [hKmap]
      exact htg.symm ▸ hgC
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective hf] at hh
    exact hh
  have hn := Ki.le_normalizer_map (P i).subtype (mem_map_of_mem (P i).subtype htKi)
  rw [map_subgroupOf_eq_of_le hKi] at hn
  exact ⟨t,ht,htg,hn⟩

private theorem image_cartan_card (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) :
    Nat.card ((cartan c).map (bOne_tree_map h)) = Nat.card (cartan c) := by
  have hCP : cartan c ≤ P false := (cartan_le c).trans (middle_le_endpoint false)
  let K := (cartan c).subgroupOf (P false)
  let f : P false →* G₀ L S := (bOne_tree_map h).comp (P false).subtype
  have hf : Function.Injective f := (bOne_tree_cover h).injective false
  have he : K.map f = (cartan c).map (bOne_tree_map h) := by
    rw [show f = (bOne_tree_map h).comp (P false).subtype from rfl,
      ←Subgroup.map_map,map_subgroupOf_eq_of_le hCP]
  rw [←he,card_map_of_injective hf]
  exact Nat.card_congr (subgroupOfEquivOfLe hCP).toEquiv

private theorem eight_reflection (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (e8 : (graphLocalGroup F (base F true) ⧸ pCore 2 (graphLocalGroup F (base F true))) ≃*
      SL(2,GaloisField 2 3)) (hr : HasSixPathRadical L S c true) :
    ∃ t : (A).Universal, t • base P true=base P true ∧
      t • base P false≠base P false ∧ t*t=1 ∧
      t ∈ normalizer (cartan c : Set (A).Universal) ∧
      Nonempty (BinarySixPathReflectionClass h true t) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let J := graphLocalGroup F (base F true)
  let : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let : Finite C := Finite.of_injective
    (inclusion ((edge_complement h c true).1.trans inf_le_left)) (inclusion_injective _)
  have hadj : (graph F).Adj (base F true) (base F false) :=
    ⟨by change true ≠ false; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨hCE,ho,hd,hg,hU⟩ := edge_complement h c true
  obtain ⟨⟨etor⟩,_⟩ := CommutingTrivial.edge_complement_local_torus (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj e8 C hCE hd hg
  have hCJ : C ≤ J := by
    have hc : Nat.card (C ⊓ J : Subgroup (G₀ L S)) = Nat.card C := by
      change (C ⊓ J : Subgroup (G₀ L S)) ≃* (GaloisField 2 3)ˣ at etor
      calc
        Nat.card (C ⊓ J : Subgroup (G₀ L S)) = Nat.card (GaloisField 2 3)ˣ := Nat.card_congr etor.toEquiv
        _ = 7 := by rw [Nat.card_units,GaloisField.card 2 3 (by decide)]; decide
        _ = Nat.card C := ((image_cartan_card h c).trans hC).symm
    exact inf_eq_left.mp (eq_of_le_of_card_ge inf_le_left hc.ge)
  obtain ⟨a,p,hp,hpl,hprev,hCp,hcard,hR,hdis,x,hx,hx2,hxQ⟩ := hr
  have hxP : x ∈ P true := by
    rw [←Subgroup.CosetGeometry.stabilizer_base P true]
    exact (pathRoot_fixes p hx).1
  have hxE := hU (mem_map_of_mem φ (hR hx))
  have hxQ' : φ x ∉ Q F (base F true) := fun he =>
    hxQ ((universalBOne_mem_core_iff h true x hxP).mp he)
  obtain ⟨g,hgJ,hgC,hg2,hgfix,hgmove,z,hzJ,hzx⟩ :=
    CommutingOneProfile.source_linear_actor_cartan_root_reflection (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hadj e8 C hCE hCJ ho hd hg
      (φ x) hxE (by rw [←map_mul,hx2,map_one]) hxQ'
  have hgP : g ∈ F true := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F true]
    exact hgfix
  obtain ⟨t,ht,htg,htC⟩ := lift_endpoint_normalizer h c true g hgP hgC
  have hzP : z ∈ F true := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F true]
    exact sylowGenerated_le _ hzJ
  obtain ⟨y,hy,hφy⟩ := (cov.map_eq true).symm ▸ hzP
  have hxJ : φ x ∈ graphLocalGroup F (base F true) :=
    graph_intrinsic_edgeCore_le (reduced_triple h) hxE
  have hxorder : orderOf x=2 := orderOf_eq_prime
    (by simpa only [pow_two] using hx2) (by
      intro he; apply hxQ; rw [he]; exact one_mem _)
  have hyconj : y*x*y⁻¹=t := by
    apply congrArg Subtype.val (cov.injective true
      (a₁ := ⟨y*x*y⁻¹,(P true).mul_mem ((P true).mul_mem hy hxP) ((P true).inv_mem hy)⟩)
      (a₂ := ⟨t,ht⟩) ?_)
    change φ (y*x*y⁻¹)=φ t
    rw [map_mul,map_mul,map_inv,hφy,htg]
    exact hzx
  have hclass : Nonempty (BinarySixPathReflectionClass h true t) :=
    ⟨{ start := a, path := p, isPath := hp, length_eq := hpl, previous := hprev,
       root := ⟨x,hxJ,hxP⟩, root_mem := hx, root_order := hxorder,
       conjugator := ⟨y,by change φ y∈graphLocalGroup F (base F true); rw [hφy]; exact hzJ,hy⟩,
       conjugates := hyconj }⟩
  refine ⟨t,?_,?_,?_,htC,hclass⟩
  · have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base P true] at hh
    exact hh
  · intro he
    apply hgmove
    have hh := congrArg cov.vertex he
    simpa only [cov.vertex_smul,cov.vertex_base,htg] using hh
  · exact congrArg Subtype.val (cov.injective true
      (a₁ := ⟨t*t,(P true).mul_mem ht ht⟩) (a₂ := 1)
      (by change φ (t*t)=φ 1; rw [map_mul,htg,hg2,map_one]))

private theorem binary_reflection (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) (hC : Nat.card (cartan c)=7)
    (hval : ∀ v : SourceVertex A,
      Nat.card ((sourceGraph A).neighborSet v)=if v.type then 9 else 3)
    (hodd : ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=7 →
      Odd (Nat.card (pathFixer (X := (A).Universal) p)))
    (hr : HasSixPathRadical L S c false) :
    ∃ t : (A).Universal, t • base P false=base P false ∧
      t • base P true≠base P true ∧ t*t=1 ∧
      t ∈ normalizer (cartan c : Set (A).Universal) ∧
      Nonempty (BinarySixPathReflectionClass h false t) := by
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let C := (cartan c).map φ
  let : IsMulCommutative (cartan c) := cartan_abelian h c
  let : IsMulCommutative C := inferInstanceAs (IsMulCommutative ((cartan c).map φ))
  have hCP (i : Bool) : cartan c ≤ P i := (cartan_le c).trans (middle_le_endpoint i)
  have hfix (i : Bool) : ∀ x∈cartan c, x • base P i=base P i := by
    intro x hx
    have hh := hCP i hx
    rw [←Subgroup.CosetGeometry.stabilizer_base P i] at hh
    exact hh
  have hvals (v : SourceVertex A) : Nat.card ((sourceGraph A).neighborSet v)=3 ∨
      Nat.card ((sourceGraph A).neighborSet v)=9 := by
    have hv := hval v
    cases he : v.type
    · exact Or.inl (by simpa only [he,Bool.false_eq_true,if_false] using hv)
    · exact Or.inr (by simpa only [he,if_true] using hv)
  obtain ⟨v,hvC,w,hwC,hv,hw,hvw⟩ := seven_fixed_twoNeighbors P (cartan c) hC hvals
    (base P false) (hfix false)
  have hexit : ∃ z, (sourceGraph A).Adj (base P false) z ∧ z≠base P true ∧
      ∀ x∈cartan c, x • z=z := by
    by_cases he : v=base P true
    · exact ⟨w,hw,fun hh => hvw (he.trans hh.symm),hwC⟩
    · exact ⟨v,hv,he,hvC⟩
  obtain ⟨z,hz,hzne,hzC⟩ := hexit
  have hadj : (graph F).Adj (base F false) (base F true) :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  have hz' : (graph F).Adj (base F false) (cov.vertex z) := by
    have hh := cov.hom.map_adj hz
    change (graph F).Adj (cov.vertex (base P false)) (cov.vertex z) at hh
    rwa [cov.vertex_base] at hh
  have hCz : C ≤ stabilizer F (cov.vertex z) := by
    rintro g ⟨x,hx,rfl⟩
    exact (cov.vertex_smul x z).symm.trans (congrArg cov.vertex (hzC x hx))
  obtain ⟨hCE,ho,hd,hg,hU⟩ := edge_complement h c false
  obtain ⟨g,hgJ,hgC,hgz⟩ := Assembly.BTwoSource.full_cartan_neighbor_transport
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hadj hz' C hCE hCz ho hd hg
  have hgP : g ∈ F false := by
    rw [←Subgroup.CosetGeometry.stabilizer_base F false]
    exact sylowGenerated_le _ hgJ
  obtain ⟨t,ht,htg,htC⟩ := lift_endpoint_normalizer h c false g hgP hgC
  have htfix : t • base P false=base P false := by
    have hh := ht
    rw [←Subgroup.CosetGeometry.stabilizer_base P false] at hh
    exact hh
  have htmove : t • base P true≠base P true := by
    intro he
    have hh := congrArg cov.vertex he
    have hgfix : g • base F true=base F true := by
      simpa only [cov.vertex_smul,cov.vertex_base,htg] using hh
    have hzbase : cov.vertex z=cov.vertex (base P true) := by
      rw [cov.vertex_base,←hgz,hgfix]
    have hbase : (sourceGraph A).Adj (base P false) (base P true) :=
      ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
    exact hzne (congrArg Subtype.val ((cov.neighbor_bijective (base P false)).1
      (a₁ := ⟨z,hz⟩) (a₂ := ⟨base P true,hbase⟩) (Subtype.ext hzbase)))
  obtain ⟨a,p,hp,hpl,hprev,hCp,hcard,hR,hdis,x,hx,hx2,hxQ⟩ := hr
  have hx1 : x≠1 := by
    intro he
    apply hxQ
    rw [he]
    exact one_mem _
  have hxC : x ∈ centralizer (cartan c : Set (A).Universal) := by
    apply mem_centralizer_iff.mpr
    intro k hk
    exact (mem_centralizer_iff.mp
      (normalizer_le_centralizer_of_card_two (pathRoot (X := (A).Universal) p) hcard
        (pathFixer_le_normalizer_pathRoot p (hCp hk))) x hx).symm
  let r := t*x*t⁻¹
  have hrC : r ∈ centralizer (cartan c : Set (A).Universal) :=
    (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer (cartan c) htC) x).mp hxC
  have hxP : x ∈ P false := by
    rw [←Subgroup.CosetGeometry.stabilizer_base P false]
    exact (pathRoot_fixes p hx).1
  have hxJ : φ x ∈ graphLocalGroup F (base F false) :=
    graph_intrinsic_edgeCore_le (reduced_triple h) (hU (mem_map_of_mem φ (hR hx)))
  have htJ : φ t ∈ graphLocalGroup F (base F false) := by rw [htg]; exact hgJ
  have hclass : Nonempty (BinarySixPathReflectionClass h false r) :=
    ⟨{ start := a, path := p, isPath := hp, length_eq := hpl, previous := hprev,
       root := ⟨x,hxJ,hxP⟩, root_mem := hx,
       root_order := orderOf_eq_prime (by simpa only [pow_two] using hx2) hx1,
       conjugator := ⟨t,htJ,ht⟩, conjugates := rfl }⟩
  refine ⟨r,?_,?_,?_,Subgroup.centralizer_le_normalizer _ hrC,hclass⟩
  · dsimp only [r]
    rw [mul_smul,mul_smul,inv_smul_eq_iff.mpr htfix.symm,
      (pathRoot_fixes p hx).1,htfix]
  · intro he
    have htinv : t⁻¹ • base P true≠base P true := by
      intro hi
      apply htmove
      have hh := congrArg (fun v => t • v) hi
      simpa only [smul_inv_smul] using hh.symm
    have hzexit : (sourceGraph A).Adj (base P false) (t⁻¹ • base P true) := by
      have hh := source_action A t⁻¹
        (show (sourceGraph A).Adj (base P false) (base P true) from
          ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩)
      simpa only [inv_smul_eq_iff.mpr htfix.symm] using hh
    have hzprev : t⁻¹ • base P true≠p.penultimate := hprev ▸ htinv
    have htree := (Universal.cosetGraph_isTree A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
    have hznew : t⁻¹ • base P true∉p.support := fun hm =>
      hzprev (htree.eq_penultimate_of_adj_end hp hzexit hm)
    have ho := hodd (p.concat hzexit) (hp.concat hznew hzexit)
      (by rw [Walk.length_concat,hpl])
    have hh : x ∈ pathRoot (X := (A).Universal) p ⊓
        MulAction.stabilizer (A).Universal (t⁻¹ • base P true) := by
      refine ⟨hx,?_⟩
      change x • (t⁻¹ • base P true)=t⁻¹ • base P true
      have hh := congrArg (fun v => t⁻¹ • v) he
      simpa only [r,mul_smul,inv_smul_smul] using hh
    rw [pathRoot_inf_stabilizer_eq_bot p hzexit ho] at hh
    exact hx1 hh
  · dsimp only [r]
    calc
      _ = t*(x*x)*t⁻¹ := by group
      _ = 1 := by rw [hx2,mul_one,mul_inv_cancel]

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Aₛ" => reducedAmalgam Lₛ (T : Subgroup G)
local notation "Pₛ" => Universal.cosetFamily Aₛ

set_option maxHeartbeats 800000 in
/-- Actual involutive reflections at both original universal endpoints,
normalizing the same prescribed full Cartan. No reflection is assumed. -/
theorem source_tree_reflections
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ (T : Subgroup G))) :
    ∃ t : Bool → (Aₛ).Universal,
      (∀ i, t i • base Pₛ i=base Pₛ i) ∧
      (∀ i, t i • base Pₛ (!i)≠base Pₛ (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i ∈ normalizer (cartan c : Set (Aₛ).Universal)) ∧
      (∀ i, Nonempty (BinarySixPathReflectionClass
        (show HypothesisF11 Lₛ (T : Subgroup G) from
          (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) i (t i))) := by
  have h : HypothesisF11 Lₛ (T : Subgroup G) :=
    (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap
  have hC := SourceCartan.source_cartan_order hG T hempty hM hu hmany hcard e H hH eR c
  have hr := source_six_path_radical hG T hempty hM hu hmany hcard e H hH eR c
  have hprof := source_path_profile hG T hempty hM hu hmany hcard e H hH eR
  have hb := binary_reflection h c hC
    (source_tree_neighbor_cards hG T hempty hM hu hmany hcard e H hH eR) hprof.2.2 (hr false)
  have e8 := (Assembly.linear_graph_quotient h true (residualQuotientEquiv H eR)
    (base (reducedFamily Lₛ (T : Subgroup G)) true) rfl).some
  have he := eight_reflection h c hC e8 (hr true)
  have hall : ∀ i : Bool, ∃ t : (Aₛ).Universal, t • base Pₛ i=base Pₛ i ∧
      t • base Pₛ (!i)≠base Pₛ (!i) ∧ t*t=1 ∧
      t ∈ normalizer (cartan c : Set (Aₛ).Universal) ∧
      Nonempty (BinarySixPathReflectionClass h i t) := by
    intro i
    cases i
    · exact hb
    · exact he
  choose t htfix htmove htsq htnorm htclass using hall
  exact ⟨t,htfix,htmove,htsq,htnorm,htclass⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceTreeReflections
