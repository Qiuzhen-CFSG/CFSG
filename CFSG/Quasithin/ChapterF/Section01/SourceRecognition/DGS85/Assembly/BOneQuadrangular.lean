module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneQuotientMidpoint
public import Theory.Combinatorics.SimpleGraph.QuadrangleSymmetry
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathRootSigns
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneRecognition

/-!
# Marked recognition of the central four-edge natural branch

On the literal source quotient, a radius-two ball fixer is a generalized
quadrangle symmetry. Projection rigidity injects it into the q exits at a
vertex two steps from its center. Each four-edge root already has order q,
so its image is the whole ball fixer. Roots at equivalent midpoint vertices
therefore have equal images.

A nontrivial symmetry fixing the marked edge has its center adjacent to
that edge. Lift this center, and its full root has a representative in the
original Borel. This gives both root signs in the WHOLE original Borel
image. Source exchange then constructs the marked finite split quotient,
whose original rotation order four selects the symplectic amalgam. The
quotient, both endpoints and the complete middle map retain their original
markings. BOneQuadrangularConsumers restores the original Chapter 12 pair.

Source: DGS, Groups and Graphs (1985), (3.6)--(3.7), pp.77--80, (10.5),
pp.156--157 and Theorem D, p.224; Fong--Seitz I (6A)(a), II (7C),(8A).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open SimpleGraph SimpleGraph.Walk
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "n" => fullCartanPathLength ds
local notation "T" => cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))
local notation "r" => sourceRelation A T n
local notation "q" => quotientMap A T n
local notation "Γ" => fullCartanClassGraph ds
local notation "hrInv" => apartmentSetoid_invariant (source_action A)
local notation "κ" => sourceClassType A T n
variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5)

include hr in
private theorem quad_length : n=4 := (fullCartanProfiles_parameters ds).1.unique hr.1

private theorem quad_connected : (Γ).Connected :=
  (Universal.cosetGraph_isTree A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).connected.map
    (full_profile_class_map ds) Quotient.mk_surjective

include hr in
private theorem quad_diameter (a b : Quotient r) : (Γ).dist a b≤4 := by
  obtain ⟨p,hp⟩ := full_profile_class_bounded_walks ds a b
  have hn4 := quad_length ds hr
  exact (dist_le p).trans (by omega)

private theorem quad_thick (v a b : Quotient r) : ∃ z, (Γ).Adj v z ∧ z≠a ∧ z≠b := by
  let : Finite (Quotient r) := fullCartanClassGraph_finite ds
  have hpair : ({a,b} : Set (Quotient r)).ncard≤2 := by
    simpa using Set.ncard_insert_le a ({b} : Set (Quotient r))
  have hc := full_profile_class_neighbor_card ds v
  rw [Nat.card_coe_set_eq] at hc
  have hgt : ({a,b} : Set (Quotient r)).ncard<((Γ).neighborSet v).ncard := by
    rw [hc]
    have : 1<Nat.card (ds false).F := Finite.one_lt_card
    omega
  obtain ⟨z,hz,hne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hgt
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hne
  exact ⟨z,hz,hne⟩

include hr in
private theorem quad_girth (v : Quotient r) (p : (Γ).Walk v v) (hp : p.IsCycle) :
    8≤p.length := by
  by_contra hn
  have he := full_profile_class_short_paths_unique ds p.tail
    (Walk.cons (p.adj_snd hp.not_nil).symm Walk.nil) hp.isPath_tail
    (Walk.IsPath.nil.cons (by simpa only [support_nil,List.mem_singleton] using (p.adj_snd hp.not_nil).ne.symm))
    (by simp only [length_tail,length_cons,length_nil]; have hn4 := quad_length ds hr; omega)
  have hh := congrArg Walk.length he
  simp only [length_tail,length_cons,length_nil] at hh
  have := hp.three_le_length
  omega

/-- The permutation representation, with the literal source quotient as domain. -/
def quotientPermutation : ((A).Universal ⧸ quotientKernel r hrInv) →* Equiv.Perm (Quotient r) :=
  QuotientGroup.kerLift (quotientAction r hrInv)

local notation "φ" => quotientPermutation ds

@[simp] theorem quotientPermutation_mk (g : (A).Universal) :
    φ (q g)=quotientAction r hrInv g := rfl

theorem quotientPermutation_injective : Function.Injective φ :=
  QuotientGroup.kerLift_injective (quotientAction r hrInv)

/-- The faithful action of the SAME quotient is a graph automorphism. -/
def quotientGraphIso (g : (A).Universal ⧸ quotientKernel r hrInv) : Γ ≃g Γ where
  toEquiv := φ g
  map_rel_iff' := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (quotientKernel r hrInv) g
    exact quotientAction_adj_iff hrInv (source_action A) x _ _

/-- Radius-two ball fixation supplies the actual quadrangle symmetry. -/
theorem quotient_ball_isSymmetry (a : Quotient r)
    (g : (A).Universal ⧸ quotientKernel r hrInv)
    (hg : g∈classBallFixer (sourceGraph A) r hrInv a 2) :
    QuadrangleSymmetry.IsSymmetry (quotientGraphIso ds g) a := by
  intro b ⟨l,hal,hbl⟩
  apply (mem_fixingSubgroup_iff _).mp hg b
  exact (Walk.cons hal (Walk.cons hbl.symm Walk.nil)).edist_le

include hr in
/-- A quotient midpoint symmetry is determined by its image of a nonincident
vertex of the other type. -/
theorem quotient_ball_evaluation_injective (a l : Quotient r)
    (ht : κ a≠κ l) (hn : ¬(Γ).Adj a l) :
    Function.Injective (fun g : classBallFixer (sourceGraph A) r hrInv a 2 => φ g l) := by
  intro g k he
  change φ (g : (A).Universal ⧸ quotientKernel r hrInv) l=φ (k : (A).Universal ⧸ quotientKernel r hrInv) l at he
  have hg := quotient_ball_isSymmetry ds a (k⁻¹*g) (k⁻¹*g).property
  have hfix : quotientGraphIso ds (k⁻¹*g) l=l := by
    change φ ((k : (A).Universal ⧸ quotientKernel r hrInv)⁻¹*(g : (A).Universal ⧸ quotientKernel r hrInv)) l=l
    rw [map_mul,map_inv]
    change (φ (k : (A).Universal ⧸ quotientKernel r hrInv)).symm (φ g l)=l
    rw [he,Equiv.symm_apply_apply]
  have hall := QuadrangleSymmetry.symmetry_fixed_nonincident κ
    (sourceClassGraph_bipartition A T n) (quad_girth ds hr) (quad_connected ds)
    (quad_diameter ds hr) (quad_thick ds) (quotientGraphIso ds (k⁻¹*g)) hg ht hn hfix
  apply Subtype.ext
  apply (quotientPermutation_injective ds)
  apply Equiv.ext
  intro x
  have hh := hall x
  change φ ((k : (A).Universal ⧸ quotientKernel r hrInv)⁻¹*(g : (A).Universal ⧸ quotientKernel r hrInv)) x=x at hh
  rw [map_mul,map_inv] at hh
  exact (Equiv.symm_apply_eq (φ k)).mp hh

private theorem card_avoid_one {Y : Type*} [Finite Y] (y : Y) :
    Nat.card {z : Y // z≠y}+1=Nat.card Y := by
  let := Fintype.ofFinite Y
  classical
  simp only [Nat.card_eq_fintype_card]
  have he := Fintype.card_subtype_compl (fun z : Y => z=y)
  rw [Fintype.card_subtype_eq] at he
  rw [he]
  have : 0<Fintype.card Y := Fintype.card_pos_iff.mpr ⟨y⟩
  omega

include hr in
/-- The full quotient midpoint ball fixer has at most q elements, by faithful
geometric evaluation on the q exits at a distance-two vertex. -/
theorem quotient_ball_card_le (a : Quotient r) :
    Nat.card (classBallFixer (sourceGraph A) r hrInv a 2)≤Nat.card (ds false).F := by
  let : Finite (Quotient r) := fullCartanClassGraph_finite ds
  obtain ⟨p,hp,hlen⟩ := full_profile_class_cycle ds a
  have hn4 := quad_length ds hr
  have hl : (p.take 3).length=3 := by rw [take_length]; omega
  have ht : κ a≠κ (p.getVert 3) := by
    intro hh
    have he := (sourceClassGraph_even_walk A T n (p.take 3)).mpr hh
    rw [hl] at he
    norm_num at he
  have hn : ¬(Γ).Adj a (p.getVert 3) := by
    intro hh
    have he := full_profile_class_short_paths_unique ds (p.take 3) (Walk.cons hh Walk.nil)
      (hp.isPath_take (by omega)) (Walk.IsPath.nil.cons (by simp [hh.ne]))
      (by simp only [hl,length_cons,length_nil]; omega)
    have := congrArg Walk.length he
    simp only [hl,length_cons,length_nil] at this
    omega
  obtain ⟨z,hzl,m,ham,hzm⟩ := QuadrangleSymmetry.projection_exists κ
    (sourceClassGraph_bipartition A T n) (quad_connected ds) (quad_diameter ds hr) ht hn
  let H := classBallFixer (sourceGraph A) r hrInv a 2
  have hmfix (g : H) : φ g m=m := by
    apply (mem_fixingSubgroup_iff _).mp g.property m
    exact (Walk.cons ham Walk.nil).edist_le.trans (by norm_num)
  have hzfix (g : H) : φ g z=z := by
    apply (mem_fixingSubgroup_iff _).mp g.property z
    exact (Walk.cons ham (Walk.cons hzm.symm Walk.nil)).edist_le
  have hlm : p.getVert 3≠m := fun he => hn (he.symm ▸ ham)
  let E := {w : (Γ).neighborSet z // w.val≠m}
  let ev : H → E := fun g => ⟨⟨φ g (p.getVert 3),by
    have he := (quotientGraphIso ds g).map_adj_iff.mpr hzl
    change (Γ).Adj (φ g z) (φ g (p.getVert 3)) at he
    change (Γ).Adj z (φ g (p.getVert 3))
    simpa only [hzfix g] using he⟩,by
      intro he
      exact hlm ((φ g).injective (he.trans (hmfix g).symm))⟩
  have hi : Function.Injective ev := by
    intro g k he
    apply quotient_ball_evaluation_injective ds hr a (p.getVert 3) ht hn
    exact congrArg (fun w : E => w.val.val) he
  have hb := Nat.card_le_card_of_injective ev hi
  let b : (Γ).neighborSet z := ⟨m,hzm⟩
  let e : E ≃ {w : (Γ).neighborSet z // w≠b} :=
    Equiv.subtypeEquivRight (by
      intro w
      constructor
      · intro hw he; exact hw (congrArg Subtype.val he)
      · intro hw he; exact hw (Subtype.ext he))
  have hcard := card_avoid_one b
  rw [←Nat.card_congr e,full_profile_class_neighbor_card ds z] at hcard
  change Nat.card H≤_
  omega

include hr in
/-- Every original four-edge root is the ENTIRE symmetry group of its
quotient midpoint, on the literal quotient map and vertex classes. -/
theorem four_path_root_eq_quotient_ball {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : p.length=4) :
    (pathRoot (X := (A).Universal) p).map q=
      classBallFixer (sourceGraph A) r hrInv (Quotient.mk r (p.getVert 2)) 2 := by
  let : Finite (Quotient r) := fullCartanClassGraph_finite ds
  let H := classBallFixer (sourceGraph A) r hrInv (Quotient.mk r (p.getVert 2)) 2
  let : Finite H := Finite.of_injective (fun x : H => φ x)
    (by intro x y he; exact Subtype.ext (quotientPermutation_injective ds he))
  apply Subgroup.eq_of_le_of_card_ge (K := H)
    (four_path_root_fixes_class_ball ds p hp hlen (p.getVert 2) ((r).refl _))
  obtain ⟨g,hg⟩ := exists_smul_base (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 2))
  have hfield (i : Bool) : Nat.card (ds i).F=Nat.card (ds false).F := by
    cases i
    · rfl
    · exact (paired_field_orders_eq (reduced_triple h) (ds false).data (ds true).data
        (ds false).dimension).symm
  have hc := (four_path_root_quotient_card ds hr p hp hlen _ g hg).trans (hfield _)
  exact (quotient_ball_card_le ds hr _).trans hc.ge

include hr in
/-- Equivalent midpoint vertices give equal root images in the actual
finite quotient; equality of their universal representatives is unnecessary. -/
theorem four_path_root_images_eq_of_midpoint_class {a b a' b' : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (p' : (sourceGraph A).Walk a' b')
    (hp : p.IsPath) (hp' : p'.IsPath) (hlen : p.length=4) (hlen' : p'.length=4)
    (hm : r (p.getVert 2) (p'.getVert 2)) :
    (pathRoot (X := (A).Universal) p).map q=(pathRoot (X := (A).Universal) p').map q := by
  rw [four_path_root_eq_quotient_ball ds hr p hp hlen,
    four_path_root_eq_quotient_ball ds hr p' hp' hlen',Quotient.sound hm]

include hr in
/-- A nontrivial quotient symmetry fixes only incident vertices of the other type. -/
theorem quotient_ball_fixed_implies_adj (a l : Quotient r)
    (g : (A).Universal ⧸ quotientKernel r hrInv)
    (hg : g∈classBallFixer (sourceGraph A) r hrInv a 2)
    (hne : g≠1) (ht : κ a≠κ l) (hf : φ g l=l) : (Γ).Adj a l := by
  by_contra hn
  have he := quotient_ball_evaluation_injective ds hr a l ht hn
    (a₁ := ⟨g,hg⟩) (a₂ := 1) (by simpa using hf)
  exact hne (congrArg Subtype.val he)

include ds in
private theorem exists_four_path_at (v : SourceVertex A) :
    ∃ a b, ∃ p : (sourceGraph A).Walk a b, p.IsPath ∧ p.length=4 ∧ p.getVert 2=v := by
  have ht := (Universal.cosetGraph_isTree A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hd : TwoNeighborsIn (sourceGraph A) Set.univ := by
    intro a _
    obtain ⟨b,hb,_,_⟩ := fullCartanProfiles_tree_thick ds a a a
    obtain ⟨c,hc,hcb,_⟩ := fullCartanProfiles_tree_thick ds a b b
    exact ⟨b,Set.mem_univ _,c,Set.mem_univ _,hb,hc,hcb.symm⟩
  obtain ⟨a,p,hp,hl,_,_⟩ := path_extension_in_set ht hd
    (.nil : (sourceGraph A).Walk v v) .nil (by simp) (N := 2) (by simp)
  obtain ⟨b,t,htp,htl,_,hm⟩ := path_extension_in_set ht hd p.reverse hp.reverse
    (by simp) (N := 4) (by simp [hl])
  exact ⟨a,b,t,htp,htl,by simpa only [length_reverse,hl] using hm⟩

include hr in
/-- Every quotient midpoint symmetry fixing the marked edge lies in the
image of the whole original Borel. -/
theorem quotient_ball_mem_borel (a : Quotient r)
    (g : (A).Universal ⧸ quotientKernel r hrInv)
    (hg : g∈classBallFixer (sourceGraph A) r hrInv a 2)
    (hf : ∀ i : Bool, φ g (Quotient.mk r (base (Universal.cosetFamily A) i))=
      Quotient.mk r (base (Universal.cosetFamily A) i)) : g∈(originalMiddle A).map q := by
  by_cases he : g=1
  · exact he ▸ ((originalMiddle A).map q).one_mem
  let i : Bool := !(κ a)
  have ht : κ a≠κ (Quotient.mk r (base (Universal.cosetFamily A) i)) := by
    change κ a≠!(κ a)
    cases κ a <;> decide
  have hadj := quotient_ball_fixed_implies_adj ds hr a _ g hg he ht (hf i)
  obtain ⟨v,hv,hva⟩ := classGraph_neighbor_lift (full_profile_class_neighbor_lifting ds) hadj.symm
  obtain ⟨s,t,p,hp,hl,hm⟩ := exists_four_path_at ds v
  have hg' : g∈(pathRoot (X := (A).Universal) p).map q := by
    rw [four_path_root_eq_quotient_ball ds hr p hp hl,hm,hva]
    exact hg
  obtain ⟨x,hx,rfl⟩ := hg'
  have hball := four_path_root_fixes_ball_two ds p hp hl hx
  rw [hm] at hball
  have hfix (j : Bool) : x • base (Universal.cosetFamily A) j=base (Universal.cosetFamily A) j := by
    apply hball
    by_cases hj : j=i
    · subst j
      exact (Walk.cons hv.symm Walk.nil).edist_le.trans (by norm_num)
    · have hji : j=(!i) := Bool.eq_not_iff.mpr hj
      rw [hji]
      have hbase : (sourceGraph A).Adj (base (Universal.cosetFamily A) i)
          (base (Universal.cosetFamily A) (!i)) :=
        ⟨by change i≠!i; cases i <;> decide,incident_base _ _ _⟩
      exact (Walk.cons hv.symm (Walk.cons hbase Walk.nil)).edist_le
  apply mem_map_of_mem
  rw [originalMiddle,←Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  have hfalse : x∈RankTwo.stabilizer (Universal.cosetFamily A) (base (Universal.cosetFamily A) false) := hfix false
  have htrue : x∈RankTwo.stabilizer (Universal.cosetFamily A) (base (Universal.cosetFamily A) true) := hfix true
  change x∈MulAction.stabilizer _ _ at hfalse htrue
  rw [stabilizer_base] at hfalse htrue
  exact ⟨hfalse,htrue⟩

local notation "ρ" => fullCartanPathRoots ds
local notation "N" => apartmentGroup c ρ
local notation "E" => classStabilizer r hrInv (base (Universal.cosetFamily A) false) ⊓
  classStabilizer r hrInv (base (Universal.cosetFamily A) true)

/-- Both original source lengths have geometric signs on the same quotient. -/
theorem full_profile_quotient_root_class_sign
    (i : Bool) (x : (reducedAmalgam L S).Universal) (hx : x∈N) :
    (∀ u∈(ρ i).root, q (x⁻¹*u*x)∈E) ∨
    (∀ u∈(ρ i).root, q (((ρ i).reflection*x)⁻¹*u*((ρ i).reflection*x))∈E) := by
  let rr := pathRoots h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
    (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
    (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
    (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds)
  have hroot (j : Bool) : (ρ j).root=(rr j).root := by
    rw [fullCartanRoots_root]
    exact (pathRoots_root h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
      (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
      (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
      (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds) j).symm
  have hN : N=apartmentGroup c rr := by
    unfold apartmentGroup
    apply congrArg Subgroup.closure
    apply congrArg ((cartan c : Set (reducedAmalgam L S).Universal) ∪ ·)
    apply congrArg Set.range
    funext j
    exact (fullCartanRoots_reflection ds j).trans
      (pathRoots_reflection h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
        (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
        (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
        (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds) j).symm
  have hsep : Separated (sourceRelation A (cartanApartment A (apartmentGroup c rr)) n)
      (sourceGraph A) (2*n) := by
    rw [←hN]
    exact full_profile_separated ds
  have hx' : x∈apartmentGroup c rr := hN ▸ hx
  have hs := pathRoots_class_sign h c n (fullCartanPathLength_gt ds) (fullCartanReflections ds)
    (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
    (fullCartanReflections_square ds) (fullCartanReflections_normalize ds)
    (fullCartanProfiles_path_transitive ds) (fullCartanProfiles_thickness ds) hsep i x hx'
  change (∀ u∈(rr i).root, ∀ j : Bool,
      sourceRelation A (cartanApartment A (apartmentGroup c rr)) n
        ((x⁻¹*u*x) • base (Universal.cosetFamily A) j) (base (Universal.cosetFamily A) j)) ∨
    (∀ u∈(rr i).root, ∀ j : Bool,
      sourceRelation A (cartanApartment A (apartmentGroup c rr)) n
        (((fullCartanReflections ds i*x)⁻¹*u*(fullCartanReflections ds i*x)) •
          base (Universal.cosetFamily A) j) (base (Universal.cosetFamily A) j)) at hs
  rw [←hN,←hroot i] at hs
  have hmem (g : (reducedAmalgam L S).Universal)
      (hg : ∀ j : Bool, r (g • base (Universal.cosetFamily A) j)
        (base (Universal.cosetFamily A) j)) : q g∈E := by
    exact ⟨(mem_classStabilizer r (apartmentSetoid_invariant (source_action A)) g _).mpr (hg false),
      (mem_classStabilizer r (apartmentSetoid_invariant (source_action A)) g _).mpr (hg true)⟩
  rcases hs with hs | hs
  · exact Or.inl (fun u hu => hmem _ (hs u hu))
  · right
    intro u hu
    rw [fullCartanRoots_reflection]
    exact hmem _ (hs u hu)

include hr in
/-- The original four-edge roots have their signs in the WHOLE Borel image,
with quotient-midpoint descent and geometric symmetry rigidity discharged. -/
theorem full_profile_quotient_root_sign (i : Bool) (x : (A).Universal) (hx : x∈N) :
    (∀ u∈(ρ i).root, q (x⁻¹*u*x)∈(originalMiddle A).map q) ∨
    (∀ u∈(ρ i).root, q (((ρ i).reflection*x)⁻¹*u*((ρ i).reflection*x))∈
      (originalMiddle A).map q) := by
  have hmem (a u : (A).Universal) (hu : u∈(ρ i).root)
      (hf : q (a⁻¹*u*a)∈E) : q (a⁻¹*u*a)∈(originalMiddle A).map q := by
    let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
      (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
      n (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) i
    let iso := translationGraphIso (Universal.cosetFamily A) a⁻¹
    let pp := p.walk.map iso.toHom
    have hpp : pp.IsPath := p.isPath.map iso.injective
    have hl : pp.length=4 := by
      simpa only [pp,length_map] using p.length_eq.trans (quad_length ds hr)
    have hconj : (pathRoot (X := (A).Universal) p.walk).map (MulAut.conj a⁻¹).toMonoidHom=
        pathRoot (X := (A).Universal) pp := by
      apply pathRoot_map_conj p.walk pp a⁻¹ (by simp only [pp,length_map])
      intro k _
      simp only [pp,getVert_map]
      rfl
    have hroot : a⁻¹*u*a∈pathRoot (X := (A).Universal) pp := by
      rw [←hconj]
      have hu' : u∈pathRoot (X := (A).Universal) p.walk := by
        rw [fullCartanRoots_root] at hu
        exact hu
      have hh := mem_map_of_mem (MulAut.conj a⁻¹).toMonoidHom hu'
      change a⁻¹*u*(a⁻¹)⁻¹∈_ at hh
      simpa only [inv_inv] using hh
    apply quotient_ball_mem_borel ds hr (Quotient.mk r (pp.getVert 2)) (q (a⁻¹*u*a))
      (four_path_root_fixes_class_ball ds pp hpp hl (pp.getVert 2) ((r).refl _)
        (mem_map_of_mem q hroot))
    intro j
    rw [quotientPermutation_mk,quotientAction_mk]
    apply Quotient.sound
    cases j
    · exact (mem_classStabilizer r hrInv (a⁻¹*u*a) _).mp hf.1
    · exact (mem_classStabilizer r hrInv (a⁻¹*u*a) _).mp hf.2
  rcases full_profile_quotient_root_class_sign ds i x hx with hs | hs
  · exact Or.inl (fun u hu => hmem x u hu (hs u hu))
  · exact Or.inr (fun u hu => hmem ((ρ i).reflection*x) u hu (hs u hu))

/-- The marked finite split quotient of the original r=4 source branch. -/
def fullCartanRFourFiniteQuotient :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient (recognitionEndpoints A) :=
  fullCartanFiniteQuotient ds (full_profile_source_exchange ds) (full_profile_quotient_root_sign ds hr)

/-- Both original endpoints and the whole Borel retain their inclusion squares. -/
def fullCartanRFourFiniteMarkedIso : Iso A (fullCartanRFourFiniteQuotient ds hr).standardAmalgam :=
  fullCartanFiniteMarkedIso ds (full_profile_source_exchange ds) (full_profile_quotient_root_sign ds hr)

/-- Splitness is constructed on that same finite marked quotient. -/
def fullCartanRFourFiniteSplitData :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData (fullCartanRFourFiniteQuotient ds hr).tits :=
  fullCartanFiniteSplitData ds (full_profile_source_exchange ds) (full_profile_quotient_root_sign ds hr)

@[simp] theorem fullCartanRFourFiniteQuotient_kernel :
    (fullCartanRFourFiniteQuotient ds hr).D=kernel A T n := rfl

@[simp] theorem fullCartanRFourFiniteQuotient_map (g : (A).Universal) :
    (fullCartanRFourFiniteQuotient ds hr).q g=q g := rfl

/-- The marked Borel is the image of the full original middle group. -/
theorem fullCartanRFourFiniteQuotient_borel :
    (originalMiddle A).map q=(fullCartanRFourFiniteQuotient ds hr).tits.B := by
  have he := (fullCartanRFourFiniteQuotient ds hr).borel_image
  change ((Universal.left A).range ⊓ (Universal.right A).range).map q=_ at he
  rw [Universal.overlap_eq A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))] at he
  exact he

/-- The Weyl rotation has the literal original source order four. -/
theorem quadrangular_quotient_rotation :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates.rotationOrder
      (fullCartanRFourFiniteQuotient ds hr)=4 := by
  have ho := finiteQuotient_simple_product_order h c (fullCartanPathRoots ds)
    (fullCartanRoots_normalizes ds) (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    (fullCartanRoots_square ds) n (fullCartanPathLength_gt ds)
    (fullCartanProfiles_path_odd ds) (fullCartanProfiles_path_transitive ds)
    (full_profile_source_exchange ds) (full_profile_quotient_root_sign ds hr)
  exact ho.trans (quad_length ds hr)

include hr in
/-- Recognize the original reduced central branch as the marked symplectic
amalgam over its original left field. -/
theorem quadrangular_reduced_comparison :
    ∃ point : Bool, Nonempty (Iso A (SymplecticNative.amalgam (ds false).F point)) := by
  let p : C2Source.Profile L S (ds false).F (ds true).F (ds false).W (ds true).W :=
    ⟨(ds false).data,(ds true).data,(ds false).actor_eq,(ds true).actor_eq,(ds false).dimension⟩
  rcases reduced_comparison h p (ds true).dimension (fullCartanRFourFiniteQuotient ds hr)
    (fullCartanRFourFiniteMarkedIso ds hr) (fullCartanRFourFiniteSplitData ds hr) with hh | hh
  · have ho := quadrangular_quotient_rotation ds hr
    omega
  · exact hh.2

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
