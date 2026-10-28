module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralRigidity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneCenterlessExchange

/-!
# Exchange on both original natural apartments

Transport the canonical opposite roots and their exact cubic braid to the
midpoint of every length-2r path in the chosen apartment. The braid maps
one endpoint to the other. Factoring a half-path fixer by its radical and
the original full Cartan gives exchange for every source actor.

The proof works at r=3 and r=4, keeping the central actor in the second
case. It uses no natural action on the whole core, trivial common-core
centralizer, split-actor assumption or quotient root-sign hypothesis.
BOneCentralCompletion applies exchange to the original critical pair and
constructs its faithful finite geometric completion.

Source: DGS, Groups and Graphs (1985), (14.12)--(14.15), pp.217--220;
this is the characteristic-two natural branch II(a) of (14.15).
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
local notation "n" => fullCartanPathLength ds
local notation "t" => fullCartanReflections ds
local notation "N" => reflectionGroup c t
local notation "T" => cartanApartment A N

/-- The transported cubic braid carries the first endpoint to the second
on every actual length-2r apartment path. -/
theorem apartment_root_pairs
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hlen : p.length=2*n) (hpT : ∀ z∈p.support, z∈T)
    (x : (reducedAmalgam L S).Universal)
    (hx : x∈pathRoot (X := (reducedAmalgam L S).Universal) (p.drop n)) (hxn : x≠1) :
    ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (p.take n),
      x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧ (x*y*x) • a=b := by
  have hn := fullCartanPathLength_gt ds
  have hline := fullCartanApartment_noBranching ds
  have hnorm := reflectionGroup_normalizes c t (fullCartanReflections_normalize ds)
  obtain ⟨g,hg,j,hgv,hgw⟩ := cartanApartment_edge_coordinates A N (fullCartanPathRoots ds)
    (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    (fun i => by rw [fullCartanRoots_reflection]; exact reflectionGroup_mem c t i)
    hline (hpT _ (p.getVert_mem_support n)) (hpT _ (p.getVert_mem_support (n+1)))
    (p.adj_getVert_succ (by omega))
  let r := reflectionPath c t (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
    (fullCartanReflections_normalize ds) n (Nat.zero_lt_of_lt hn) j
  have hrT : ∀ z∈r.walk.reverse.support, z∈T := by
    intro z hz
    exact r.supported z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
  have hdT : ∀ z∈(p.drop n).support, z∈T := by
    intro z hz
    rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
    exact hpT z (List.mem_of_mem_drop hz)
  have hrlen : r.walk.reverse.length=(p.drop n).length := by
    rw [SimpleGraph.Walk.length_reverse,r.length_eq,SimpleGraph.Walk.drop_length,hlen]
    omega
  have hfirst : r.walk.reverse.getVert 1=base (Universal.cosetFamily A) (!j) := by
    rw [SimpleGraph.Walk.getVert_reverse]
    exact r.previous
  have hvertices := maps_path_of_first_edge (source_action A) hline r.walk.reverse (p.drop n)
    r.isPath.reverse (hp.drop n) hrlen hrT hdT g
    (fun _ hz => cartanApartment_preserves A N hg hz) hgv
    (by rw [hfirst,SimpleGraph.Walk.drop_getVert]; exact hgw)
  have hRmap : ((fullCartanPathRoots ds j).root).map (MulAut.conj g).toMonoidHom=
      pathRoot (X := (reducedAmalgam L S).Universal) (p.drop n) := by
    rw [fullCartanRoots_root]
    change (pathRoot (X := (reducedAmalgam L S).Universal) r.walk).map _=_
    rw [←pathRoot_reverse r.walk]
    exact pathRoot_map_conj r.walk.reverse (p.drop n) g hrlen hvertices
  let v := base (Universal.cosetFamily A) j
  let u := g*t j*g⁻¹
  have huu : u*u=1 := by
    calc
      _ = g*(t j*t j)*g⁻¹ := by dsimp [u]; group
      _ = 1 := by rw [fullCartanReflections_square,mul_one,mul_inv_cancel]
  have huN : u∈N := (reflectionGroup c t).mul_mem ((reflectionGroup c t).mul_mem hg (reflectionGroup_mem c t j)) ((reflectionGroup c t).inv_mem hg)
  have hufix : u • p.getVert n=p.getVert n := by
    rw [←hgv]
    change (g*t j*g⁻¹) • (g • v)=g • v
    rw [mul_smul,mul_smul,inv_smul_smul,fullCartanReflections_fix]
  have humove : u • p.getVert (n+1)≠p.getVert (n+1) := by
    rw [←hgw]
    change (g*t j*g⁻¹) • (g • base (Universal.cosetFamily A) (!j))≠_
    rw [mul_smul,mul_smul,inv_smul_smul]
    exact fun he => fullCartanReflections_move ds j ((MulAction.toPerm g).injective he)
  have hrev := reverses_path_of_moves_midpoint_neighbor (source_action A) hline p hp n
    (by omega) hlen hpT u huu (fun _ hz => cartanApartment_preserves A N huN hz) hufix humove
  have hSmap : (pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j)).map
      (MulAut.conj g).toMonoidHom=pathRoot (X := (reducedAmalgam L S).Universal) (p.take n) := by
    rw [fullCartanOppositePath_root]
    calc
      _ = (((fullCartanPathRoots ds j).root).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj u).toMonoidHom := by
        rw [Subgroup.map_map,Subgroup.map_map]
        congr 1
        apply MonoidHom.ext
        intro x
        change g*(t j*x*(t j)⁻¹)*g⁻¹=(g*t j*g⁻¹)*(g*x*g⁻¹)*(g*t j*g⁻¹)⁻¹
        group
      _ = _ := by rw [hRmap]; exact (pathRoot_halves_reflection p n hlen u hrev).2
  obtain ⟨x₀,hx₀,he⟩ : x∈((fullCartanPathRoots ds j).root).map (MulAut.conj g).toMonoidHom := hRmap.symm ▸ hx
  have hx₀ne : x₀≠1 := by
    intro hx1
    exact hxn (he.symm.trans (by rw [hx1,map_one]))
  obtain ⟨y₀,hy₀,hxx,hyy,ho,k,hk,hbraid⟩ := root_pairs_exact ds j x₀ hx₀ hx₀ne
  let y := g*y₀*g⁻¹
  have hy : y∈pathRoot (X := (reducedAmalgam L S).Universal) (p.take n) := by
    rw [←hSmap]
    exact ⟨y₀,hy₀,rfl⟩
  have he' : g*x₀*g⁻¹=x := he
  have hb : x*y*x=(g*k*g⁻¹)*u := by
    rw [←he']
    calc
      _ = g*(x₀*y₀*x₀)*g⁻¹ := by dsimp [y]; group
      _ = g*(k*t j)*g⁻¹ := by rw [hbraid]
      _ = _ := by dsimp [u]; group
  have hk' : g*k*g⁻¹∈cartan c := (mem_normalizer_iff.mp (hnorm hg) k).mp hk
  have huab : u • a=b := by
    simpa only [SimpleGraph.Walk.getVert_zero,Nat.sub_zero,←hlen,SimpleGraph.Walk.getVert_length]
      using hrev 0 (Nat.zero_le _)
  refine ⟨y,hy,?_,?_,?_,?_⟩
  · rw [←he']
    calc
      _ = g*(x₀*x₀)*g⁻¹ := by group
      _ = 1 := by rw [hxx,mul_one,mul_inv_cancel]
  · calc
      _ = g*(y₀*y₀)*g⁻¹ := by dsimp [y]; group
      _ = 1 := by rw [hyy,mul_one,mul_inv_cancel]
  · have hm : x*y=(MulAut.conj g) (x₀*y₀) := by rw [←he']; dsimp [y]; simp [mul_assoc]
    rw [hm]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _).trans ho
  · rw [hb,mul_smul,huab]
    exact reflectionApartment_fixed c t (fullCartanReflections_normalize ds) _ hk' _
      (hpT _ (by simpa only [SimpleGraph.Walk.getVert_length] using p.getVert_mem_support p.length))

/-- Both natural source lengths satisfy exchange on the actual chosen apartment;
no trivial-center or common-core-centralizer premise is used. -/
theorem full_profile_source_exchange :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph A)
      (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))) n := by
  have hN : apartmentGroup c (fullCartanPathRoots ds)=N := by
    simp only [apartmentGroup,reflectionGroup,fullCartanRoots_reflection]
  rw [hN]
  intro a b p hp hl hT g hg hmove
  have hfix : cartan c≤pathFixer (X := (reducedAmalgam L S).Universal) p := by
    intro k hk j _
    exact reflectionApartment_fixed c t (fullCartanReflections_normalize ds) k hk _
      (hT _ (p.getVert_mem_support j))
  have hf := apartment_path_factorization h c n (fullCartanPathLength_gt ds) t
    (fullCartanReflections_fix ds) (fullCartanReflections_move ds) (fullCartanReflections_square ds)
    (fullCartanReflections_normalize ds) (fullCartanProfiles_path_transitive ds)
    (fullCartanProfiles_thickness ds) (p.drop n)
    (by have hn := fullCartanPathLength_gt ds; rw [SimpleGraph.Walk.drop_length,hl]; omega)
    (by
      intro z hz
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
      exact hT z (List.mem_of_mem_drop hz))
  have hgF : g∈(pathFixer (X := (reducedAmalgam L S).Universal) (p.drop n) : Set _) := by
    intro j hj
    rw [SimpleGraph.Walk.drop_length,hl] at hj
    rw [SimpleGraph.Walk.drop_getVert]
    exact hg (n+j) (by omega) (by omega)
  rw [hf] at hgF
  obtain ⟨x,hx,k,hk,he⟩ := hgF
  have hka : k • a=a := by
    simpa only [SimpleGraph.Walk.getVert_zero] using hfix hk 0 (Nat.zero_le _)
  have hgxa : g • a=x • a := by rw [←he,mul_smul,hka]
  have hxn : x≠1 := by
    intro hx1
    exact hmove (by rw [hgxa,hx1,one_smul])
  obtain ⟨y,hy,hxx,_,_,hbraid⟩ := apartment_root_pairs ds p hp hl hT x hx hxn
  have hxb : x • b=b := (pathRoot_fixes (p.drop n) hx).1
  refine ⟨y,?_,?_⟩
  · intro j hj
    have hh := (Subgroup.pCoreIn_le 2 _ hy) j
      (show j≤(p.take n).length by rw [SimpleGraph.Walk.take_length,hl]; omega)
    simpa only [SimpleGraph.Walk.take_getVert,min_eq_right hj] using hh
  · rw [hgxa]
    calc
      y • (x • a) = (x*(x*y*x)) • a := by rw [←mul_smul]; congr 1; rw [←mul_assoc,←mul_assoc,hxx,one_mul]
      _ = b := by rw [mul_smul,hbraid,hxb]

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
