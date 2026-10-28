module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneOppositeCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanAlignment
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathMidpointCoordinates

/-!
# Actual midpoint coordinates and centerless natural apartment exchange

The marked apartment edge supplies one transporter from an original endpoint
to the midpoint of each even apartment path. Nonbranching aligns the canonical
half-path, and the transported chosen reflection reverses the whole path.
The same transporter carries both opposite roots, the original actor and its
literal quotient, its full two-core, and the whole Cartan marking. Thus both
canonical length-six paths have constructed natural coordinates.

The centerless alternative of original (10.5) identifies the full kernel
with the natural module and forces r=3. Applying the cubic exchange calculation
proves (14.13), with neither natural-path-coordinate witnesses nor exchange
callbacks assumed. The final source theorem derives both actor-center equalities from the
genuine source parameter r=3, s=4. The paired earlier full-Cartan profiles
still exclude the binary field. The r=4 central quotient is not used as a natural full kernel.

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
local notation "A" => reducedAmalgam L S
local notation "n" => fullCartanPathLength ds
local notation "t" => fullCartanReflections ds
local notation "N" => reflectionGroup c t
local notation "T" => cartanApartment A N

/-- The actual chosen whole-Cartan apartment has no branching. -/
theorem fullCartanApartment_noBranching : NoBranchingIn (sourceGraph A) T := by
  exact cartanApartment_noBranching A N (cartan c) (fullCartanPathRoots ds)
    (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    (fun i => by rw [fullCartanRoots_reflection]; exact reflectionGroup_mem c t i)
    (cartan_le c) (reflectionGroup_normalizes c t (fullCartanReflections_normalize ds))
    (by
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | ⟨i,rfl⟩)
      · exact Subgroup.subset_closure (Or.inl hx)
      · exact Subgroup.subset_closure (Or.inr ⟨i,(fullCartanRoots_reflection ds i)⟩))
    (fullCartanRoots_square ds)
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))

/-- Construct the original natural actor and both marked root images at the
midpoint of every actual length-six path in the chosen apartment. -/
theorem fullCartanApartment_natural_coordinates
    (hcenter : ∀ j, centerIn (ds j).data.actor=⊥)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hlen : p.length=2*n) (hpT : ∀ z∈p.support, z∈T) :
    Nonempty (NaturalPathCoordinates.{uF} p n (cartan c)) := by
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
  obtain ⟨hR,_,_⟩ := fullCartanRoots_source_coordinates ds j
  obtain ⟨m,himage,hfull,hS,hlower,honto,_⟩ := fullCartanRoots_opposite_coordinates ds j
  let H := universalBOneActor h j (ds j).data
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)
  have hcore : Q (reducedFamily L S) (base (reducedFamily L S) j)=
      Z (reducedFamily L S) (base (reducedFamily L S) j) := by
    have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
    cases j
    · exact hc.1
    · exact hc.2
  let nat := (universalBOneNaturalKernel h j (ds j).data hcore (hcenter j) (ds j).dimension).marking m
  have hH : H≤MulAction.stabilizer (reducedAmalgam L S).Universal v := by
    rw [stabilizer_base]
    exact inf_le_right
  have hQ : (MulAction.stabilizer (reducedAmalgam L S).Universal v).pCoreIn 2≤H := by
    rw [stabilizer_base]
    exact universalBOne_core_le h j (ds j).data
  have hker : π.ker=((MulAction.stabilizer (reducedAmalgam L S).Universal v).pCoreIn 2).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,
      universalBOne_kernel_eq,stabilizer_base]
  have hupper (x : H) (hx : (x:(reducedAmalgam L S).Universal)∈(fullCartanPathRoots ds j).root) :
      ∃ a : (ds j).F, π x=upper a := by
    have hm : π x∈Matrix.SpecialLinearGroup.upperUnipotent (ds j).F := by
      rw [←himage]
      exact mem_map_of_mem π hx
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent _ _).mp hm
    exact ⟨a,ha.symm⟩
  exact ⟨naturalPathCoordinates_of_conjugate p n (cartan c) H (fullCartanPathRoots ds j).root
    (pathRoot (X := (reducedAmalgam L S).Universal) (fullCartanOppositePath ds j)) hH hQ hR hS π hker nat
    hupper hlower honto hfull
    ⟨t j,(fullCartanReflections_source_clauses ds j).1⟩ g (hnorm hg) hgv hRmap hSmap hrev⟩

/-- Both canonical exchange paths carry constructed natural coordinates;
no coordinate witness remains as a source assumption. -/
theorem fullCartan_exchangePath_coordinates
    (hcenter : ∀ j, centerIn (ds j).data.actor=⊥) (i : Bool) :
    Nonempty (NaturalPathCoordinates.{uF}
      (exchangePath c n (fullCartanPathLength_gt ds) t (fullCartanReflections_fix ds)
        (fullCartanReflections_move ds) (fullCartanReflections_normalize ds) i) n (cartan c)) := by
  let r := reflectionPath c t (fullCartanReflections_fix ds) (fullCartanReflections_move ds)
    (fullCartanReflections_normalize ds) (2*n)
    (Nat.mul_pos (by decide) (lt_trans Nat.zero_lt_one (fullCartanPathLength_gt ds))) i
  apply fullCartanApartment_natural_coordinates ds hcenter r.walk.reverse r.isPath.reverse
    (by rw [SimpleGraph.Walk.length_reverse,r.length_eq])
  intro z hz
  exact r.supported z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)

/-- DGS (14.13) on the actual centerless characteristic-two source branch:
both half-path coordinate inputs and the odd-fixer input are discharged. -/
theorem fullCartan_source_exchange_of_center_eq_bot
    (hcenter : ∀ j, centerIn (ds j).data.actor=⊥) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph A)
      (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))) 3 := by
  have hn := fullCartanPathLength_eq_three_of_center_eq_bot ds (hcenter false)
  rw [←hn]
  intro a b p hp hl hT x hx hmove
  exact fullCartan_natural_exchange (fullCartan_exchangePath_coordinates ds hcenter)
    (fullCartanProfiles_path_odd ds) p hp hl hT x hx hmove

/-- The genuine r=3 source parameter excludes the central r=4 alternative
and makes both original actors centerless, with the original inclusions retained. -/
theorem fullCartan_centers_eq_bot_of_source_r_three
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    ∀ j, centerIn (ds j).data.actor=⊥ := by
  rcases original_bOne_tree_path_alternatives h (ds false).data (ds true).data
    (ds false).actor_eq (ds true).actor_eq (ds false).dimension (ds true).dimension with
    ⟨hc₀,hc₁,_,_,_⟩ | ⟨_,_,hp,_,_⟩
  · rw [←reduced_actor_center_map,map_eq_bot_iff_of_injective _ (G₀ L S).subtype_injective] at hc₀ hc₁
    intro j
    cases j
    · exact hc₀
    · exact hc₁
  · have he := hr.1.unique hp.1
    omega

/-- Source (14.13) for the supplied characteristic-two b=1 profiles, assuming
only the genuine source parameter r=3 (and s=r+1). The actor centers and both
natural-path-coordinate witnesses are derived, not extra target inputs. -/
theorem fullCartan_source_exchange_of_r_three
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4) :
    ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph A)
      (cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))) 3 := by
  intro a b p hp hl hT x hx hmove
  exact fullCartan_source_exchange_of_center_eq_bot ds
    (fullCartan_centers_eq_bot_of_source_r_three ds hr) p hp hl hT x hx hmove

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
