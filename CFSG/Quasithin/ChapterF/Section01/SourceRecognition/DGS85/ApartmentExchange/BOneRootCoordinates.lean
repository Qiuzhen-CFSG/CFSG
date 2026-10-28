module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneSourceMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathFactorization
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic

/-!
# Coordinates of the actual b=1 apartment roots

Every two-subgroup of the original universal Borel lies in its normal
Sylow subgroup, hence in the literal lifted Chapter 10 actor. The covering
identifies the actor quotient kernel with the endpoint two-core. A canonical
path radical has nontrivial quotient image because it moves an exit whereas
the endpoint core fixes all neighbors. The simultaneously marked full Cartan
then makes this image the whole upper unipotent group. Odd next-path fixers
separate the radical from the endpoint core.

Both orientations use the actual reflection paths and the same original
covering. The markings are constructed from the original Borel; no root-image
or diagonal-surjectivity premise is added. Triviality of the original actor
center selects r=3 by uniqueness of the source path parameter. The remaining
midpoint transport and opposite-root construction are separate steps toward
coordinates on the canonical length-six paths.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.156--157,
(14.1), pp.210--211, and (14.13), p.218.
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
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

include h in
/-- Every two-subgroup of the full universal Borel lies in its actual normal Sylow subgroup. -/
theorem isTwo_le_twoGroup {R : Subgroup (reducedAmalgam L S).Universal}
    (hR : IsPGroup 2 R) (hRB : R ≤ originalMiddle (reducedAmalgam L S)) :
    R ≤ twoGroup L S := by
  let U := (reducedSylow L S).subgroupOf (commonBorel L (reducedSylow L S))
  let T : Sylow 2 (commonBorel L (reducedSylow L S)) :=
    (reduced_hypothesis h).S_isP.comap_subtype.toSylow
      (reduced_hypothesis h).commonBorel_odd_index
  let : U.Normal := reduced_sylow_normal h
  have he := (hR.comap_of_injective (middleMap L S) middleMap_injective).inf_normalizer_sylow T
  have hle : R.comap (middleMap L S) ≤ U := by
    change R.comap (middleMap L S) ⊓ normalizer (U : Set _) =
      R.comap (middleMap L S) ⊓ U at he
    rw [normalizer_eq_top, inf_top_eq] at he
    exact inf_eq_left.mp he.symm
  have hm := map_mono (f := middleMap L S) hle
  rw [map_comap_eq_self (show R ≤ (middleMap L S).range from hRB)] at hm
  exact hm

include h in
/-- An actual path radical ending at the original oriented edge lies in the Borel two-group. -/
theorem aligned_pathRoot_le_twoGroup {i : Bool}
    {a : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hprev : p.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) :
    pathRoot (X := (reducedAmalgam L S).Universal) p ≤ twoGroup L S := by
  apply isTwo_le_twoGroup h (pathRoot_isTwo p)
  have he := pathRoot_fixes (X := (reducedAmalgam L S).Universal) p
  rw [hprev,stabilizer_base,stabilizer_base] at he
  rw [originalMiddle,←Universal.overlap_eq _
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases i
  · exact he
  · exact le_trans he (by rw [inf_comm]; rfl)

variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable (i : Bool)
variable (d : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
  (base (reducedFamily L S) (!i)) F W)

/-- The marked covering maps the whole universal endpoint two-core onto the original one. -/
theorem universalBOne_core_map :
    ((Universal.cosetFamily (reducedAmalgam L S) i).pCoreIn 2).map (bOne_tree_map h) =
      Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let P := Universal.cosetFamily (reducedAmalgam L S) i
  let f : P →* reducedFamily L S i :=
    { toFun x := ⟨bOne_tree_map h x, by
        rw [←(bOne_tree_cover h).map_eq i]
        exact mem_map_of_mem _ x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ _ _) }
  let e : P ≃* reducedFamily L S i :=
    MulEquiv.ofBijective f
      ⟨by
        intro x y he
        exact (bOne_tree_cover h).injective i (congrArg Subtype.val he), by
        intro y
        have hy : (y:G₀ L S) ∈ P.map (bOne_tree_map h) := by
          rw [(bOne_tree_cover h).map_eq i]
          exact y.property
        obtain ⟨x,hx,he⟩ := hy
        exact ⟨⟨x,hx⟩,Subtype.ext he⟩⟩
  change ((pCore 2 P).map P.subtype).map (bOne_tree_map h) = _
  rw [map_map]
  have he : (bOne_tree_map h).comp P.subtype = (reducedFamily L S i).subtype.comp e.toMonoidHom := rfl
  rw [he,←map_map,pCore_map_iso]
  rw [Q,RankTwo.stabilizer,stabilizer_base]
  rfl

/-- Inside the endpoint, the original covering detects exact membership in its two-core. -/
theorem universalBOne_mem_core_iff (x : (reducedAmalgam L S).Universal)
    (hx : x ∈ Universal.cosetFamily (reducedAmalgam L S) i) :
    bOne_tree_map h x ∈ Q (reducedFamily L S) (base (reducedFamily L S) i) ↔
      x ∈ (Universal.cosetFamily (reducedAmalgam L S) i).pCoreIn 2 := by
  rw [←universalBOne_core_map h i]
  constructor
  · rintro ⟨y,hy,he⟩
    have hh := (bOne_tree_cover h).injective i
      (a₁ := ⟨y,pCoreIn_le 2 _ hy⟩) (a₂ := ⟨x,hx⟩) he
    have hyx : y = x := congrArg Subtype.val hh
    exact hyx ▸ hy
  · exact mem_map_of_mem _

/-- The full endpoint two-core is contained in the literal lifted Chapter 10 actor. -/
theorem universalBOne_core_le :
    (Universal.cosetFamily (reducedAmalgam L S) i).pCoreIn 2 ≤ universalBOneActor h i d := by
  intro x hx
  exact ⟨d.core_le ((universalBOne_mem_core_iff h i x (pCoreIn_le 2 _ hx)).mpr hx),
    pCoreIn_le 2 _ hx⟩

/-- The unchanged actor quotient has precisely the actual endpoint two-core as kernel. -/
theorem universalBOne_kernel_eq : (universalBOneQuotient h i d).ker =
    ((Universal.cosetFamily (reducedAmalgam L S) i).pCoreIn 2).subgroupOf
      (universalBOneActor h i d) := by
  ext x
  change universalBOneActorEquiv h i d x ∈ d.quotient.ker ↔ _
  rw [d.kernel]
  exact universalBOne_mem_core_iff h i x x.property.2

include h in
/-- The path radical lies in the same actor as the source quotient. -/
theorem aligned_pathRoot_le_actor
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    {a : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hprev : p.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) :
    pathRoot (X := (reducedAmalgam L S).Universal) p ≤ universalBOneActor h i d :=
  (aligned_pathRoot_le_twoGroup h p hprev).trans (twoGroup_le_bOneActor h i d hactor)

include h in
/-- The source neighbor marking places the actual two-group root image in the upper root. -/
theorem aligned_pathRoot_image_le_upper (m : SL(2,F))
    (htri : ∀ k : d.actor, (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
      (base (reducedFamily L S) (!i)) → (m*d.quotient k*m⁻¹).val 1 0=0)
    {a : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hprev : p.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i)) :
    ((pathRoot (X := (reducedAmalgam L S).Universal) p).subgroupOf
      (universalBOneActor h i d)).map ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d)) ≤
        Matrix.SpecialLinearGroup.upperUnipotent F := by
  let R := ((pathRoot (X := (reducedAmalgam L S).Universal) p).subgroupOf
      (universalBOneActor h i d)).map ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d))
  have hRB : R ≤ Matrix.SpecialLinearGroup.rankOneBorel F := by
    rintro y ⟨x,hx,rfl⟩
    apply (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff _).mpr
    apply htri (universalBOneActorEquiv h i d x)
    have hn := (pathRoot_fixes p hx).2
    rw [hprev,stabilizer_base] at hn
    rw [RankTwo.stabilizer,stabilizer_base,←(bOne_tree_cover h).map_eq (!i)]
    exact mem_map_of_mem _ hn
  have he := ((pathRoot_isTwo (X := (reducedAmalgam L S).Universal) p).comap_subtype.map
    ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d))).inf_normalizer_sylow
      (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  change R ⊓ Matrix.SpecialLinearGroup.rankOneBorel F =
    R ⊓ Matrix.SpecialLinearGroup.upperUnipotent F at he
  rw [inf_eq_left.mpr hRB] at he
  exact inf_eq_left.mp he.symm

include h in
/-- Exit transitivity and the full diagonal Cartan exhaust all upper-root parameters. -/
theorem aligned_pathRoot_image_eq_upper (m : SL(2,F))
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (htri : ∀ k : d.actor, (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
      (base (reducedFamily L S) (!i)) → (m*d.quotient k*m⁻¹).val 1 0=0)
    (hfull : ∀ b : F, ∀ hb : b≠0, Matrix.SpecialLinearGroup.diag2 b hb∈
      ((cartan c).subgroupOf (universalBOneActor h i d)).map
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d)))
    {a : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (hp : p.IsPath)
    (hprev : p.penultimate = base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (hK : cartan c ≤ pathFixer (X := (reducedAmalgam L S).Universal) p)
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) (p.length+1))
    (v : SourceVertex (reducedAmalgam L S))
    (hv : (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) v)
    (hvprev : v≠p.penultimate) (hKv : ∀ k∈cartan c, k • v=v)
    (hthick : ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
      z≠p.penultimate ∧ z≠v) :
    ((pathRoot (X := (reducedAmalgam L S).Universal) p).subgroupOf
      (universalBOneActor h i d)).map
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d)) =
          Matrix.SpecialLinearGroup.upperUnipotent F := by
  let A := reducedAmalgam L S
  let H := universalBOneActor h i d
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d)
  let R := pathRoot (X := A.Universal) p
  let U := (R.subgroupOf H).map π
  have hRH : R ≤ H := aligned_pathRoot_le_actor h i d hactor p hprev
  have hRU : U ≤ Matrix.SpecialLinearGroup.upperUnipotent F :=
    aligned_pathRoot_image_le_upper h i d m htri p hprev
  have hacyc := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  obtain ⟨z,hz,hzprev,hzv⟩ := hthick
  obtain ⟨r,hr,hrv⟩ := pathRoot_transitive_exits hacyc p hp htrans (cartan c)
    hv hvprev hKv (pathFixer_factorization c h p hprev hK) z hz hzprev
  have hπr : π ⟨r,hRH hr⟩ ≠ 1 := by
    intro he
    have hk : (⟨r,hRH hr⟩ : H)∈π.ker := he
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj m).injective,
      universalBOne_kernel_eq] at hk
    have hQr : r∈(MulAction.stabilizer A.Universal
        (base (Universal.cosetFamily A) i)).pCoreIn 2 := by
      rw [stabilizer_base]
      exact hk
    have hrv' : r • v = v := universal_vertex_core_fixes_neighbors h _ _ hv hQr
    exact hzv (hrv.symm.trans hrv')
  have hKn : cartan c ≤ normalizer (R : Set A.Universal) := by
    have hn := (pCore 2 (pathFixer (X := A.Universal) p)).le_normalizer_map
      (pathFixer (X := A.Universal) p).subtype
    have hn' : pathFixer (X := A.Universal) p ≤ normalizer (R : Set A.Universal) := by
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,R,pathRoot,pCoreIn] using hn
    exact hK.trans hn'
  have hdiag (b : F) (hb : b≠0) : Matrix.SpecialLinearGroup.diag2 b hb∈normalizer (U : Set SL(2,F)) := by
    obtain ⟨k,hk,hπk⟩ := hfull b hb
    rw [←hπk]
    apply (R.subgroupOf H).le_normalizer_map π
    exact mem_map_of_mem π (R.le_normalizer_comap H.subtype (hKn hk))
  apply le_antisymm hRU
  intro x hx
  obtain ⟨b,rfl⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F x).mp hx
  let w : SL(2,F) := π ⟨r,hRH hr⟩
  have hw : w∈U := mem_map_of_mem π (show (⟨r,hRH hr⟩ : H)∈R.subgroupOf H from hr)
  have hwne : w≠1 := hπr
  obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F w).mp (hRU hw)
  have hane : a≠0 := by
    intro he
    apply hwne
    rw [←ha,he,Matrix.SpecialLinearGroup.transvection_coeff_zero]
  by_cases hb : b=0
  · rw [hb,Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact U.one_mem
  obtain ⟨s,hs⟩ := isSquare_of_charTwo' (b/a)
  have hsne : s≠0 := by
    intro he
    simp [he,div_eq_zero_iff,hb,hane] at hs
  have hsa : s^2*a=b := by rw [sq,←hs,div_mul_cancel₀ _ hane]
  have hm := (mem_normalizer_iff.mp (hdiag s hsne) w).mp hw
  rw [←ha,Matrix.SpecialLinearGroup.diag_conj_upper,hsa] at hm
  exact hm

include h in
/-- Odd next-path fixers separate the actual path radical from the endpoint two-core. -/
theorem pathRoot_disjoint_endpoint_core
    {a b v : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hp : p.IsPath)
    (hv : (sourceGraph (reducedAmalgam L S)).Adj b v) (hvprev : v≠p.penultimate)
    (hodd : ∀ {u w} (q : (sourceGraph (reducedAmalgam L S)).Walk u w),
      q.IsPath → q.length=p.length+1 → Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) q))) :
    pathRoot (X := (reducedAmalgam L S).Universal) p ⊓
      (MulAction.stabilizer (reducedAmalgam L S).Universal b).pCoreIn 2 = ⊥ := by
  have hacyc := (Universal.cosetGraph_isTree (reducedAmalgam L S)
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hvnew : v∉p.support := fun hm => hvprev (hacyc.eq_penultimate_of_adj_end hp hv hm)
  have hdis := pathRoot_inf_stabilizer_eq_bot (X := (reducedAmalgam L S).Universal) p hv
    (hodd (p.concat hv) (hp.concat hvnew hv) (by rw [SimpleGraph.Walk.length_concat]))
  apply le_bot_iff.mp
  exact (inf_le_inf_left _ (universal_vertex_core_fixes_neighbors h _ _ hv)).trans hdis.le

universe uF
variable {h c}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)

/-- Construct root containment, kernel disjointness, and full root/Cartan markings at either original endpoint. -/
theorem fullCartanRoots_source_coordinates (j : Bool) :
    (fullCartanPathRoots ds j).root ≤ universalBOneActor h j (ds j).data ∧
    (fullCartanPathRoots ds j).root ⊓
      (Universal.cosetFamily (reducedAmalgam L S) j).pCoreIn 2 = ⊥ ∧
    ∃ m : SL(2,(ds j).F),
      (((fullCartanPathRoots ds j).root).subgroupOf (universalBOneActor h j (ds j).data)).map
        ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data)) =
          Matrix.SpecialLinearGroup.upperUnipotent (ds j).F ∧
      (∀ b : (ds j).F, ∀ hb : b≠0, Matrix.SpecialLinearGroup.diag2 b hb∈
        ((cartan c).subgroupOf (universalBOneActor h j (ds j).data)).map
          ((MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h j (ds j).data))) ∧
      (∀ k : universalBOneActor h j (ds j).data, (k:(reducedAmalgam L S).Universal)∈cartan c →
        ∃ a : (ds j).F, ∃ ha : a≠0, m*universalBOneQuotient h j (ds j).data k*m⁻¹=
          Matrix.SpecialLinearGroup.diag2 a ha) := by
  let A := reducedAmalgam L S
  let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
    (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
    (fullCartanPathLength ds) (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) j
  have hroot : (fullCartanPathRoots ds j).root = pathRoot (X := A.Universal) p.walk :=
    fullCartanRoots_root ds j
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (ds false).data (ds true).data
  have hneighbor : Q (reducedFamily L S) (base (reducedFamily L S) (!j))=
      Z (reducedFamily L S) (base (reducedFamily L S) (!j)) := by
    cases j
    · exact hc.2
    · exact hc.1
  obtain ⟨m,hdiag,hfull,htri,_⟩ := exists_full_cartan_neighbor_marking h c j (ds j).data
    (ds j).actor_eq hneighbor
  let v := fullCartanReflections ds j • base (Universal.cosetFamily A) (!j)
  have hv : (sourceGraph A).Adj (base (Universal.cosetFamily A) j) v := by
    have he : (sourceGraph A).Adj (base (Universal.cosetFamily A) j)
        (base (Universal.cosetFamily A) (!j)) :=
      ⟨by change j≠!j; cases j <;> decide,incident_base _ _ _⟩
    have hm := source_action A (fullCartanReflections ds j) he
    change (sourceGraph A).Adj (fullCartanReflections ds j •
      base (Universal.cosetFamily (reducedAmalgam L S)) j) v at hm
    rw [fullCartanReflections_fix] at hm
    exact hm
  have hvprev : v≠p.walk.penultimate := by rw [p.previous]; exact fullCartanReflections_move ds j
  have hodd : ∀ {u w} (q : (sourceGraph A).Walk u w), q.IsPath → q.length=p.walk.length+1 →
      Odd (Nat.card (pathFixer (X := A.Universal) q)) := by
    intro u w q hq hlen
    exact fullCartanProfiles_path_odd ds q hq (hlen.trans (congrArg (·+1) p.length_eq))
  rw [hroot]
  refine ⟨aligned_pathRoot_le_actor h j (ds j).data (ds j).actor_eq p.walk p.previous,?_,m,?_,hfull,hdiag⟩
  · simpa only [stabilizer_base] using pathRoot_disjoint_endpoint_core h p.walk p.isPath hv hvprev hodd
  · apply aligned_pathRoot_image_eq_upper h c j (ds j).data m (ds j).actor_eq htri hfull
      p.walk p.isPath p.previous p.fixed
      (by rw [p.length_eq]; exact fullCartanProfiles_path_transitive ds) v hv hvprev
    · intro k hk
      exact reflectionApartment_fixed c (fullCartanReflections ds) (fullCartanReflections_normalize ds)
        k hk v (cartanApartment_preserves A _ (reflectionGroup_mem c _ j)
          (cartanApartment_base A _ (!j)))
    · simpa only [p.previous] using fullCartanProfiles_thickness ds j

/-- The original centerless branch forces the chosen source regularity length to be three. -/
theorem fullCartanPathLength_eq_three_of_center_eq_bot
    (hc : centerIn (ds false).data.actor=⊥) : fullCartanPathLength ds=3 := by
  rcases original_bOne_tree_path_alternatives h (ds false).data (ds true).data
    (ds false).actor_eq (ds true).actor_eq (ds false).dimension (ds true).dimension with
    ⟨_,_,hp,_,_⟩ | ⟨hcard,_,_,_,_⟩
  · exact (fullCartanProfiles_parameters ds).1.unique hp.1
  · rw [←reduced_actor_center_map,hc,Subgroup.map_bot] at hcard
    have hh : Nat.card (ds false).F=1 := by simpa using hcard.symm
    exact (Finite.one_lt_card (α := (ds false).F)).ne' hh |>.elim


end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
