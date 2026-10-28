module
public import CFSG.Quasithin.Chapter14.Section09.StrictActorKernel.SecondCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.PathCoreControl


/-!
# The literal middle six-path root and the strict actor kernel

Local core control places a path radical in every interior vertex core.
Conversely, the intersection of the five interior cores of a six-path is
normal in its path fixer and is a two-group. The original covering lifts
its elements, using local bijectivity along the path, and is injective on
the fixer. Thus the image of the literal path radical is exactly this
five-core intersection.

For a centered six-path with the source opposite transporter, the natural
center geometry identifies this intersection with the original four-core
residual. This proves D = Z_i R_(i-3)^+ and disjointness, preserving Z_i,
the actual path and the original covering map. The final application puts
that decomposition into the kernel formula for the same strict half-path
actor. The selected source roots also receive the five-core formula.

The transporter equations are explicit path equations, not a natural-action
assumption. Their construction for every path in the chosen strict apartment,
the equality of the actor kernel with Z_i, its natural action, and the
compatible reversing reflection remain required for full apartment exchange.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.4), pp.155--156; (14.1), p.210; (14.7), p.214; (14.9)(c),
pp.215--216. The middle root on a twelve-path is its segment from index 3
to index 9: j=i-r/2=i-3, with i=6.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
namespace CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.DGS85
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment Assembly.BTwoSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
variable (h : HypothesisF11 L S) {v w : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) v w)
  (hne : ⁅Z (reducedFamily L S) v,Z (reducedFamily L S) w⁆ ≠ ⊥)

include h hc hne in
/-- Every interior source core contains the image of the literal path radical. -/
theorem source_pathRoot_image_le_interior_core
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hp : p.IsPath)
    (j : ℕ) (hj : 0<j) (hjl : j<p.length) :
    (pathRoot (X := (A).Universal) p).map (bOne_tree_map h)  ≤
      Q F ((bOne_tree_cover h).vertex (p.getVert j)) := by
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let R := pathRoot (X := (A).Universal) p
  have hprev := p.adj_getVert_succ (by omega : j-1<p.length)
  rw [show j-1+1=j by omega] at hprev
  have hnext := p.adj_getVert_succ hjl
  have hdiff : cov.vertex (p.getVert (j-1)) ≠ cov.vertex (p.getVert (j+1)) := by
    intro he
    have he' := (cov.neighbor_bijective (p.getVert j)).1
      (a₁:=⟨_,hprev.symm⟩) (a₂:=⟨_,hnext⟩) (Subtype.ext he)
    have hh := hp.getVert_injOn (by omega : j-1 ≤ p.length) (by omega : j+1 ≤ p.length)
      (congrArg Subtype.val he')
    omega
  have hfix (k : ℕ) (hk : k ≤ p.length) :
      R.map f ≤ stabilizer F (cov.vertex (p.getVert k)) := by
    rintro _ ⟨x,hx,rfl⟩
    change f x • cov.vertex (p.getVert k)=_
    rw [←cov.vertex_smul]
    exact congrArg cov.vertex ((pCoreIn_le 2 _ hx) k hk)
  exact original_noncommuting_two_neighbor_core h hc hne
    (cov.hom.map_adj hprev) (cov.hom.map_adj hnext) hdiff
    (R.map f) ((pathRoot_isTwo p).map f)
    (hfix _ (by omega)) (hfix _ (by omega)) (hfix _ (by omega))

include h hc hne in
/-- The six-path root has exactly the five interior source cores as its image. -/
theorem source_six_pathRoot_image_eq
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length=6) :
    (pathRoot (X := (A).Universal) p).map (bOne_tree_map h) =
      ⨅ i : Fin 5, Q F ((bOne_tree_cover h).vertex (p.getVert (i.val+1))) := by
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let P := pathFixer (X := (A).Universal) p
  let N := ⨅ i : Fin 5, Q F (cov.vertex (p.getVert (i.val+1)))
  have hNQ (i : ℕ) (hi : 1 ≤ i) (hi' : i ≤ 5) :
      N ≤ Q F (cov.vertex (p.getVert i)) := by
    have hh := iInf_le (fun i : Fin 5 => Q F (cov.vertex (p.getVert (i.val+1))))
      (⟨i-1,by omega⟩ : Fin 5)
    simpa only [show i-1+1=i by omega] using hh
  have hNfix (k : ℕ) (hk : k ≤ 6) : N ≤ stabilizer F (cov.vertex (p.getVert k)) := by
    by_cases h0 : k=0
    · subst k
      exact (hNQ 1 (by decide) (by decide)).trans
        ((source_Z_Q_U (reduced_triple h) _).2.trans
          ((ballKernel_one_le_edge F (cov.hom.map_adj
            (p.adj_getVert_succ (i:=0) (by omega))).symm).trans inf_le_right))
    by_cases h6 : k=6
    · subst k
      exact (hNQ 5 (by decide) (by decide)).trans
        ((source_Z_Q_U (reduced_triple h) _).2.trans
          ((ballKernel_one_le_edge F (cov.hom.map_adj
            (p.adj_getVert_succ (i:=5) (by omega)))).trans inf_le_right))
    exact (hNQ k (by omega) (by omega)).trans (Q_le_stabilizer F _)
  let ψ : P  →* G₀ L S := f.comp P.subtype
  have hψ : Function.Injective ψ := by
    intro x y he
    have hh := (cov.stabilizerEquiv (p.getVert 1)).injective
      (a₁:=⟨x,x.property 1 (by omega)⟩)
      (a₂:=⟨y,y.property 1 (by omega)⟩) (Subtype.ext he)
    exact Subtype.ext (congrArg (fun z : stabilizer (Universal.cosetFamily A) (p.getVert 1) =>
      (z : (A).Universal)) hh)
  let E := N.comap ψ
  have hEtwo : IsPGroup 2 E :=
    ((isPGroup_pCoreIn 2 (stabilizer F (cov.vertex (p.getVert 1)))).to_le
      (hNQ 1 (by decide) (by decide))).comap_of_injective ψ hψ
  have hn : E.Normal := by
    constructor
    intro x hx g
    change ψ (g*x*g⁻¹)∈N
    simp only [map_mul,map_inv]
    apply mem_iInf.mpr
    intro i
    have hg : ψ g∈stabilizer F (cov.vertex (p.getVert (i.val+1))) := by
      change f g.val • cov.vertex (p.getVert (i.val+1))=_
      rw [←cov.vertex_smul]
      exact congrArg cov.vertex (g.property _ (by omega))
    exact (mem_normalizer_iff.mp
      (CommutingNontrivial.stabilizer_normalizes_Q F _ hg) _).mp
      (mem_iInf.mp hx i)
  let := hn
  have hEp : E ≤ pCore 2 P := le_sSup ⟨inferInstance,hEtwo⟩
  apply le_antisymm
  · apply le_iInf
    intro i
    exact source_pathRoot_image_le_interior_core h hc hne p hp (i.val+1)
      (by omega) (by omega)
  · intro y hy
    obtain ⟨x,hxy⟩ := (cov.stabilizerEquiv (p.getVert 1)).surjective
      ⟨y,hNfix 1 (by decide) hy⟩
    have hxy' : f x.val=y := congrArg Subtype.val hxy
    have hx0 : x.val • p.getVert 0=p.getVert 0 :=
      cov.fixes_neighbor_of_image (p.adj_getVert_succ (i:=0) (by omega)).symm
        x.val x.property (hxy' ▸ hNfix 0 (by decide) hy)
    have hxfix (k : ℕ) (hk : k ≤ 6) : x.val • p.getVert k=p.getVert k := by
      induction k with
      | zero => exact hx0
      | succ k ih =>
        exact cov.fixes_neighbor_of_image (p.adj_getVert_succ (i:=k) (by omega))
          x.val (ih (by omega)) (hxy' ▸ hNfix (k+1) hk hy)
    have hxP : x.val∈P := fun k hk => hxfix k (by omega)
    have hxE : (⟨x.val,hxP⟩ : P)∈E := by
      change f x.val∈N
      rwa [hxy']
    exact ⟨x.val,mem_map_of_mem P.subtype (hEp hxE),hxy'⟩

include h hc hne in
/-- The four-core residual of the original opposite-center geometry is the
literal six-path radical, under the same covering. -/
theorem source_six_pathRoot_residual
    (hb : b F = 2) {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hl : p.length=6)
    (hv : (bOne_tree_cover h).vertex (p.getVert 3)=v)
    (hw : (bOne_tree_cover h).vertex (p.getVert 5)=w)
    (g : graphLocalGroup F v)
    (hg₂ : (g : G₀ L S) • (bOne_tree_cover h).vertex (p.getVert 4)=
      (bOne_tree_cover h).vertex (p.getVert 2))
    (hg₁ : (g : G₀ L S) • w=(bOne_tree_cover h).vertex (p.getVert 1)) :
    let R := (pathRoot (X := (A).Universal) p).map (bOne_tree_map h)
    let D₀ := D F ((bOne_tree_cover h).vertex (p.getVert 4))
      ((bOne_tree_cover h).vertex (p.getVert 2))
    R = bTwoResidual F ((bOne_tree_cover h).vertex (p.getVert 4))
      ((bOne_tree_cover h).vertex (p.getVert 2)) w (g • w) ∧
      D₀=Z F v ⊔ R ∧ Disjoint (Z F v) R := by
  intro R D₀
  let cov := bOne_tree_cover h
  let z (i : ℕ) := cov.vertex (p.getVert i)
  have hvm : (graph F).Adj v (z 4) := by
    have hh := cov.hom.map_adj (p.adj_getVert_succ (i:=3) (by omega))
    change (graph F).Adj (cov.vertex (p.getVert 3)) (z 4) at hh
    rwa [hv] at hh
  have hmw : (graph F).Adj (z 4) w := by
    have hh := cov.hom.map_adj (p.adj_getVert_succ (i:=4) (by omega))
    change (graph F).Adj (z 4) (cov.vertex (p.getVert 5)) at hh
    rwa [hw] at hh
  have hne₂ : z 2 ≠ z 4 := by
    intro he
    have hh := (cov.neighbor_bijective (p.getVert 3)).1
      (a₁:=⟨_,(p.adj_getVert_succ (i:=2) (by omega)).symm⟩)
      (a₂:=⟨_,p.adj_getVert_succ (i:=3) (by omega)⟩) (Subtype.ext he)
    have hi := hp.getVert_injOn (by omega : 2≤p.length) (by omega : 4≤p.length)
      (congrArg Subtype.val hh)
    omega
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ := reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  let _ := f
  let _ := fin
  let _ := ch
  let _ := alg
  let g' : c.actor := ⟨g,hactor.symm ▸ g.property⟩
  have hop : c.quotient g' ∉ normalizer (c.imageSylow : Set _) := by
    intro hm
    exact hne₂ (hg₂.symm.trans (c.normalizer_fixes_neighbor (reduced_triple h) g' hm))
  obtain ⟨d,hd,hker⟩ := c.exists_oppositeGeometry (reduced_triple h)
    (reduced_kernel_sylow h) hb g' hg₂ hop
  have hω := c.omega_eq_bot_of_central_neighbor (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) hactor
    (reduced_bTwo_middle_central h hc hne hb hvm hmw)
  have hR : R=d.residual := by
    rw [show R=(pathRoot (X := (A).Universal) p).map (bOne_tree_map h) from rfl,
      source_six_pathRoot_image_eq h hc hne p hp hl]
    change (⨅ i : Fin 5, Q F (z (i.val+1))) = (D F (z 4) (z 2) ⊓ Q F w) ⊓ Q F (g • w)
    apply le_antisymm
    · intro x hx
      have hx' (i : Fin 5) := mem_iInf.mp hx i
      exact ⟨⟨⟨hx' 3,hx' 1⟩,hw ▸ hx' 4⟩,hg₁.symm ▸ hx' 0⟩
    · intro x hx
      apply mem_iInf.mpr
      intro i
      fin_cases i
      · change x∈Q F (cov.vertex (p.getVert 1))
        rw [←hg₁]
        exact hx.2
      · exact hx.1.1.2
      · change x∈Q F (cov.vertex (p.getVert 3))
        rw [hv]
        exact d.separated hx.1.1
      · exact hx.1.1.1
      · change x∈Q F (cov.vertex (p.getVert 5))
        rw [hw]
        exact hx.1.2
  refine ⟨hR.trans (d.residual_eq_source (reduced_triple h)
    (reduced_kernel_sylow h) hb (hd.symm ▸ hω)),?_,?_⟩
  · exact (d.decomposition (reduced_triple h) (reduced_kernel_sylow h) hb).trans
      (congrArg (Z F v ⊔ ·) hR.symm)
  · rw [hR,disjoint_iff,inf_comm]
    exact bot_unique (hker.trans hω.le)

include h hc hne in
/-- In the twelve-path convention the middle root is the segment from
index 3 to index 9, exactly R_(i-3)^+ for midpoint index i=6. -/
theorem source_middle_six_pathRoot_image_eq
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length=12) :
    (pathRoot (X := (A).Universal) ((p.drop 3).take 6)).map (bOne_tree_map h) =
      ⨅ i : Fin 5, Q F ((bOne_tree_cover h).vertex (p.getVert (i.val+4))) := by
  rw [source_six_pathRoot_image_eq h hc hne ((p.drop 3).take 6)
    ((hp.drop 3).take 6) (by simp only [SimpleGraph.Walk.take_length,
      SimpleGraph.Walk.drop_length,hl]; decide)]
  congr 1
  funext i
  rw [SimpleGraph.Walk.take_getVert,min_eq_right (by omega : i.val+1≤6),
    SimpleGraph.Walk.drop_getVert]
  congr 3
  omega

variable {u : Vertex (reducedFamily L S)}
  (hc₀ : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne₀ : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb₀ : b (reducedFamily L S)=2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- The original selected roots themselves have this five-core image;
both endpoint markings and the selected apartment are unchanged. -/
theorem strict_source_root_image_eq (i : Bool) :
    ((strictSourceRoots h hc₀ hne₀ hb₀ hβu hns hlinear i).root).map (bOne_tree_map h) =
      ⨅ j : Fin 5, Q F ((bOne_tree_cover h).vertex
        ((strictSourcePath h hc₀ hne₀ hb₀ hβu hns hlinear i).walk.getVert (j.val+1))) := by
  rw [strictSourceRoots_root]
  exact source_six_pathRoot_image_eq h hc₀ hne₀ _
    (strictSourcePath h hc₀ hne₀ hb₀ hβu hns hlinear i).isPath
    (strictSourcePath h hc₀ hne₀ hb₀ hβu hns hlinear i).length_eq

/-- Apply the literal middle-root factorization to the same alpha actor
kernel used by the strict finite-quotient consumer. The transporter equations
refer to this path, and the printed nontrivial Cartan-kernel premise is retained. -/
theorem strict_source_alpha_actor_core_middle_root
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc₀ hne₀ hb₀ hβu hns hlinear)
    (hKn : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6)) ≠ ⊥)
    (h₆ : (bOne_tree_cover h).vertex (p.getVert 6)=base F false)
    (h₇ : (bOne_tree_cover h).vertex (p.getVert 7)=base F true)
    (h₈ : (bOne_tree_cover h).vertex (p.getVert 8)=u)
    (g : graphLocalGroup F (base F false))
    (hg₅ : (g : G₀ L S) • base F true=(bOne_tree_cover h).vertex (p.getVert 5))
    (hg₄ : (g : G₀ L S) • u=(bOne_tree_cover h).vertex (p.getVert 4)) :
    let R := halfPathActor (X := (A).Universal) p 6
    let φ := bOne_tree_map h
    let M := (pathRoot (X := (A).Universal) ((p.drop 3).take 6)).map φ
    (R.pCoreIn 2).map φ = R.map φ ⊓ (Z F (base F false) ⊔ M) ∧
      Disjoint (Z F (base F false)) M := by
  intro R φ M
  let cov := bOne_tree_cover h
  let q := (p.drop 3).take 6
  have hq (j : ℕ) (hj : j≤6) : q.getVert j=p.getVert (j+3) := by
    simp only [q,SimpleGraph.Walk.take_getVert,min_eq_right hj,
      SimpleGraph.Walk.drop_getVert,Nat.add_comm 3 j]
  have hql : q.length=6 := by
    simp only [q,SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,hl]
    decide
  have hqv : cov.vertex (q.getVert 3)=base F false := by rw [hq 3 (by decide)]; exact h₆
  have hqw : cov.vertex (q.getVert 5)=u := by rw [hq 5 (by decide)]; exact h₈
  have hqg₂ : (g : G₀ L S) • cov.vertex (q.getVert 4)=cov.vertex (q.getVert 2) := by
    rw [hq 4 (by decide),hq 2 (by decide),h₇]
    exact hg₅
  have hqg₁ : (g : G₀ L S) • u=cov.vertex (q.getVert 1) := by
    rw [hq 1 (by decide)]
    exact hg₄
  obtain ⟨_,hdec,hdis⟩ := source_six_pathRoot_residual h hc₀ hne₀ hb₀
    q ((hp.drop 3).take 6) hql hqv hqw g hqg₂ hqg₁
  change D F (cov.vertex (q.getVert 4)) (cov.vertex (q.getVert 2))=
    Z F (base F false) ⊔ M at hdec
  rw [hq 4 (by decide),hq 2 (by decide),h₇] at hdec
  have ht : (graph F).Adj (base F false) (cov.vertex (p.getVert 5)) := by
    have hh := cov.hom.map_adj (p.adj_getVert_succ (i:=5) (by omega)).symm
    change (graph F).Adj (cov.vertex (p.getVert 6)) (cov.vertex (p.getVert 5)) at hh
    rwa [h₆] at hh
  have htne : cov.vertex (p.getVert 5)≠base F true := by
    intro he
    have hh := (cov.neighbor_bijective (p.getVert 6)).1
      (a₁:=⟨_,(p.adj_getVert_succ (i:=5) (by omega)).symm⟩)
      (a₂:=⟨_,p.adj_getVert_succ (i:=6) (by omega)⟩) (Subtype.ext (he.trans h₇.symm))
    have hi := hp.getVert_injOn (by omega : 5≤p.length) (by omega : 7≤p.length)
      (congrArg Subtype.val hh)
    omega
  have hk := strict_source_alpha_actor_core_image h hc₀ hne₀ hb₀ hβu hns hlinear
    p hp hl hT hKn h₆ ht htne
  change (R.pCoreIn 2).map φ=R.map φ ⊓ D F (base F true) (cov.vertex (p.getVert 5)) at hk
  rw [hdec] at hk
  exact ⟨hk,hdis⟩

end CFSG.Quasithin.Chapter14.Section09.StrictActorKernel
