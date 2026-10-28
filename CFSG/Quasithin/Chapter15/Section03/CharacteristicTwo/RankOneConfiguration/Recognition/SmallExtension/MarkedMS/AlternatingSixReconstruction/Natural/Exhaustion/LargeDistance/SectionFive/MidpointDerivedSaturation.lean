module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SelectedKernelDerived
public import Theory.Representation.BinaryPermutation.ProperInvariant

/-!
# The whole moving cover in the midpoint core's derived subgroup

At distance four with the literal full point-core image, a large forward
slice gives a nonabelian selected common kernel. Its derived line lies in
the whole midpoint core's derived subgroup and is noncentral at the midpoint.

Every proper invariant subspace of either actual moving cover is fixed by
the full symmetric actor: for the natural module it is zero, and for the
augmentation core it is contained in the constant line. Thus any subgroup
normalized by the whole vertex stabilizer and containing a noncentral part
of the moving cover contains that entire cover. Applying this to the derived
subgroup of the midpoint core retains the order-thirty-two central attachment.

The original midpoint coordinates pull this containment back to the actual
replacement two-core. Its derived subgroup has order at least sixteen.
Mapping through the replacement inclusion also puts the entire original
moved layer in the original ambient two-core's derived subgroup. These are
lower bounds for the whole core, not the missing upper bounds for the
residual commutator [Q,Ltilde].

Source: Aschbacher--Smith B.3.1, printed p.83, and the selected-kernel
configuration in Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of
rank two* (1993), (3.10) and (5.12), printed pp.879--881 and 924--927.
The forced configuration still needs exclusion or the source normalization
and small-slice selection. The endpoint and opposite residual-core estimates,
other radical-image branches and unconditional distance-two conclusion
remain unproved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u


variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem cover_normal_subgroup_dichotomy
    (N : Subgroup d.overgroup) [N.Normal] :
    replacementMoved d ≤ N ∨ replacementMoved d ⊓ N ≤ center d.overgroup := by
  classical
  by_cases hle : replacementMoved d ≤ N
  · exact Or.inl hle
  right
  let W := NormalElementaryQuotient.subspace (replacementMoved d)
    (N.subgroupOf (replacementMoved d))
  have hW : ∀ g : Equiv.Perm (Fin 6), ∀ v ∈ W, coverAction s g v ∈ W := by
    intro g v hv
    obtain ⟨x,rfl⟩ := s.surjective g
    change ((coverAction s (s.projection x) v).toMul : d.overgroup) ∈ N
    rw [coverAction_conjugate]
    exact (inferInstance : N.Normal).conj_mem _ hv x
  have hproper : W ≠ ⊤ := by
    intro he
    apply hle
    intro x hx
    exact (show Additive.ofMul (⟨x,hx⟩ : replacementMoved d) ∈ W from he ▸ Submodule.mem_top)
  have hfixed : ∀ g : Equiv.Perm (Fin 6), ∀ v ∈ W, coverAction s g v = v := by
    rcases cover_model s with ⟨E,hE⟩ | ⟨E,hE⟩
    · let F := W.map E.toLinearMap
      have hF : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ F,
          naturalRepresentation (Fin 6) g.val v ∈ F := by
        rintro g _ ⟨v,hv,rfl⟩
        exact ⟨coverAction s g.val v,hW g.val v hv,hE g.val v⟩
      have hnF : F ≠ ⊤ := by
        intro he
        apply hproper
        apply top_unique
        intro v _
        obtain ⟨w,hw,heq⟩ := (show E v ∈ F from he ▸ Submodule.mem_top)
        exact E.injective heq ▸ hw
      have hzF := natural_invariant_eq_bot_of_ne_top (by decide : 5 ≤ Fintype.card (Fin 6)) F hF hnF
      intro g v hv
      have hvF : E v ∈ F := ⟨v,hv,rfl⟩
      rw [hzF] at hvF
      have hv0 : v = 0 := E.injective (((show E v = 0 from hvF)).trans E.map_zero.symm)
      rw [hv0,map_zero]
    · let F := W.map E.toLinearMap
      have hF : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ F,
          coreRepresentation (Fin 6) g.val v ∈ F := by
        rintro g _ ⟨v,hv,rfl⟩
        exact ⟨coverAction s g.val v,hW g.val v hv,hE g.val v⟩
      have hnF : F ≠ ⊤ := by
        intro he
        apply hproper
        apply top_unique
        intro v _
        obtain ⟨w,hw,heq⟩ := (show E v ∈ F from he ▸ Submodule.mem_top)
        exact E.injective heq ▸ hw
      intro g v hv
      apply E.injective
      rw [hE]
      exact core_proper_invariant_fixed (by decide : 5 ≤ Fintype.card (Fin 6)) F hF hnF
        g (E v) ⟨v,hv,rfl⟩
  rintro x ⟨hxW,hxN⟩
  apply mem_center_iff.mpr
  intro g
  have hh := congrArg (fun v : Additive (replacementMoved d) => (v.toMul : d.overgroup))
    (hfixed (s.projection g) (Additive.ofMul ⟨x,hxW⟩) hxN)
  rw [coverAction_conjugate] at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

include s in
/-- A noncentral subgroup of the actual moving cover forces any normal
subgroup containing it to contain the entire cover, including its central line. -/
theorem moving_le_normal_of_noncentral
    (hc : DistanceTwo.CentralLayer d) {c : Vertex d.radical}
    (hcol : color d.radical c = false)
    (A N : Subgroup (FreeAmalgam d.radical))
    (hAU : A ≤ U d.radical c) (hAN : A ≤ N)
    (hN : stabilizer d.radical c ≤ normalizer (N : Set (FreeAmalgam d.radical)))
    (hne : ¬ A ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) :
    U d.radical c ≤ N := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  let N₀ := N.comap i
  let : N₀.Normal := ⟨by
    intro x hx g
    change i (g*x*g⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (le_normalizer_iff.mp hN (i g) (hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩))) _ hx⟩
  rcases cover_normal_subgroup_dichotomy s N₀ with hle | hcentral
  · rw [←hiU]
    exact (map_mono hle).trans (map_comap_le _ _)
  · exfalso
    apply hne
    intro x hx y hy
    obtain ⟨v,hv,hvx⟩ := (hiU.symm ▸ hAU hx)
    obtain ⟨g,rfl⟩ := hir.symm ▸ hy
    have hvN : v ∈ N₀ := by change i v ∈ N; rw [hvx]; exact hAN hx
    rw [←hvx,←map_mul,←map_mul]
    exact congrArg i ((mem_center_iff.mp (hcentral ⟨hv,hvN⟩)) g)

/-- In the large-slice branch the full midpoint moving cover is contained
in the derived subgroup of its whole two-core. -/
theorem full_point_four_large_slice_moving_le_core_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    U d.radical (p.walk.getVert 2) ≤
      ⁅Q d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let c := p.walk.getVert 2
  let P := localZSpan d.radical c (alpha d.radical)
  let D := ⁅P,P⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hd := full_point_four_large_slice_kernel_derived_knownSimple hb u hfull p hlarge
  have hmov : D = ⁅U d.radical c,P⁆ := hd.2.2.2.2.2.1.symm
  have hPG : P ≤ stabilizer d.radical c :=
    ((localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      (V_le_Q d.radical rfl hb2)).trans
      (Q_le_stabilizer_of_dist_two d.radical _ _ rfl (p.dist_start (by omega)))
  apply moving_le_normal_of_noncentral s hc hcol D _
  · rw [hmov]
    exact le_normalizer_iff_commutator_le_left.mp (hPG.trans (U_normalized c))
  · exact hd.2.2.1
  · intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator]
    have hQ : (Q d.radical c).map (MulAut.conj x).toMonoidHom = Q d.radical c :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical c hx)
    exact congrArg₂ (fun A B : Subgroup (FreeAmalgam d.radical) => ⁅A,B⁆) hQ hQ
  · intro he
    exact hd.2.2.2.2.2.2 (hd.1 ▸ he)

/-- The graph estimate pulls back through the same midpoint coordinates to
the original replacement core, whose derived subgroup has order at least sixteen. -/
theorem full_point_four_large_slice_replacement_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    replacementMoved d ≤ ⁅pCore 2 d.overgroup,pCore 2 d.overgroup⁆ ∧
      16 ≤ Nat.card (⁅pCore 2 d.overgroup,pCore 2 d.overgroup⁆ : Subgroup d.overgroup) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc (p.walk.getVert 2) hcol
  have hle : replacementMoved d ≤ ⁅pCore 2 d.overgroup,pCore 2 d.overgroup⁆ := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [map_commutator,hiQ,hiU]
    exact full_point_four_large_slice_moving_le_core_derived_knownSimple hb u hfull p hlarge
  refine ⟨hle,?_⟩
  have hcard := card_le_of_le hle
  rcases moved_card s with hcardU | hcardU <;> rw [hcardU] at hcard <;> omega

/-- The entire original moved layer lies in the derived subgroup of the
original ambient two-core in this forced configuration. This application
retains the replacement inclusion and the original nonsylow radical. -/
theorem full_point_four_large_slice_initial_moved_le_derived_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    initialMoved L R ≤ ⁅pCore 2 (L ⊔ R : Subgroup G),pCore 2 (L ⊔ R : Subgroup G)⁆ := by
  have hh := map_mono (f := d.overgroup.subtype)
    (full_point_four_large_slice_replacement_derived_knownSimple hb u hfull p hlarge).1
  rw [replacementMoved_map h d,map_commutator] at hh
  have hcore : (pCore 2 d.overgroup).map d.overgroup.subtype ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    rw [replacement_core h d]
    exact map_comap_le _ _
  exact hh.trans (commutator_mono hcore hcore)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
