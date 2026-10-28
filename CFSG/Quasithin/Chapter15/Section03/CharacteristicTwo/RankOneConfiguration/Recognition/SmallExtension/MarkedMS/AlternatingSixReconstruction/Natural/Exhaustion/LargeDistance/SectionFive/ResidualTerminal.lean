module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ForcedDerived


/-!
# The residual-core obstruction without an endpoint estimate

At distance four with the literal full point-core image, the selected common
kernel Y has the same derived line as the nonabelian selected span P. That
transfer is already proved independently of the endpoint commutator estimate.
We apply it directly to the opposite residual core C = [Q,Ltilde].

If Y', C' and [Y,C] all have order at most two, the incident edge radical
centralizes all three. The normal subgroup N = Y C has derived subgroup
inside their product, of order at most eight. The actual symmetric-six
quotient then makes the two-residual centralize N', hence Y'. The incident
edge and the two-residual generate the midpoint stabilizer, contradicting
the proved noncentrality of Y' there. Thus a numerical cross-commutator bound
suffices; containment of [Y,C] in C' is unnecessary for this argument.

The original-graph large-slice construction supplies one such Y without any
path, slice or nonabelianness premise. The literal minimum-replacement
application consequently has distance two or an actual critical path with
|C'| > 2 or |[Y,C]| > 2. Both central covers and the original nonsylow radical
are retained. Bounding those two residual commutators, and excluding the
other radical-image branches, remain obligations of the large-distance owner.
This does not establish the unconditional distance-two theorem.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and the terminal commutator argument of (5.12), printed
pp.879--881 and 926--927. The three-line argument extends the existing
SelectedSpan two-line calculation and uses the actual quotient and edge maps.
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

include h in
private theorem residual_component_radical_sup : replacementComponent d ⊔ d.radical = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
  exact mul_mem (mem_sup_left hk) (mem_sup_right hr)


include h in
private theorem residual_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hsup : replacementComponent d ⊔ d.radical = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d g
    exact mul_mem (mem_sup_left hk) (mem_sup_right hr)
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d,Q_beta,←Subgroup.map_sup,hsup]
    exact (MonoidHom.range_eq_map (embedM d.radical)).symm.trans (stabilizer_m_base d.radical).symm
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
    rw [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act] at he
    simpa only [alpha,beta,act_mVertex,act_hVertex,one_mul] using he
  · rw [hg.1] at ha
    cases ha


private theorem residual_small_centralized
    {M : Type*} [Group M] [Finite M] (A B : Subgroup M)
    (hn : A ≤ normalizer (B : Set M)) (hc : Nat.card B ≤ 2) :
    A ≤ centralizer (B : Set M) := by
  have hp := Nat.card_pos (α := B)
  have hh : Nat.card B = 1 ∨ Nat.card B = 2 := by omega
  rcases hh with hh | hh
  · rw [card_eq_one.mp hh]
    intro a _ b hb
    have hb1 : b = 1 := mem_bot.mp hb
    simp only [hb1,mul_one,one_mul]
  · exact hn.trans (normalizer_le_centralizer_of_card_two B hh)


include h in
private theorem residual_edge_coordinates {c t : Vertex d.radical}
    (hc : color d.radical c=false) (hct : Adjacent d.radical c t) :
    ∃ i : d.overgroup→*FreeAmalgam d.radical, Function.Injective i ∧
      d.radical.map i=Q d.radical t ∧ (pCore 2 d.overgroup).map i=Q d.radical c ∧ (replacementComponent d).map i=Ltilde d.radical c := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_⟩
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
    · have he := Q_act d.radical g (alpha d.radical)
      rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · have he := Ltilde_act d.radical g (alpha d.radical)
      rw [Ltilde_alpha,replacement_residual h d] at he
      simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at hc
    cases hc


private theorem residual_card_sup_le {F : Type*} [Group F] [Finite F]
    (A B : Subgroup F) (hn : B ≤ normalizer (A : Set F)) :
    Nat.card (A ⊔ B : Subgroup F) ≤ Nat.card A * Nat.card B := by
  have hprod : (A : Set F) * (B : Set F) = (A ⊔ B : Subgroup F) :=
    (coe_mul_of_right_le_normalizer_left _ _ hn).symm
  let f : A × B → (A ⊔ B : Subgroup F) :=
    fun x => ⟨x.1*x.2,mul_mem (mem_sup_left x.1.property) (mem_sup_right x.2.property)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    have hx' : x ∈ (A : Set F) * (B : Set F) := hprod.symm ▸ hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hx'
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩),rfl⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

include s in
private theorem residual_three_small_commutators
    (D : Subgroup d.overgroup) (hDQ : D ≤ pCore 2 d.overgroup)
    (hDN : d.radical ≤ normalizer (D : Set d.overgroup))
    (hDcard : Nat.card (⁅D,D⁆ : Subgroup d.overgroup) ≤ 2)
    (hCcard : Nat.card (⁅⁅pCore 2 d.overgroup,replacementComponent d⁆,
      ⁅pCore 2 d.overgroup,replacementComponent d⁆⁆ : Subgroup d.overgroup) ≤ 2)
    (hcross : Nat.card (⁅D,⁅pCore 2 d.overgroup,replacementComponent d⁆⁆ :
      Subgroup d.overgroup) ≤ 2) :
    ⁅D,D⁆ ≤ centralizer (replacementComponent d : Set d.overgroup) := by
  let := replacementComponent_normal h d
  let C := ⁅pCore 2 d.overgroup,replacementComponent d⁆
  let A := ⁅D,D⁆
  let B := ⁅C,C⁆
  let X := ⁅D,C⁆
  have hCQ : C ≤ pCore 2 d.overgroup := commutator_le_left _ _
  have hDR : D ≤ d.radical := hDQ.trans (replacement_core_le_radical h d)
  have hCR : C ≤ d.radical := hCQ.trans (replacement_core_le_radical h d)
  have hAn : d.radical ≤ normalizer (A : Set d.overgroup) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hDN hg)]
  have hXn : d.radical ≤ normalizer (X : Set d.overgroup) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hDN hg),
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (C : Set d.overgroup) from
        le_normalizer_of_normal (mem_top g))]
  have hAC : A ≤ centralizer (d.radical : Set d.overgroup) :=
    le_centralizer_iff.mp (residual_small_centralized _ _ hAn hDcard)
  have hBC : B ≤ centralizer (d.radical : Set d.overgroup) :=
    le_centralizer_iff.mp (residual_small_centralized _ _ le_normalizer_of_normal hCcard)
  have hXC : X ≤ centralizer (d.radical : Set d.overgroup) :=
    le_centralizer_iff.mp (residual_small_centralized _ _ hXn hcross)
  have hAR : A ≤ d.radical := (Subgroup.commutator_le_sup D D).trans (sup_le hDR hDR)
  have hBR : B ≤ d.radical := (commutator_le_left C C).trans hCR
  have hXR : X ≤ d.radical := (commutator_le_right D C).trans hCR
  let H := (A ⊔ B) ⊔ X
  let N := D ⊔ C
  have hHC : H ≤ centralizer (d.radical : Set d.overgroup) := sup_le (sup_le hAC hBC) hXC
  have hHN : d.radical ≤ normalizer (H : Set d.overgroup) :=
    (le_centralizer_iff.mp hHC).trans (Subgroup.centralizer_le_normalizer _)
  have hNN : (⊤ : Subgroup d.overgroup) ≤ normalizer (N : Set d.overgroup) := by
    rw [←residual_component_radical_sup (h := h)]
    apply sup_le
    · apply le_normalizer_iff_commutator_le_right.mpr
      rw [commutator_comm]
      exact (commutator_mono (sup_le hDQ hCQ) le_rfl).trans le_sup_right
    · exact (le_inf hDN (le_normalizer_of_normal (H := C))).trans
        (normalizer_inf_normalizer_le_normalizer_sup D C)
  let : N.Normal := ⟨by
    intro n hn g
    exact (le_normalizer_iff.mp hNN g (mem_top _)) n hn⟩
  have hNC : ⁅N,N⁆ ≤ H := by
    apply commutator_sup_le_of_relative_normal d.radical D C N H hHN hDR hCR
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal d.radical D C D H hHN hDR hCR
      · exact le_sup_left.trans le_sup_left
      · rw [commutator_comm]; exact le_sup_right
    · rw [commutator_comm]
      apply commutator_sup_le_of_relative_normal d.radical D C C H hHN hDR hCR
      · exact le_sup_right
      · exact le_sup_right.trans le_sup_left
  have hAB : Nat.card (A ⊔ B : Subgroup d.overgroup) ≤ 4 :=
    (residual_card_sup_le A B (hBR.trans
      ((le_centralizer_iff.mp hAC).trans (Subgroup.centralizer_le_normalizer _)))).trans
        (Nat.mul_le_mul hDcard hCcard)
  have hcardH : Nat.card H ≤ 8 :=
    (residual_card_sup_le (A ⊔ B) X (hXR.trans
      ((le_centralizer_iff.mp (sup_le hAC hBC)).trans (Subgroup.centralizer_le_normalizer _)))).trans
        (Nat.mul_le_mul hAB hcross)
  have hNQ : ⁅N,N⁆ ≤ pCore 2 d.overgroup :=
    (show ⁅N,N⁆ ≤ N from commutator_le_left _ _).trans (sup_le hDQ hCQ)
  have hcard : (⊥ : Subgroup d.overgroup).relIndex ⁅N,N⁆ ≤ 8 := by
    rw [relIndex_bot_left]
    exact (card_le_of_le hNC).trans hcardH
  have hker : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hh := commutator_pResidual_le_of_symmetricSix_small_section s.projection
    s.surjective hker ⁅N,N⁆ ⊥ (hNQ.trans_eq s.projection_kernel.symm) hcard
  rw [replacement_residual h d] at hh
  exact commutator_eq_bot_iff_le_centralizer.mp
    (le_bot_iff.mp ((commutator_mono (commutator_mono le_sup_left le_sup_left) le_rfl).trans hh))

include s in
private theorem residual_three_small_commutators_at
    {c t : Vertex d.radical} (hc : color d.radical c = false) (hct : Adjacent d.radical c t)
    (D : Subgroup (FreeAmalgam d.radical)) (hDQ : D ≤ Q d.radical c)
    (hDN : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)))
    (hDcard : Nat.card (⁅D,D⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hCcard : Nat.card (⁅⁅Q d.radical c,Ltilde d.radical c⁆,
      ⁅Q d.radical c,Ltilde d.radical c⁆⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2)
    (hcross : Nat.card (⁅D,⁅Q d.radical c,Ltilde d.radical c⁆⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ 2) :
    ⁅D,D⁆ ≤ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
  obtain ⟨i,hi,hiR,hiQ,hiL⟩ := residual_edge_coordinates (h := h) hc hct
  let D₀ := D.comap i
  let C₀ := ⁅pCore 2 d.overgroup,replacementComponent d⁆
  have hDm : D₀.map i = D := map_comap_eq_self (hDQ.trans (hiQ ▸ map_le_range i _))
  have hCm : C₀.map i = ⁅Q d.radical c,Ltilde d.radical c⁆ := by rw [map_commutator,hiQ,hiL]
  have hDDm : (⁅D₀,D₀⁆ : Subgroup d.overgroup).map i = ⁅D,D⁆ := by rw [map_commutator,hDm]
  have hCCm : (⁅C₀,C₀⁆ : Subgroup d.overgroup).map i =
      ⁅⁅Q d.radical c,Ltilde d.radical c⁆,⁅Q d.radical c,Ltilde d.radical c⁆⁆ := by
    rw [map_commutator,hCm]
  have hD₀Q : D₀ ≤ pCore 2 d.overgroup := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hDm,hiQ]
  have hD₀N : d.radical ≤ normalizer (D₀ : Set d.overgroup) :=
    ((map_le_iff_le_comap).mp (hiR ▸ hDN)).trans (le_normalizer_comap i)
  have hD₀card : Nat.card (⁅D₀,D₀⁆ : Subgroup d.overgroup) ≤ 2 := by
    rwa [←hDDm,card_map_of_injective hi] at hDcard
  have hC₀card : Nat.card (⁅C₀,C₀⁆ : Subgroup d.overgroup) ≤ 2 := by
    rwa [←hCCm,card_map_of_injective hi] at hCcard
  have hcross₀ : Nat.card (⁅D₀,C₀⁆ : Subgroup d.overgroup) ≤ 2 := by
    rw [←card_map_of_injective hi,map_commutator,hDm,hCm]
    exact hcross
  have hh := residual_three_small_commutators s D₀ hD₀Q hD₀N hD₀card hC₀card hcross₀
  have hm := (map_mono (f := i) hh).trans (map_centralizer_le_centralizer_image _ _)
  change (⁅D₀,D₀⁆ : Subgroup d.overgroup).map i ≤
    centralizer ((replacementComponent d).map i : Set (FreeAmalgam d.radical)) at hm
  rwa [hDDm,hiL] at hm

/-- The selected common kernel forces either the opposite residual derived
subgroup or its cross commutator to have order greater than two. The
endpoint commutator estimate is not required. -/
theorem full_point_four_large_slice_residual_obstruction_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) :
    let C := ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆
    let Y := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert 2)
    2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) ∨
      2 < Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam d.radical)) := by
  dsimp only
  by_contra! hsmall
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan d.radical c (alpha d.radical)
  let Y := P ⊓ Q d.radical c
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcol : color d.radical c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical (alpha d.radical) t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hQc : Q d.radical t ≤ stabilizer d.radical c :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hYN : Q d.radical t ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQa.trans (localZSpan_normalized d.radical _ _))
      (hQc.trans (Q_normalized d.radical c))).trans inf_normalizer_le_normalizer_inf
  have hd := full_point_four_large_slice_kernel_derived_knownSimple hb u hfull p hlarge
  have hfixed := residual_three_small_commutators_at s hcol hct Y inf_le_right hYN
    hd.2.1.le hsmall.1 hsmall.2
  have hbase : ⁅Y,Y⁆ ≤ centralizer
      (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    hd.1 ▸ hd.2.2.2.1
  apply hd.2.2.2.2.2.2
  apply le_centralizer_iff.mpr
  rw [←residual_edge_generation (h := h) hcol hct]
  exact sup_le (le_centralizer_iff.mp hfixed)
    (hQa.trans (le_centralizer_iff.mp hbase))

/-- At full-point distance four, one actual critical path already witnesses
the residual obstruction. No endpoint, nonabelianness or slice premise
is supplied by a caller. -/
theorem full_point_four_exists_residual_obstruction_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a', ∃ p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a',
      let C := ⁅Q d.radical (p.walk.getVert 2),Ltilde d.radical (p.walk.getVert 2)⁆
      let Y := localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊓
        Q d.radical (p.walk.getVert 2)
      2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam d.radical)) ∨
        2 < Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam d.radical)) := by
  obtain ⟨a',p,hlarge⟩ := full_point_four_exists_large_slice_knownSimple hb u hfull
  exact ⟨a',p,full_point_four_large_slice_residual_obstruction_knownSimple hb u hfull p hlarge⟩

/-- Application to the literal minimum replacement. The unresolved
full-point alternative now requires only two numerical residual-core
bounds on its constructed path, without endpoint or natural-quotient input. -/
theorem original_full_point_distance_two_or_residual_obstruction_knownSimple
    (u : Equiv.Perm (Fin 6))
    (hfull : (replacement h).radical.map
      (SourceReduction.projection h e hz hn (replacement h)) =
        pointCore.map (MulAut.conj u).toMonoidHom) :
    replacementDistance h (replacement h) = 2 ∨
      ∃ a', ∃ p : CriticalPath (replacement h).radical (replacementGeometry h (replacement h))
          (alpha (replacement h).radical) a',
        let C := ⁅Q (replacement h).radical (p.walk.getVert 2),
          Ltilde (replacement h).radical (p.walk.getVert 2)⁆
        let Y := localZSpan (replacement h).radical (p.walk.getVert 2)
          (alpha (replacement h).radical) ⊓ Q (replacement h).radical (p.walk.getVert 2)
        2 < Nat.card (⁅C,C⁆ : Subgroup (FreeAmalgam (replacement h).radical)) ∨
          2 < Nat.card (⁅Y,C⁆ : Subgroup (FreeAmalgam (replacement h).radical)) := by
  rcases full_point_distance_two_or_four_knownSimple u hfull with hb | hb
  · exact Or.inl hb
  · exact Or.inr (full_point_four_exists_residual_obstruction_knownSimple hb u hfull)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
