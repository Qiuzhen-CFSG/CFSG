module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowMovingLine
public import Theory.GroupTheory.IndexTwoConjugateCommutator
public import Theory.GroupTheory.ThreeKernelParity
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Full critical kernels and endpoint orbits in the Sylow branch

Above distance four, the first-edge relative normalizer has at most two
conjugates of the full critical seed kernel. When it moves the critical
line, the two distinct kernels generate the entire starting seed and
intersect in an invariant subgroup of index four. Their full pointwise
centralizers, inside the starting stabilizer, intersect in exactly its
two-core. The transporting element preserves the first-edge kernel; the
proof retains the actual transported vertices instead of identifying them.

The orbit of the endpoint seed stays in the original first-edge kernel.
Its commutator with the full starting seed is exactly the normalizer orbit
of the critical line, and its fixed seed is the intersection of the kernel
conjugates. Thus fixed index two accompanies a fixed commutator line, while
fixed index four accompanies a commutator four-group and a fixed displacement
line of order two. The endpoint seed fixes its critical line; the previously
proved equality of relative centralizers then shows that the entire endpoint
orbit centralizes its own commutator. The three-subgroups lemma places its
derived subgroup in the starting two-core.

The final application identifies the actor with the literal restriction of
the original Sylow subgroup through the graph embedding. All seed kernels,
both moving covers and their full central attachments are retained. These
are estimates for the endpoint orbit; they do not bound the whole edge core
or complete the non-elementary shifts and distance-four exclusions.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the small-kernel and relative-normalizer arguments in (5.5)--(5.8),
printed pp.915--920, and the critical-line comparisons in (5.10)--(5.11),
printed pp.922--924. The index-two intersection and orbit calculations use
the existing general group lemmas with the literal source subgroups.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair

private theorem two_hyperplanes {F : Type*} [Group F]
    (Z K K' : Subgroup F) [Finite Z]
    (hK : K ≤ Z) (hK' : K' ≤ Z)
    (hi : K.relIndex Z = 2) (hi' : K'.relIndex Z = 2) (hne : K ≠ K') :
    K ⊔ K' = Z ∧ (K ⊓ K').relIndex Z = 4 := by
  have hn : ¬ K ≤ K' := by
    intro hk
    have hm := relIndex_mul_relIndex K K' Z hk hK'
    rw [hi,hi'] at hm
    exact hne (le_antisymm hk (relIndex_eq_one.mp (by omega : K.relIndex K' = 1)))
  have hn' : ¬ K' ≤ K := by
    intro hk
    have hm := relIndex_mul_relIndex K' K Z hk hK
    rw [hi,hi'] at hm
    exact hne (le_antisymm (relIndex_eq_one.mp (by omega : K'.relIndex K = 1)) hk)
  have hm := relIndex_mul_relIndex K (K ⊔ K') Z le_sup_left (sup_le hK hK')
  rw [hi] at hm
  have ho : (K ⊔ K').relIndex Z = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hn' (le_sup_right.trans (relIndex_eq_one.mp hh.2))).elim
  refine ⟨le_antisymm (sup_le hK hK') (relIndex_eq_one.mp ho),?_⟩
  have he := index_inf_eq_four_of_distinct_index_two (K.subgroupOf Z) (K'.subgroupOf Z)
    hi hi' (fun hk => hn (by
      intro x hx
      exact hk (show (⟨x,hK hx⟩ : Z) ∈ K.subgroupOf Z from hx)))
  exact he

private theorem kernel_core_pair {F : Type*} [Group F]
    (Z K T : Subgroup F) [Finite Z] [Finite T]
    (hK : K ≤ Z) (hTZ : T ≤ normalizer (Z : Set F))
    (hindex : K.relIndex Z = 2)
    (hbound : (normalizer (K : Set F)).relIndex T ≤ 2)
    (t : F) (ht : t ∈ T) (hnt : t ∉ normalizer (K : Set F)) :
    let K' := K.map (MulAut.conj t).toMonoidHom
    (⨅ s : T, K.map (MulAut.conj (s : F)).toMonoidHom) = K ⊓ K' ∧
      T ≤ normalizer ((K ⊓ K' : Subgroup F) : Set F) ∧
      K ⊔ K' = Z ∧ (K ⊓ K').relIndex Z = 4 := by
  let N := T ⊓ normalizer (K : Set F)
  have hn : N.relIndex T = 2 := by
    rw [inf_relIndex_left]
    have hp : 0 < (normalizer (K : Set F)).relIndex T :=
      Nat.pos_of_ne_zero index_ne_zero_of_finite
    have he : (normalizer (K : Set F)).relIndex T ≠ 1 :=
      fun he => hnt (relIndex_eq_one.mp he ht)
    omega
  have hTN := (le_normalizer_inf_and_commutator_conjugate_of_relIndex_two K N T
    inf_le_left hn inf_le_right t ht (fun hh => hnt hh.2)).trans inf_le_left
  let K' := K.map (MulAut.conj t).toMonoidHom
  have hZ : Z.map (MulAut.conj t).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp (hTZ ht)
  have hK' : K' ≤ Z := (map_mono hK).trans_eq hZ
  have hi' : K'.relIndex Z = 2 := by
    rw [←hZ,relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hindex
  have hne : K ≠ K' := fun hh => hnt (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  obtain ⟨hjoin,hfour⟩ := two_hyperplanes Z K K' hK hK' hindex hi' hne
  refine ⟨?_,hTN,hjoin,hfour⟩
  apply le_antisymm
  · apply le_inf
    · have hh := iInf_le (fun s : T => K.map (MulAut.conj (s : F)).toMonoidHom) 1
      have he : (MulAut.conj (1 : F)).toMonoidHom = MonoidHom.id F := by
        ext x
        simp
      simpa only [Subgroup.coe_one,he,map_id] using hh
    · exact iInf_le (fun s : T => K.map (MulAut.conj (s : F)).toMonoidHom) ⟨t,ht⟩
  · apply le_iInf
    intro s
    have he := mem_normalizer_iff_map_conj_eq.mp (hTN s.property)
    exact he.symm.le.trans (map_mono (show K ⊓ K' ≤ K from inf_le_left))

private theorem orbit_commutator {F : Type*} [Group F]
    (Z A T : Subgroup F) (hAZ : A ≤ normalizer (Z : Set F))
    (hTZ : T ≤ normalizer (Z : Set F)) :
    ⁅Z,componentOrbit A T⁆ = componentOrbit ⁅Z,A⁆ T := by
  let W := componentOrbit ⁅Z,A⁆ T
  have hWZ : W ≤ Z := by
    apply iSup_le
    intro t
    exact (map_mono (le_normalizer_iff_commutator_le_left.mp hAZ)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hTZ t.property))
  have hmap (t : T) :
      ⁅Z,A.map (MulAut.conj (t : F)).toMonoidHom⁆ =
        (⁅Z,A⁆).map (MulAut.conj (t : F)).toMonoidHom := by
    have hz : Z.map (MulAut.conj (t : F)).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp (hTZ t.property)
    rw [map_commutator,hz]
  have hsingle (t : T) : ⁅Z,A.map (MulAut.conj (t : F)).toMonoidHom⁆ ≤ W := by
    rw [hmap]
    exact le_iSup (fun t : T => (⁅Z,A⁆).map (MulAut.conj (t : F)).toMonoidHom) t
  have hEW : componentOrbit A T ≤ normalizer (W : Set F) := by
    apply iSup_le
    intro t
    apply le_normalizer_iff_commutator_le_right.mpr
    rw [commutator_comm]
    exact (commutator_mono hWZ le_rfl).trans (hsingle t)
  apply le_antisymm
  · rw [commutator_comm]
    exact commutator_iSup_le_of_relative_normal (componentOrbit A T) Z W
      (fun t : T => A.map (MulAut.conj (t : F)).toMonoidHom) hEW
      (fun t => le_iSup (fun t : T => A.map (MulAut.conj (t : F)).toMonoidHom) t) (fun t => by rw [commutator_comm]; exact hsingle t)
  · apply iSup_le
    intro t
    rw [←hmap]
    exact commutator_mono le_rfl (le_iSup (fun t : T => A.map (MulAut.conj (t : F)).toMonoidHom) t)

private theorem orbit_fixer {F : Type*} [Group F]
    (Z A T : Subgroup F) (hTZ : T ≤ normalizer (Z : Set F)) :
    Z ⊓ centralizer (componentOrbit A T : Set F) =
      ⨅ t : T, (Z ⊓ centralizer (A : Set F)).map (MulAut.conj (t : F)).toMonoidHom := by
  have hmap (t : T) :
      (Z ⊓ centralizer (A : Set F)).map (MulAut.conj (t : F)).toMonoidHom =
        Z ⊓ centralizer (A.map (MulAut.conj (t : F)).toMonoidHom : Set F) := by
    have hz : Z.map (MulAut.conj (t : F)).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp (hTZ t.property)
    rw [map_inf _ _ _ (MulAut.conj (t : F)).injective,hz]
    congr 1
    apply le_antisymm (map_centralizer_le_centralizer_image _ _)
    intro x hx
    refine ⟨(MulAut.conj (t : F)).symm x,?_,(MulAut.conj (t : F)).apply_symm_apply x⟩
    intro y hy
    apply (MulAut.conj (t : F)).injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using
      hx ((MulAut.conj (t : F)) y) (mem_map_of_mem _ hy)
  apply le_antisymm
  · apply le_iInf
    intro t
    rw [hmap]
    exact inf_le_inf_left Z (centralizer_le (le_iSup (fun t : T => A.map (MulAut.conj (t : F)).toMonoidHom) t))
  · intro x hx
    have hxt (t : T) : x ∈ Z ⊓ centralizer
        (A.map (MulAut.conj (t : F)).toMonoidHom : Set F) := by
      rw [←hmap]
      exact (iInf_le (fun t : T => (Z ⊓ centralizer (A : Set F)).map
        (MulAut.conj (t : F)).toMonoidHom) t) hx
    refine ⟨(hxt 1).1,?_⟩
    have hh : componentOrbit A T ≤ centralizer ({x} : Set F) := by
      apply iSup_le
      intro t y hy z hz
      have hz' : z=x := Set.mem_singleton_iff.mp hz
      subst z
      exact ((hxt t).2 y hy).symm
    intro y hy
    exact (hh hy x (Set.mem_singleton x)).symm

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- A moving critical line gives exactly two full seed kernels, with
whole-seed join and invariant intersection of index four. -/
theorem small_kernel_pair_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (t : FreeAmalgam d.radical)
    (ht : t ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a)
    (hmove : t ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let K := Z d.radical a ⊓ Q d.radical a'
    let K' := K.map (MulAut.conj t).toMonoidHom
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    (⨅ s : T, K.map (MulAut.conj (s : FreeAmalgam d.radical)).toMonoidHom) = K ⊓ K' ∧
      T ≤ normalizer ((K ⊓ K' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      K ⊔ K' = Z d.radical a ∧ (K ⊓ K').relIndex (Z d.radical a) = 4 := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let K := Z d.radical a ⊓ Q d.radical a'
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  let := finite_Z d.radical a
  let := finite_stabilizer d.radical a
  let : Finite T := Finite.of_injective
    (inclusion (show T ≤ stabilizer d.radical a from inf_le_right)) (inclusion_injective _)
  have hnt : t ∉ normalizer (K : Set (FreeAmalgam d.radical)) := by
    intro hh
    have he := small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall
    have hh' : t ∈ stabilizer d.radical a ⊓ normalizer (K : Set (FreeAmalgam d.radical)) :=
      ⟨ht.2,hh⟩
    rw [he] at hh'
    exact hmove hh'.2
  have hi : K.relIndex (Z d.radical a) = 2 := by
    rw [inf_relIndex_left]
    exact (small_critical_indices s hc p hsmall).1
  exact kernel_core_pair (Z d.radical a) K T inf_le_left
    (inf_le_right.trans (Z_normalized d.radical a)) hi
    (SylowSmallNormalizer.small_kernel_relative_index_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall) t ht hnt

include e hz hn in
/-- The endpoint orbit has the literal orbit of the critical line as its
commutator, and its full fixed seed is the intersection of the critical
kernels. The first-edge kernel contains the entire endpoint orbit. -/
theorem small_seed_orbit_identifications_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    E ≤ Q d.radical (p.walk.getVert 1) ∧
      T ≤ normalizer (E : Set (FreeAmalgam d.radical)) ∧
      ⁅Z d.radical a,E⁆ = componentOrbit ⁅Z d.radical a,Z d.radical a'⁆ T ∧
      Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) =
        ⨅ t : T, (Z d.radical a ⊓ Q d.radical a').map
          (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  have hTZ : T ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (Z_normalized d.radical a)
  have hAG : Z d.radical a' ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical
  have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant a' p.end_color,
      SimpleGraph.dist_comm,p.dist_end]
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : Z d.radical a ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Q d.radical a' := by
    apply le_antisymm
    · apply le_inf inf_le_left
      rw [←C_eq_Q s hc a' p.end_color]
      exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)) inf_le_right
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
  refine ⟨?_,le_normalizer_componentOrbit _ _,orbit_commutator _ _ _
    (hAG.trans (Z_normalized d.radical a)) hTZ,?_⟩
  · apply iSup_le
    intro t
    exact (map_mono hAt).trans_eq (mem_normalizer_iff_map_conj_eq.mp t.property.1)
  · rw [orbit_fixer _ _ _ hTZ,hfixed]

include e hz hn in
/-- The whole endpoint orbit either has a fixed kernel of index two and
one commutator line, or a fixed kernel of index four and a commutator
four-group with a fixed displacement line of order two. -/
theorem small_seed_orbit_dichotomy_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    let W := ⁅Z d.radical a,E⁆
    let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
    W ≤ U d.radical a ∧ ⁅⁅W,T⁆,T⁆ = ⊥ ∧
      ((F = Z d.radical a ⊓ Q d.radical a' ∧ F.relIndex (Z d.radical a) = 2 ∧
        W = ⁅Z d.radical a,Z d.radical a'⁆ ∧
        W ≤ centralizer (T : Set (FreeAmalgam d.radical))) ∨
      (F.relIndex (Z d.radical a) = 4 ∧ Nat.card W = 4 ∧
        Nat.card (⁅W,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
        ⁅W,T⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical)))) := by
  classical
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let K := Z d.radical a ⊓ Q d.radical a'
  let E := componentOrbit (Z d.radical a') T
  let W := ⁅Z d.radical a,E⁆
  let F := Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical))
  have hd := small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hw : W = componentOrbit D T := hd.2.2.1
  have hf : F = ⨅ t : T, K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom := hd.2.2.2
  have ho := SylowMovingLine.small_critical_line_orbit_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  change W ≤ U d.radical a ∧ ⁅⁅W,T⁆,T⁆ = ⊥ ∧
    ((F = K ∧ F.relIndex (Z d.radical a) = 2 ∧ W = D ∧
      W ≤ centralizer (T : Set (FreeAmalgam d.radical))) ∨
    (F.relIndex (Z d.radical a) = 4 ∧ Nat.card W = 4 ∧
      Nat.card (⁅W,T⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅W,T⁆ ≤ centralizer (T : Set (FreeAmalgam d.radical))))
  refine ⟨by rw [hw]; exact ho.1,by rw [hw]; exact ho.2.2.2,?_⟩
  by_cases hfix : T ≤ centralizer (D : Set (FreeAmalgam d.radical))
  · apply Or.inl
    have hTK : T ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
      have hh := le_inf (show T ≤ stabilizer d.radical a from inf_le_right) hfix
      rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
      exact hh.trans inf_le_right
    have hFK : F=K := by
      rw [hf]
      have he (t : T) : K.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom = K :=
        mem_normalizer_iff_map_conj_eq.mp (hTK t.property)
      simp only [he,iInf_const]
    have hWD : W=D := by
      rw [hw]
      apply le_antisymm ?_ (le_componentOrbit _ _)
      apply iSup_le
      intro t
      exact (mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.centralizer_le_normalizer _ (hfix t.property))).le
    refine ⟨hFK,?_,hWD,?_⟩
    · rw [hFK,inf_relIndex_left]
      exact (small_critical_indices s hc p hsmall).1
    · rw [hWD]
      exact le_centralizer_iff.mp hfix
  · obtain ⟨t,ht,hnt⟩ := Set.not_subset.mp hfix
    have hp := small_kernel_pair_knownSimple (e := e) (hz := hz) (hn := hn)
      hb p hsmall t ht hnt
    have hfour : F.relIndex (Z d.radical a)=4 := by
      rw [hf,hp.1]
      exact hp.2.2.2
    have hm := SylowMovingLine.small_critical_line_dichotomy_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall
    rcases hm with hm | hm
    · exact (hfix hm).elim
    · exact Or.inr ⟨hfour,by rw [hw]; exact hm.1,by rw [hw]; exact hm.2.1,by rw [hw]; exact hm.2.2⟩


include e hz hn in
/-- A moving normalizer element transports the entire critical path. Its
first-edge kernel is unchanged; the vertices themselves are not identified.
The two full seed centralizers intersect in exactly the starting core. -/
theorem small_moving_kernel_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (t : FreeAmalgam d.radical)
    (ht : t ∈ normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a)
    (hmove : t ∉ centralizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical t⁻¹ a'),
      (∀ i, q.walk.getVert i = act d.radical t⁻¹ (p.walk.getVert i)) ∧
      Q d.radical (q.walk.getVert 1) = Q d.radical (p.walk.getVert 1) ∧
      (Q d.radical (act d.radical t⁻¹ a')).relIndex (Z d.radical a) = 2 ∧
      let K := Z d.radical a ⊓ Q d.radical a'
      let K' := Z d.radical a ⊓ Q d.radical (act d.radical t⁻¹ a')
      let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical a
      K ⊔ K' = Z d.radical a ∧ (K ⊓ K').relIndex (Z d.radical a) = 4 ∧
        T ≤ normalizer ((K ⊓ K' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
        (Q d.radical a ⊔ Z d.radical a') ⊓
          (Q d.radical a ⊔ Z d.radical (act d.radical t⁻¹ a')) = Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hta : act d.radical t⁻¹ a = a := (stabilizer d.radical a).inv_mem ht.2
  have hex : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical t⁻¹ a) (act d.radical t⁻¹ a'),
      ∀ i, q.walk.getVert i = act d.radical t⁻¹ (p.walk.getVert i) :=
    ⟨p.act t⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hta] at hex
  obtain ⟨q,hq⟩ := hex
  have hqs : (Q d.radical (act d.radical t⁻¹ a')).relIndex (Z d.radical a) < 4 := by
    conv_lhs => rhs; rw [←hta]
    rw [Q_act,Z_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hsmall
  have hkm : (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj t).toMonoidHom =
      Z d.radical a ⊓ Q d.radical (act d.radical t⁻¹ a') := by
    have hzmap : (Z d.radical a).map (MulAut.conj t).toMonoidHom = Z d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a ht.2)
    rw [map_inf _ _ _ (MulAut.conj t).injective,hzmap,Q_act,inv_inv]
  have hp := small_kernel_pair_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p hsmall t ht hmove
  dsimp only at hp
  rw [hkm] at hp
  refine ⟨q,hq,?_,(small_critical_indices s hc q hqs).1,hp.2.2.1,hp.2.2.2,hp.2.1,?_⟩
  · rw [hq,Q_act,inv_inv]
    exact mem_normalizer_iff_map_conj_eq.mp ht.1
  · let K := Z d.radical a ⊓ Q d.radical a'
    let K' := Z d.radical a ⊓ Q d.radical (act d.radical t⁻¹ a')
    have hjoin : K ⊔ K' = Z d.radical a := hp.2.2.1
    have hC : centralizer (K : Set (FreeAmalgam d.radical)) ⊓
        centralizer (K' : Set (FreeAmalgam d.radical)) =
        centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
      apply le_antisymm
      · apply le_centralizer_iff.mpr
        rw [←hjoin]
        exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
      · exact le_inf (centralizer_le (show K ≤ Z d.radical a from inf_le_left))
          (centralizer_le (show K' ≤ Z d.radical a from inf_le_left))
    rw [←small_critical_kernel_centralizer_eq s hc p hsmall,
      ←small_critical_kernel_centralizer_eq s hc q hqs]
    have he : (stabilizer d.radical a ⊓ centralizer (K : Set (FreeAmalgam d.radical))) ⊓
        (stabilizer d.radical a ⊓ centralizer (K' : Set (FreeAmalgam d.radical))) =
        stabilizer d.radical a ⊓ (centralizer (K : Set (FreeAmalgam d.radical)) ⊓
          centralizer (K' : Set (FreeAmalgam d.radical))) := by
      ext x
      simp only [mem_inf]
      tauto
    change (stabilizer d.radical a ⊓ centralizer (K : Set (FreeAmalgam d.radical))) ⊓
      (stabilizer d.radical a ⊓ centralizer (K' : Set (FreeAmalgam d.radical))) = Q d.radical a
    rw [he,hC]
    exact C_eq_Q s hc a p.start_color

include e hz hn in
/-- The entire endpoint orbit acts quadratically on the full starting seed.
Its derived subgroup lies in the actual starting core. This controls the
orbit actor, without asserting a bound on the whole first-edge core. -/
theorem small_seed_orbit_quadratic_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    ⁅⁅Z d.radical a,E⁆,E⁆ = ⊥ ∧ ⁅E,E⁆ ≤ Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  let A := Z d.radical a'
  let D := ⁅Z d.radical a,A⁆
  let W := componentOrbit D T
  let E := componentOrbit A T
  have hi := small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hEW : ⁅Z d.radical a,E⁆ = W := hi.2.2.1
  have ho := SylowMovingLine.small_critical_line_orbit_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hEq : E ≤ Q d.radical (p.walk.getVert 1) := hi.1
  have hAG : A ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical
  have hAT : A ≤ T := le_inf
    (((le_componentOrbit A T).trans hEq).trans (Q d.radical (p.walk.getVert 1)).le_normalizer) hAG
  have hDA : D ≤ A := ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
    (DistanceEight.U_le_Z d.radical a')
  let : IsElementaryAbelian 2 A :=
    (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  have hAD : A ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    intro x hx y hy
    exact setLike_mul_comm (hDA hy) hx
  have hAW : A ≤ centralizer (W : Set (FreeAmalgam d.radical)) := by
    have hh : A ≤ T ⊓ centralizer (D : Set (FreeAmalgam d.radical)) := le_inf hAT hAD
    rw [ho.2.2.1] at hh
    exact hh.trans inf_le_right
  have hEWfix : E ≤ centralizer (W : Set (FreeAmalgam d.radical)) := by
    apply iSup_le
    intro t
    have hm : W.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_componentOrbit D T) t.property)
    have hh := (map_mono (f := (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom) hAW).trans
      (map_centralizer_le_centralizer_image _ _)
    change A.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom ≤
      centralizer (W.map (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom : Set _) at hh
    rwa [hm] at hh
  have hquad : ⁅⁅Z d.radical a,E⁆,E⁆=⊥ := by
    rw [hEW,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hEWfix
  refine ⟨hquad,?_⟩
  have hEZ : ⁅⁅E,E⁆,Z d.radical a⁆=⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (by rw [commutator_comm E]; exact hquad) hquad
  have hEG : E ≤ stabilizer d.radical a := by
    apply iSup_le
    intro t
    have hm : (stabilizer d.radical a).map
        (MulAut.conj (t : FreeAmalgam d.radical)).toMonoidHom = stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer t.property.2)
    exact (map_mono hAG).trans_eq hm
  rw [←C_eq_Q s hc a p.start_color]
  exact le_inf ((Subgroup.commutator_le_sup E E).trans (sup_le hEG hEG))
    (commutator_eq_bot_iff_le_centralizer.mp hEZ)

include e hz hn in
/-- Literal restricted-original-Sylow application. The whole endpoint orbit
has fixed index and displacement order at most four on the full starting
seed, and the normalizer's action on that displacement is quadratic. -/
theorem small_base_seed_orbit_bounds_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let E := componentOrbit (Z d.radical a') T
    let W := ⁅Z d.radical (alpha d.radical),E⁆
    E ≤ Q d.radical (beta d.radical) ∧
      (centralizer (E : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical (alpha d.radical)) ≤ 4 ∧
      Nat.card W ≤ 4 ∧ ⁅⁅W,T⁆,T⁆ = ⊥ ∧ ⁅W,E⁆ = ⊥ ∧
      ⁅E,E⁆ ≤ Q d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hd := small_seed_orbit_dichotomy_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  have hquad := small_seed_orbit_quadratic_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall
  dsimp only at hi hd hquad ⊢
  rw [hfirst,SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb] at hi hd hquad
  refine ⟨hi.1,?_,?_,hd.2.1,hquad.1,hquad.2⟩
  · rcases hd.2.2 with hh | hh
    · have hn := hh.2.1
      rw [inf_relIndex_left] at hn
      omega
    · have hn := hh.1
      rw [inf_relIndex_left] at hn
      omega
  · rcases hd.2.2 with hh | hh
    · rw [hh.2.2.1,small_critical_commutator_card s hc p hsmall]
      decide
    · exact hh.2.1.le


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
