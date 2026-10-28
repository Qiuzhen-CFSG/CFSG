module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallKernel
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalMovedSpace
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.Representation.GeneratedSubgroupInvariants
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Critical lines determine the full endpoint kernels

In the small critical-image branch, the natural quotient's invariant
symplectic pairing recovers the fixed hyperplane from the moved line.
The pointwise fixer of that hyperplane determines the entire actor image.
Pulling back through the original marking and graph embedding proves that
two critical paths with a common starting vertex and the same commutator
line have the same full endpoint kernel.

Consequently the kernel normalizer and line centralizer coincide inside
the starting stabilizer. A single conjugator transports the line, kernel,
and every vertex of the actual critical path. The original replacement
applications supply the full symmetric action, central layer and small
critical index from the proved opposite-radius estimate. Both moved-cover
orders remain possible; the central kernel is never split off.

Source: MS93 (5.11), first paragraph, printed p.923, using (3.3)(ii),
pp.866--867. The selected shifted paths, strict radius indices, intermediate
R4/R6 noncentrality, and (5.12) terminal estimates remain obligations of
qt-e-ms-small-a6-exhaustion-large-distance. Final unconditional
reconstruction remains with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem small_images_eq_of_moved_eq
    (A B : Subgroup (Equiv.Perm (Fin 6))) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1)
    (hmoved : subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ A =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ B) : A = B := by
  open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing in
  have hfixed : fixedSpace (naturalRepresentation (Fin 6)) A =
      fixedSpace (naturalRepresentation (Fin 6)) B := by
    rw [moved_eq_fixed_orthogonal,moved_eq_fixed_orthogonal] at hmoved
    have he := congrArg (fun I => form.orthogonal I) hmoved
    simpa only [LinearMap.BilinForm.orthogonal_orthogonal form_nondegenerate form_alt.isRefl] using he
  have hsup : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ B) =
      fixedSpace (naturalRepresentation (Fin 6)) A := by
    have hh : fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ B) =
        fixedSpace (naturalRepresentation (Fin 6)) A ⊓ fixedSpace (naturalRepresentation (Fin 6)) B :=
      (naturalRepresentation (Fin 6)).invariants_comp_sup A B
    rw [hh,hfixed,inf_idem]
  have hsupsmall : fixedCodim (naturalRepresentation (Fin 6)) (A ⊔ B) ≤ 1 := by
    change Module.finrank (ZMod 2) ((natural (Fin 6)) ⧸
      fixedSpace (naturalRepresentation (Fin 6)) (A ⊔ B)) ≤ 1
    rw [hsup]
    exact hsmall
  have hsupne : A ⊔ B ≠ ⊥ := fun he => hA (le_bot_iff.mp (he ▸ le_sup_left))
  obtain ⟨t,_,ht,he⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
      (A ⊔ B) hsupne hsupsmall
  have hc : Nat.card (A ⊔ B : Subgroup (Equiv.Perm (Fin 6))) = 2 := by rw [he,Nat.card_zpowers,ht.orderOf]
  have hAc := (one_lt_card_iff_ne_bot A).mpr hA
  have hBc := (one_lt_card_iff_ne_bot B).mpr hB
  exact (eq_of_le_of_card_ge (show A ≤ A ⊔ B from le_sup_left) (by omega)).trans
    (eq_of_le_of_card_ge (show B ≤ A ⊔ B from le_sup_right) (by omega)).symm

include s in
/-- Equal commutators on the full cover determine equal small actor images.
The argument uses its surjective natural quotient, preserving the central kernel. -/
theorem cover_small_images_eq_of_commutator_eq (A B : Subgroup d.overgroup)
    (hA : ¬ A ≤ pCore 2 d.overgroup) (hB : ¬ B ≤ pCore 2 d.overgroup)
    (hsmall : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hcomm : ⁅replacementMoved d,A⁆ = ⁅replacementMoved d,B⁆) :
    A.map s.projection = B.map s.projection := by
  let := replacementMoved_normal h d
  have hne (X : Subgroup d.overgroup) (hX : ¬ X ≤ pCore 2 d.overgroup) :
      X.map s.projection ≠ ⊥ := by
    intro he
    exact hX (s.projection_kernel ▸ (map_eq_bot_iff X).mp he)
  have hsmall' : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hsmall
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hsmall
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall'
  have he : subspaceCommutator (coverAction s) ⊤ (A.map s.projection) =
      subspaceCommutator (coverAction s) ⊤ (B.map s.projection) := by
    have hm (X : Subgroup d.overgroup) :
        NormalElementaryQuotient.commutatorSpace (replacementMoved d) X =
          subspaceCommutator (coverAction s) ⊤ (X.map s.projection) :=
      NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection s.surjective
        (s.projection_kernel.trans (moved_centralizer s).symm) X
    rw [←hm A,←hm B]
    unfold NormalElementaryQuotient.commutatorSpace
    rw [hcomm]
  have hm (X : Subgroup d.overgroup) :
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (X.map s.projection) =
        (subspaceCommutator (coverAction s) ⊤ (X.map s.projection)).map
          (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)) := by
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id _) (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (fun g v => (coverMap_equivariant s g v).symm) (X.map s.projection) ⊤
    simpa only [Submodule.map_top,LinearMap.range_eq_top.mpr
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d)),map_id] using hh
  exact small_images_eq_of_moved_eq _ _ (hne A hA) (hne B hB) hnat (by rw [hm A,hm B,he])


include s in
/-- At a common critical starting vertex, equality of the actual small lines
forces equality of the complete opposite seed images modulo the two-core. -/
theorem small_critical_equal_lines_image (hc : DistanceTwo.CentralLayer d)
    {a a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4)
    (hline : ⁅Z d.radical a,Z d.radical a'⁆ = ⁅Z d.radical a,Z d.radical b'⁆) :
    Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical b' := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hA : Z d.radical a' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical
  have hB : Z d.radical b' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color
      (by rw [(replacementGeometry h d).distance_constant a q.start_color]
          exact replacementDistance_pos h d) q.critical
  let A := (Z d.radical a').comap i
  let B := (Z d.radical b').comap i
  have hmA : A.map i = Z d.radical a' := map_comap_eq_self hA
  have hmB : B.map i = Z d.radical b' := map_comap_eq_self hB
  have hneA : ¬ A ≤ pCore 2 d.overgroup := by
    intro he
    have hh := map_mono (f := i) he
    rw [hmA,hiQ] at hh
    exact (critical_reverse_pair s hc p).2 hh
  have hneB : ¬ B ≤ pCore 2 d.overgroup := by
    intro he
    have hh := map_mono (f := i) he
    rw [hmB,hiQ] at hh
    exact (critical_reverse_pair s hc q).2 hh
  have hcomm : ⁅replacementMoved d,A⁆ = ⁅replacementMoved d,B⁆ := by
    apply map_injective hi
    rw [map_commutator,map_commutator,hiU,hmA,hmB,
      small_critical_moving_commutator_eq s hc p hp,
      small_critical_moving_commutator_eq s hc q hq]
    exact hline
  have hC : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hidx : (centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ 2 :=
    ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a)
        index_ne_zero_of_finite)).trans_eq (small_critical_indices s hc p hp).1
  have hidx' : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hidx
    exact hidx
  have him := cover_small_images_eq_of_commutator_eq s A B hneA hneB hidx' hcomm
  have hj := congrArg (Subgroup.comap s.projection) him
  rw [comap_map_eq,comap_map_eq,s.projection_kernel] at hj
  have hj' := congrArg (Subgroup.map i) hj
  rw [Subgroup.map_sup,Subgroup.map_sup,hmA,hmB,hiQ] at hj'
  exact (sup_comm _ _).trans (hj'.trans (sup_comm _ _))

include s in
/-- The full endpoint kernel is recovered from the small critical line.
This is the reverse implication needed in the first paragraph of (5.11). -/
theorem small_critical_equal_lines_kernels (hc : DistanceTwo.CentralLayer d)
    {a a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4)
    (hline : ⁅Z d.radical a,Z d.radical a'⁆ = ⁅Z d.radical a,Z d.radical b'⁆) :
    Z d.radical a ⊓ Q d.radical a' = Z d.radical a ⊓ Q d.radical b' := by
  have hj := small_critical_equal_lines_image s hc p q hp hq hline
  have hQ : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  have step {c f : Vertex d.radical}
      (pc : CriticalPath d.radical (replacementGeometry h d) a c)
      (pf : CriticalPath d.radical (replacementGeometry h d) a f)
      (he : Q d.radical a ⊔ Z d.radical c = Q d.radical a ⊔ Z d.radical f) :
      Z d.radical a ⊓ Q d.radical c ≤ Z d.radical a ⊓ Q d.radical f := by
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [←C_eq_Q s hc f pf.end_color]
    refine ⟨Z_le_stabilizer_of_dist_le a _ pf.critical.1.le hx.1,?_⟩
    have hfix : Q d.radical a ⊔ Z d.radical c ≤
        centralizer ({x} : Set (FreeAmalgam d.radical)) := by
      apply sup_le
      · intro y hy z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hQ hy x hx.1
      · intro y hy z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical c pc.end_color) hy) x hx.2
    intro z hz
    have hz' := hfix (he.symm ▸ (show z ∈ Q d.radical a ⊔ Z d.radical f from mem_sup_right hz))
    exact (hz' x (Set.mem_singleton _)).symm
  exact le_antisymm (step p q hj) (step q p hj.symm)

include s in
/-- Kernel and line equality are equivalent for two small critical paths
with the same starting vertex and the literal original endpoint groups. -/
theorem small_critical_kernel_eq_iff_line_eq (hc : DistanceTwo.CentralLayer d)
    {a a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4) :
    Z d.radical a ⊓ Q d.radical a' = Z d.radical a ⊓ Q d.radical b' ↔
      ⁅Z d.radical a,Z d.radical a'⁆ = ⁅Z d.radical a,Z d.radical b'⁆ :=
  ⟨fun hk => (small_critical_equal_kernels s hc p q hp hq hk).2,
    small_critical_equal_lines_kernels s hc p q hp hq⟩


include s in
/-- The source conjugator preserves the full endpoint kernel exactly when
it preserves the critical line. The starting vertex and conjugator are shared. -/
theorem small_critical_conjugate_kernel_iff (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a) :
    Z d.radical a ⊓ Q d.radical (act d.radical g a') = Z d.radical a ⊓ Q d.radical a' ↔
      (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)).map
        (MulAut.conj g⁻¹).toMonoidHom = ⁅Z d.radical a,Z d.radical a'⁆ := by
  have hga : act d.radical g a = a := hg
  have q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g a') := by
    simpa only [hga] using p.act g
  have hq : (Q d.radical (act d.radical g a')).relIndex (Z d.radical a) < 4 := by
    rw [←hga,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hp
  have hmap : (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)).map
      (MulAut.conj g⁻¹).toMonoidHom = ⁅Z d.radical a,Z d.radical (act d.radical g a')⁆ := by
    rw [map_commutator,←Z_act,←Z_act,hga]
  rw [hmap]
  exact small_critical_kernel_eq_iff_line_eq s hc q p hq hp

include s in
/-- Inside the starting stabilizer, the full kernel and critical line have
the same setwise stabilizer, including on the order-thirty-two cover. -/
theorem small_critical_kernel_normalizer_eq_line_normalizer (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    stabilizer d.radical a ⊓ normalizer
      ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) =
    stabilizer d.radical a ⊓ normalizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  ext g
  constructor <;> rintro ⟨hg,hn⟩ <;> refine ⟨hg,?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    have he := (small_critical_conjugate_kernel_iff s hc p hp g⁻¹
      ((stabilizer d.radical a).inv_mem hg)).mp
    simp only [inv_inv] at he
    apply he
    have hmap := mem_normalizer_iff_map_conj_eq.mp hn
    change (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj g).toMonoidHom =
      Z d.radical a ⊓ Q d.radical a' at hmap
    have hga : act d.radical g⁻¹ a = a := (stabilizer d.radical a).inv_mem hg
    have hmZ := Z_act d.radical g⁻¹ a
    have hmQ := Q_act d.radical g⁻¹ a'
    simp only [inv_inv,hga] at hmZ hmQ
    rwa [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,←hmZ,←hmQ] at hmap
  · apply mem_normalizer_iff_map_conj_eq.mpr
    have he := (small_critical_conjugate_kernel_iff s hc p hp g⁻¹
      ((stabilizer d.radical a).inv_mem hg)).mpr
    simp only [inv_inv] at he
    have he' := he (mem_normalizer_iff_map_conj_eq.mp hn)
    change (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj g).toMonoidHom =
      Z d.radical a ⊓ Q d.radical a'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    have hga : act d.radical g⁻¹ a = a := (stabilizer d.radical a).inv_mem hg
    have hmZ := Z_act d.radical g⁻¹ a
    have hmQ := Q_act d.radical g⁻¹ a'
    simp only [inv_inv,hga] at hmZ hmQ
    rwa [←hmZ,←hmQ]

include s in
/-- A single actual conjugator moves both the small critical kernel and its
line, and carries the full critical path with it. This is a synchronized
choice; it does not assert the additional shifted-path conditions of (5.11). -/
theorem exists_small_critical_kernel_line_displacement (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ∃ g ∈ stabilizer d.radical a,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g a'),
      (∀ i, q.walk.getVert i = act d.radical g (p.walk.getVert i)) ∧
      (Q d.radical (act d.radical g a')).relIndex (Z d.radical a) = 2 ∧
      Z d.radical a ⊓ Q d.radical (act d.radical g a') ≠ Z d.radical a ⊓ Q d.radical a' ∧
      ⁅Z d.radical a,Z d.radical (act d.radical g a')⁆ ≠ ⁅Z d.radical a,Z d.radical a'⁆ := by
  classical
  have hn := small_critical_kernel_not_normalized s hc p hp
  obtain ⟨g,hg,hgn⟩ := SetLike.not_le_iff_exists.mp hn
  let k := g⁻¹
  have hk : k ∈ stabilizer d.radical a := (stabilizer d.radical a).inv_mem hg
  have hka : act d.radical k a = a := hk
  have hpath : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical k a) (act d.radical k a'),
      ∀ i, q.walk.getVert i = act d.radical k (p.walk.getVert i) :=
    ⟨p.act k,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hka] at hpath
  obtain ⟨q,hwalk⟩ := hpath
  have hq : (Q d.radical (act d.radical k a')).relIndex (Z d.radical a) < 4 := by
    rw [←hka,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hp
  have hkernel : Z d.radical a ⊓ Q d.radical (act d.radical k a') ≠
      Z d.radical a ⊓ Q d.radical a' := by
    intro he
    apply hgn
    change g ∈ normalizer ((Z d.radical a ⊓ Q d.radical a' :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Z d.radical a ⊓ Q d.radical a').map (MulAut.conj g).toMonoidHom =
      Z d.radical a ⊓ Q d.radical a'
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    have hZ : (Z d.radical a).map (MulAut.conj g).toMonoidHom = Z d.radical a := by
      simpa only [k,inv_inv,hka] using (Z_act d.radical k a).symm
    rw [hZ]
    simpa only [Q_act,k,inv_inv] using he
  refine ⟨k,hk,q,hwalk,(small_critical_indices s hc q hq).1,hkernel,?_⟩
  exact fun he => hkernel (small_critical_equal_lines_kernels s hc q p hq hp he)


include s in
/-- The kernel's setwise stabilizer is exactly the pointwise fixer of its
order-two critical line, relative to the same vertex stabilizer. -/
theorem small_critical_kernel_normalizer_eq_line_centralizer (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    stabilizer d.radical a ⊓ normalizer
      ((Z d.radical a ⊓ Q d.radical a' : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) =
    stabilizer d.radical a ⊓ centralizer
      ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  rw [small_critical_kernel_normalizer_eq_line_normalizer s hc p hp]
  apply le_antisymm
  · exact inf_le_inf_left _ (normalizer_le_centralizer_of_card_two _
      (small_critical_commutator_card s hc p hp))
  · exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)

/-- Application to the small opposite-radius branch on the original
replacement. The same conjugator transports the critical path, line and full
kernel; the critical-index premise follows from the radius bound. -/
theorem small_opposite_radius_conjugate_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hline : (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)).map
        (MulAut.conj g⁻¹).toMonoidHom = ⁅Z d.radical a,Z d.radical a'⁆) :
    ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g a'),
      (∀ i, q.walk.getVert i = act d.radical g (p.walk.getVert i)) ∧
      Z d.radical a ⊓ Q d.radical (act d.radical g a') = Z d.radical a ⊓ Q d.radical a' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_index_two_of_small_opposite_radius s hc hb p hsmall
  have hga : act d.radical g a = a := hg
  have hpath : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g a) (act d.radical g a'),
      ∀ i, q.walk.getVert i = act d.radical g (p.walk.getVert i) :=
    ⟨p.act g,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hga] at hpath
  obtain ⟨q,hwalk⟩ := hpath
  exact ⟨q,hwalk,(small_critical_conjugate_kernel_iff s hc p (by omega) g hg).mpr hline⟩

/-- The original replacement supplies one simultaneous displacement of the
path, full kernel and line in the remaining small-radius branch. -/
theorem small_opposite_radius_kernel_line_displacement_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    ∃ g ∈ stabilizer d.radical a,
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical g a'),
      (∀ i, q.walk.getVert i = act d.radical g (p.walk.getVert i)) ∧
      (Q d.radical (act d.radical g a')).relIndex (Z d.radical a) = 2 ∧
      Z d.radical a ⊓ Q d.radical (act d.radical g a') ≠ Z d.radical a ⊓ Q d.radical a' ∧
      ⁅Z d.radical a,Z d.radical (act d.radical g a')⁆ ≠ ⁅Z d.radical a,Z d.radical a'⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_index_two_of_small_opposite_radius s hc hb p hsmall
  exact exists_small_critical_kernel_line_displacement s hc p (by omega)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
