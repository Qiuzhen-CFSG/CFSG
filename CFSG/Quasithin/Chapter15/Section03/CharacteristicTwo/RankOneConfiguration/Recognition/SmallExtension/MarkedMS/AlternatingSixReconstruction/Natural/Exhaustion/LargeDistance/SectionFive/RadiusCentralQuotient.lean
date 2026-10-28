module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.ChiefFactor
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The actual radius central quotient in the symmetric branch

The source radius is of class at most two, and its involution generators
make its quotient by its own center elementary abelian. Radius centrality
makes the original two-core act trivially on this quotient. Conjugation
therefore descends through the same marked symmetric-six projection.

At distance four a critical pair at a midpoint makes the radius nonabelian.
A nontrivial kernel of the descended action would contain the alternating
component. The edge-plus-residual decomposition would then express the
radius as an abelian edge radius times central elements, a contradiction.
Thus the actual central quotient has faithful symmetric-six action. No
natural subgroup or splitting of the original cover is assumed.

This supplies central-quotient preparation for MS93 (3.10) and (5.12),
printed pp.879--881 and 924--927. Recognition of the selected orbit-span
section and the terminal path arguments remain with the large-distance owner.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
private theorem elementary_central_quotient_of_squares {P : Type*} [Group P]
    (hs : ∀ x : P, x^2 ∈ center P) : IsElementaryAbelian 2 (P ⧸ center P) := by
  have hp (x : P ⧸ center P) : x^2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center P) x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hs x)
  have : IsMulCommutative (P ⧸ center P) :=
    ⟨⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp⟩

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The full radius, including the central attachment, has class at most two. -/
theorem radius_derived_central (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (a : Vertex d.radical)
    (ha : color d.radical a = false) :
    ⁅V d.radical a,V d.radical a⁆ ≤ centralizer (V d.radical a : Set (FreeAmalgam d.radical)) :=
  (commutator_mono le_rfl (V_le_Q d.radical ha hb)).trans
    (radius_commutator_central_general_at s hc hb a ha)

include s in
/-- Critical noncommutation makes the radius nonabelian at distance four. -/
theorem radius_derived_ne_bot (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) (a : Vertex d.radical)
    (ha : color d.radical a = false) : ⁅V d.radical a,V d.radical a⁆ ≠ ⊥ := by
  have hbase : ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≠ ⊥ := by
    obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
      (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
    have hl : p.walk.length = 4 := p.length_eq_b.trans hb
    have hcol : color d.radical (p.walk.getVert 2) = false :=
      (p.vertex_color (by omega)).mpr (by decide)
    obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hcol
    have hV : V d.radical (p.walk.getVert 2) =
        (V d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hg]
      simpa only [alpha,act_mVertex,one_mul] using V_act (R := d.radical) g (alpha d.radical)
    intro hbot
    have hmid : ⁅V d.radical (p.walk.getVert 2),V d.radical (p.walk.getVert 2)⁆ = ⊥ := by
      rw [hV,←map_commutator,hbot,Subgroup.map_bot]
    have hleft : Z d.radical (alpha d.radical) ≤ V d.radical (p.walk.getVert 2) :=
      le_iSup_of_le _ (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
    have hright : Z d.radical a' ≤ V d.radical (p.walk.getVert 2) :=
      le_iSup_of_le _ (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
    exact critical_Z_commutator_ne_bot s hc p
      (le_bot_iff.mp ((commutator_mono hleft hright).trans_eq hmid))
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  have hV : V d.radical (mVertex d.radical g) =
      (V d.radical (alpha d.radical)).map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [alpha,act_mVertex,one_mul] using V_act (R := d.radical) g (alpha d.radical)
  rw [hV,←map_commutator]
  intro hz
  apply hbase
  exact (map_injective (MulAut.conj g⁻¹).injective) (by simpa only [Subgroup.map_bot] using hz)

include s in
/-- Kernel commutators of the literal radius preimage are central in it. -/
theorem radiusPreimage_kernel_commutator_central (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) :
    ⁅radiusPreimage d,pCore 2 d.overgroup⁆ ≤ centralizer (radiusPreimage d : Set d.overgroup) := by
  intro z hz y hy
  apply embedM_injective d.radical
  simp only [map_mul]
  apply radius_commutator_central_general s hc hb
  · have hm := mem_map_of_mem (embedM d.radical) hz
    rw [map_commutator,radius_comap_map (h := h) hb,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hm
    exact hm
  · exact hy

include s in
/-- The actual central quotient is elementary; the radius itself need not be. -/
theorem radius_central_quotient_elementary (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) :
    IsElementaryAbelian 2 ((radiusPreimage d) ⧸ center (radiusPreimage d)) := by
  apply elementary_central_quotient_of_squares
  intro x
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply embedM_injective d.radical
  change embedM d.radical ((y : d.overgroup) * (x : d.overgroup)^2) =
    embedM d.radical ((x : d.overgroup)^2 * (y : d.overgroup))
  simp only [map_mul,map_pow]
  exact radius_derived_central s hc hb (alpha d.radical) rfl
    (radius_sq_mem_derived (replacementGeometry h d) (replacementDistance_pos h d)
      (alpha d.radical) rfl ⟨embedM d.radical x,x.property⟩)
    (embedM d.radical y) y.property

/-- Literal conjugation on the center quotient of the pulled-back radius. -/
def radiusCentralAction (d : Replacement L R) :
    d.overgroup →* MulAut ((radiusPreimage d) ⧸ center (radiusPreimage d)) :=
  (quotientAut (center (radiusPreimage d))).comp (MulAut.conjNormal (H := radiusPreimage d))

omit [Finite G] in
theorem radiusCentralAction_apply (m : d.overgroup) (x : radiusPreimage d) :
    radiusCentralAction d m (QuotientGroup.mk' (center (radiusPreimage d)) x) =
      QuotientGroup.mk' (center (radiusPreimage d)) (MulAut.conjNormal m x) :=
  quotientAut_apply_mk _ _ _

include s in
/-- The original two-core is killed, so no replacement quotient is substituted. -/
theorem radiusCentralAction_kills_core (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) : pCore 2 d.overgroup ≤ (radiusCentralAction d).ker := by
  intro m hm
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (center (radiusPreimage d)) v
  rw [radiusCentralAction_apply]
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hx : ⁅m,(x : d.overgroup)⁆ ∈ ⁅radiusPreimage d,pCore 2 d.overgroup⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hm x.property
  change (y : d.overgroup) * (m * (x : d.overgroup) * m⁻¹ / x) =
    (m * (x : d.overgroup) * m⁻¹ / x) * y
  simpa only [div_eq_mul_inv,commutatorElement_def] using
    radiusPreimage_kernel_commutator_central s hc hb hx y y.property

/-- Descent through the given full symmetric projection. -/
def radiusSymmetricCentralAction (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) :
    Equiv.Perm (Fin 6) →* MulAut ((radiusPreimage d) ⧸ center (radiusPreimage d)) :=
  s.projection.liftOfSurjective s.surjective ⟨radiusCentralAction d,by
    rw [s.projection_kernel]
    exact radiusCentralAction_kills_core s hc hb⟩

theorem radiusSymmetricCentralAction_projection (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) (m : d.overgroup) :
    radiusSymmetricCentralAction s hc hb (s.projection m) = radiusCentralAction d m := by
  simp [radiusSymmetricCentralAction,MonoidHom.liftOfSurjective]

include s in
/-- Faithfulness holds for any descent with the literal projection identity. -/
theorem radiusCentralAction_faithful (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4)
    (ρ : Equiv.Perm (Fin 6) →* MulAut ((radiusPreimage d) ⧸ center (radiusPreimage d)))
    (hρ : ∀ m : d.overgroup, ρ (s.projection m) = radiusCentralAction d m) :
    Function.Injective ρ := by
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  by_contra hne
  have hAlt : alternatingGroup (Fin 6) ≤ ρ.ker :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot _).mpr hne)
  let P := radiusPreimage d
  let E := (V d.radical (beta d.radical)).comap (embedM d.radical)
  let C := (center P).map P.subtype
  have hCP : C ≤ P := map_subtype_le _
  have hCC : C ≤ centralizer (P : Set d.overgroup) := by
    rintro _ ⟨z,hz,rfl⟩ y hy
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hy⟩)
  have hPL : ⁅P,replacementComponent d⁆ ≤ C := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro m hm z hz
    have hmAlt : s.projection m ∈ alternatingGroup (Fin 6) :=
      s.component_image ▸ mem_map_of_mem s.projection hm
    have he := hρ m
    rw [MonoidHom.mem_ker.mp (hAlt hmAlt)] at he
    have hh := DFunLike.congr_fun he (QuotientGroup.mk' (center P) ⟨z,hz⟩)
    have hq : QuotientGroup.mk' (center P) (MulAut.conjNormal m ⟨z,hz⟩) =
        QuotientGroup.mk' (center P) ⟨z,hz⟩ := by
      exact (radiusCentralAction_apply m ⟨z,hz⟩).symm.trans
        (by simpa only [MulAut.one_apply] using hh.symm)
    have hmem : MulAut.conjNormal m ⟨z,hz⟩ / ⟨z,hz⟩ ∈ center P :=
      QuotientGroup.eq_iff_div_mem.mp hq
    refine ⟨MulAut.conjNormal m ⟨z,hz⟩ / ⟨z,hz⟩,hmem,?_⟩
    change m*z*m⁻¹/z = ⁅m,z⁆
    rw [div_eq_mul_inv,commutatorElement_def]
  have hEP : E ≤ P := comap_mono (edge_radius_le_radius rfl (base_adjacent d.radical))
  have hE : E ≤ centralizer (E : Set d.overgroup) := by
    have hcomm := le_centralizer_iff_isMulCommutative.mpr
      (edge_radius_commutative (replacementGeometry h d) (show 2 < replacementDistance h d by omega)
        (alpha d.radical) (beta d.radical) rfl (base_adjacent d.radical))
    intro x hx y hy
    apply embedM_injective d.radical
    simpa only [map_mul] using hcomm hx (embedM d.radical y) hy
  let B := E ⊔ C
  have hPB : P ≤ B :=
    (radius_comap_le_edge_sup_commutator (h := h) (show 2 < replacementDistance h d by omega)).trans
      (sup_le_sup_left hPL _)
  have hBP : B ≤ P := sup_le hEP hCP
  have hB : B ≤ centralizer (B : Set d.overgroup) := by
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact sup_le hE (hCC.trans (centralizer_le hEP))
    · exact hCC.trans (centralizer_le hBP)
  have hbot : ⁅P,P⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    ((hPB.trans hB).trans (centralizer_le hPB))
  apply radius_derived_ne_bot s hc hb (alpha d.radical) rfl
  have hh := congrArg (Subgroup.map (embedM d.radical)) hbot
  rwa [map_commutator,radius_comap_map (h := h)
    (show 2 < replacementDistance h d by omega),Subgroup.map_bot] at hh

/-- The constructed quotient action is faithful at distance four. -/
theorem radiusSymmetricCentralAction_injective (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) :
    Function.Injective (radiusSymmetricCentralAction s hc (by omega)) :=
  radiusCentralAction_faithful s hc hb _ (radiusSymmetricCentralAction_projection s hc (by omega))

include s in
/-- The kernel of the original conjugation action is exactly its two-core. -/
theorem radiusCentralAction_kernel (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) :
    (radiusCentralAction d).ker = pCore 2 d.overgroup := by
  apply le_antisymm _ (radiusCentralAction_kills_core s hc (by omega))
  intro m hm
  have he := radiusSymmetricCentralAction_projection s hc
    (show 2 < replacementDistance h d by omega) m
  rw [MonoidHom.mem_ker.mp hm,←map_one (radiusSymmetricCentralAction s hc (by omega))] at he
  have hproj : s.projection m = 1 := radiusSymmetricCentralAction_injective s hc hb he
  rw [←s.projection_kernel]
  exact hproj

include s in
/-- The central quotient is too large for the abelian index-two exception
in the source's derived-subgroup transfer argument. -/
theorem radius_center_index_gt_four (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) : 4 < (center (radiusPreimage d)).index := by
  let ρ := radiusSymmetricCentralAction s hc (show 2 < replacementDistance h d by omega)
  have hρ : Function.Injective ρ := radiusSymmetricCentralAction_injective s hc hb
  have hi := Nat.card_le_card_of_injective (f := fun g => (ρ g).toEquiv)
    (MulEquiv.toEquiv_injective.comp hρ)
  change Nat.card (Equiv.Perm (Fin 6)) ≤
    Nat.card (Equiv.Perm ((radiusPreimage d) ⧸ center (radiusPreimage d))) at hi
  rw [Nat.card_perm,Nat.card_fin,Nat.card_perm] at hi
  rw [index_eq_card]
  by_contra hn
  have hh := Nat.factorial_le (show Nat.card ((radiusPreimage d) ⧸ center (radiusPreimage d)) ≤ 4 by omega)
  have hs : Nat.factorial 6 = 720 := rfl
  have ht : Nat.factorial 4 = 24 := rfl
  omega

/-- The original replacement has a genuine elementary central quotient with
faithful action through its canonical marked projection. This is construction
of a section; recognition of the selected source section remains separate. -/
theorem radius_central_quotient_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4) :
    IsElementaryAbelian 2 ((radiusPreimage d) ⧸ center (radiusPreimage d)) ∧
      ∃ ρ : Equiv.Perm (Fin 6) →* MulAut ((radiusPreimage d) ⧸ center (radiusPreimage d)),
        Function.Injective ρ ∧ ∀ m : d.overgroup,
          ρ (SourceReduction.projection h e hz hn d m) = radiusCentralAction d m := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (show 2 < replacementDistance h d by omega)
  let hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  refine ⟨radius_central_quotient_elementary s hc (by omega),
    radiusSymmetricCentralAction s hc (by omega),radiusSymmetricCentralAction_injective s hc hb,?_⟩
  intro m
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  exact radiusSymmetricCentralAction_projection s hc (by omega) m

/-- On every original distance-four replacement the central quotient action
has precisely the actual two-core as its kernel. -/
theorem radiusCentralAction_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4) :
    (radiusCentralAction d).ker = pCore 2 d.overgroup :=
  radiusCentralAction_kernel (fullSymmetricAction_knownSimple h e hz hn d (by omega))
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb

/-- The same original-replacement application gives the strict central-index
bound used by the source's class-two transfer. -/
theorem radius_center_index_gt_four_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4) :
    4 < (center (radiusPreimage d)).index :=
  radius_center_index_gt_four (fullSymmetricAction_knownSimple h e hz hn d (by omega))
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
