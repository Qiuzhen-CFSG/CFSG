module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusCentralQuotient
public import Theory.Representation.BinaryPermutation.SixCentralDerived
public import Theory.Representation.BinaryPermutation.SixTransitivity
public import Theory.GroupTheory.ClassTwoIndexTwoDerived

/-!
# Derived-group transfer for the actual natural central section

A nonabelian normal section with natural binary four-dimensional quotient
has precisely its whole center as quotient kernel. Indeed, alternating-six
transitivity on the fifteen nonzero vectors would otherwise make every
coset have a central lift, forcing the section to be abelian. Its central
index is therefore sixteen. When the original alternating component fixes
the derived subgroup, the natural-cover commutator calculation makes that
subgroup a line of order two. The class-two index-two theorem then shows
that every subgroup of relative index at most two retains the same derived
line.

The graph application uses the full radius pulled back through the original
free-amalgam embedding. Its nonabelianness follows from an actual critical
pair at distance four; the source fixed-core assumption supplies fixation
by the original component. The final transfer is an equality of literal
graph commutators, and the known-simple application keeps the canonical
marked projection. The normal-section version also applies to a selected
normal orbit span once its source hypotheses have been constructed.

These are the binary central-section and hyperplane calculations in MS93
(3.10)(i), printed pp.880--881, used by (5.12), pp.924--927. They do not
assert that the full radius or the original cover is already natural.
The selected section, its central-kernel and fixed-core hypotheses, and the
terminal arguments (5.11)--(5.12) remain with
qt-e-ms-small-a6-exhaustion-large-distance; the final unconditional
reconstruction remains with qt-e-ms-small-a6-reconstruction.
-/

public section
open Subgroup
open scoped commutatorElement

private theorem natural_section_kernel_eq_center
    {P A : Type*} [Group P] [Group A]
    (q : P →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hker : q.ker ≤ center P) (hne : _root_.commutator P ≠ ⊥)
    (ρ : A →* MulAut P) (π : A →* Equiv.Perm (Fin 6))
    (hπ : alternatingGroup (Fin 6) ≤ π.range)
    (hequiv : ∀ a x, (q (ρ a x)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (π a) (q x).toAdd) :
    q.ker = center P := by
  apply le_antisymm hker
  intro z hz
  by_contra hzq
  have hz0 : (q z).toAdd ≠ 0 := hzq
  have hcent (x : P) : x ∈ center P := by
    by_cases hxq : q x = 1
    · exact hker hxq
    obtain ⟨g,hg⟩ := BinaryPermutation.alternatingSix_natural_nonzero_transitive
      (q z).toAdd (q x).toAdd hz0 hxq
    obtain ⟨a,ha⟩ := hπ g.property
    have he : q (ρ a z) = q x := by
      apply Multiplicative.toAdd.injective
      rw [hequiv,ha,hg]
    have hr : ρ a z ∈ center P := (centerCongr (ρ a) ⟨z,hz⟩).property
    have hd : (ρ a z)⁻¹*x ∈ center P := hker (by
      rw [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel])
    simpa only [mul_inv_cancel_left] using (center P).mul_mem hr hd
  apply hne
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x _ y _
  exact mem_center_iff.mp (hcent x) y

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

omit [Finite G] in
private theorem derived_nontrivial_iff (W : Subgroup d.overgroup) :
    _root_.commutator W ≠ ⊥ ↔ ⁅W,W⁆ ≠ ⊥ := by
  rw [←W.map_subtype_commutator]
  constructor
  · intro hn hz
    apply hn
    apply (map_injective W.subtype_injective)
    simpa only [Subgroup.map_bot] using hz
  · intro hn hz
    exact hn (by rw [hz,Subgroup.map_bot])

private theorem section_component_image :
    alternatingGroup (Fin 6) ≤ (s.projection.comp (replacementComponent d).subtype).range := by
  rw [MonoidHom.range_comp,(replacementComponent d).range_subtype,s.component_image]

omit [Finite G] in
private theorem section_derived_central
    (W : Subgroup d.overgroup)
    (q : W →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hker : q.ker ≤ center W) : _root_.commutator W ≤ center W := by
  apply le_trans _ hker
  apply commutator_le.mpr
  intro x _ y _
  rw [MonoidHom.mem_ker,map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

/-- The kernel of a nonabelian natural central section is its entire center. -/
theorem natural_section_kernel_center
    (W : Subgroup d.overgroup) [W.Normal]
    (hW : ⁅W,W⁆ ≠ ⊥)
    (q : W →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hker : q.ker ≤ center W)
    (hequiv : ∀ (m : d.overgroup) (x : W),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) (q x).toAdd) :
    q.ker = center W := by
  exact natural_section_kernel_eq_center q hker ((derived_nontrivial_iff W).mpr hW)
    (MulAut.conjNormal.comp (replacementComponent d).subtype)
    (s.projection.comp (replacementComponent d).subtype) (section_component_image s)
    (fun a x => hequiv a x)

/-- The nonabelian natural section has central index sixteen. -/
theorem natural_section_center_index
    (W : Subgroup d.overgroup) [W.Normal]
    (hW : ⁅W,W⁆ ≠ ⊥)
    (q : W →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (hker : q.ker ≤ center W)
    (hequiv : ∀ (m : d.overgroup) (x : W),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) (q x).toAdd) :
    (center W).index = 16 := by
  rw [←natural_section_kernel_center s W hW q hker hequiv,index_ker,
    q.range_eq_top_of_surjective hq,Nat.card_congr (topEquiv).toEquiv]
  change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
  rfl

/-- The alternating actor's fixation makes the derived group a single line. -/
theorem natural_section_derived_card
    (W : Subgroup d.overgroup) [W.Normal]
    (hW : ⁅W,W⁆ ≠ ⊥)
    (q : W →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (hker : q.ker ≤ center W)
    (hequiv : ∀ (m : d.overgroup) (x : W),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) (q x).toAdd)
    (hfix : ⁅W,W⁆ ≤ centralizer (replacementComponent d : Set d.overgroup)) :
    Nat.card (⁅W,W⁆ : Subgroup d.overgroup) = 2 := by
  have hb : Nat.card (_root_.commutator W) ≤ 2 :=
    BinaryPermutation.SixCentralDerived.card_derived_le_two q hq hker
      (MulAut.conjNormal.comp (replacementComponent d).subtype)
      (s.projection.comp (replacementComponent d).subtype) (section_component_image s)
      (fun a x => hequiv a x) (by
        intro a _ z hz
        apply Subtype.ext
        have hzW : (z : d.overgroup) ∈ ⁅W,W⁆ := by
          rw [←W.map_subtype_commutator]
          exact mem_map_of_mem W.subtype hz
        change (a : d.overgroup) * z * (a : d.overgroup)⁻¹ = z
        rw [hfix hzW a a.property,mul_inv_cancel_right])
  have he : Nat.card (_root_.commutator W) = Nat.card (⁅W,W⁆ : Subgroup d.overgroup) := by
    rw [←W.map_subtype_commutator]
    exact Nat.card_congr ((_root_.commutator W).equivMapOfInjective W.subtype
      W.subtype_injective).toEquiv
  have hl := (one_lt_card_iff_ne_bot ⁅W,W⁆).mpr hW
  omega

/-- Every subgroup of relative index at most two retains the original derived line. -/
theorem natural_section_derived_transfer
    (W : Subgroup d.overgroup) [W.Normal]
    (hW : ⁅W,W⁆ ≠ ⊥)
    (q : W →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (hker : q.ker ≤ center W)
    (hequiv : ∀ (m : d.overgroup) (x : W),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) (q x).toAdd)
    (hfix : ⁅W,W⁆ ≤ centralizer (replacementComponent d : Set d.overgroup))
    (A : Subgroup d.overgroup) (hAW : A ≤ W) (hi : A.relIndex W ≤ 2) :
    ⁅A,A⁆ = ⁅W,W⁆ := by
  have hc := section_derived_central W q hker
  have hcard : Nat.card (_root_.commutator W) = 2 := by
    rw [←natural_section_derived_card s W hW q hq hker hequiv hfix,
      ←W.map_subtype_commutator]
    exact Nat.card_congr ((_root_.commutator W).equivMapOfInjective W.subtype
      W.subtype_injective).toEquiv
  have hlarge : 4 < (center W).index := by
    rw [natural_section_center_index s W hW q hq hker hequiv]
    decide
  have ht := ClassTwo.commutator_eq_of_index_le_two_of_center_index_gt_four
    hc hcard hlarge (A.subgroupOf W) hi
  have hm := congrArg (Subgroup.map W.subtype) ht
  rwa [map_commutator,map_subgroupOf_eq_of_le hAW,W.map_subtype_commutator] at hm

include s in
/-- The graph radius is nonabelian on the original finite preimage. -/
theorem radiusPreimage_derived_ne_bot (hc : DistanceTwo.CentralLayer d)
    (hb : replacementDistance h d = 4) :
    ⁅radiusPreimage d,radiusPreimage d⁆ ≠ ⊥ := by
  intro hz
  apply radius_derived_ne_bot s hc hb (alpha d.radical) rfl
  have hm := congrArg (Subgroup.map (embedM d.radical)) hz
  rwa [map_commutator,radius_comap_map (h := h) (show 2 < replacementDistance h d by omega),Subgroup.map_bot] at hm

private theorem radius_derived_fixed_preimage
    (hb : 2 < replacementDistance h d)
    (hD : ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical)) :
    ⁅radiusPreimage d,radiusPreimage d⁆ ≤
      centralizer (replacementComponent d : Set d.overgroup) := by
  intro z hz m hm
  apply embedM_injective d.radical
  simp only [map_mul]
  have hz' := mem_map_of_mem (embedM d.radical) hz
  rw [map_commutator,radius_comap_map (h := h) hb] at hz'
  apply (hD hz').2
  have hL : (replacementComponent d).map (embedM d.radical) =
      Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  rw [←hL]
  exact mem_map_of_mem (embedM d.radical) hm

/-- MS93 (3.10)'s binary derived-line calculation on the full actual radius,
under the natural central-section and fixed-core hypotheses used by (5.12). -/
theorem radius_natural_section_derived_card
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (q : radiusPreimage d →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (hker : q.ker ≤ center (radiusPreimage d))
    (hequiv : ∀ (m : d.overgroup) (x : radiusPreimage d),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) (q x).toAdd)
    (hD : ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical)) :
    Nat.card (⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ :
      Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hd := natural_section_derived_card s (radiusPreimage d)
    (radiusPreimage_derived_ne_bot s hc hb) q hq hker hequiv
    (radius_derived_fixed_preimage (h := h) (by omega) hD)
  have he := Nat.card_congr ((⁅radiusPreimage d,radiusPreimage d⁆ : Subgroup d.overgroup).equivMapOfInjective (embedM d.radical) (embedM_injective d.radical)).toEquiv
  rw [map_commutator,radius_comap_map (h := h) (show 2 < replacementDistance h d by omega)] at he
  exact he.symm.trans hd

/-- Transfer keeps the literal graph subgroup and its derived group. -/
theorem radius_natural_section_derived_transfer
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (q : radiusPreimage d →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (hker : q.ker ≤ center (radiusPreimage d))
    (hequiv : ∀ (m : d.overgroup) (x : radiusPreimage d),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection m) (q x).toAdd)
    (hD : ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ V d.radical (alpha d.radical))
    (hi : A.relIndex (V d.radical (alpha d.radical)) ≤ 2) :
    ⁅A,A⁆ = ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ := by
  have hpre : (A.comap (embedM d.radical)).relIndex (radiusPreimage d) ≤ 2 := by
    rw [relIndex_comap,radius_comap_map (h := h) (show 2 < replacementDistance h d by omega)]
    exact hi
  have ht := natural_section_derived_transfer s (radiusPreimage d)
    (radiusPreimage_derived_ne_bot s hc hb) q hq hker hequiv
    (radius_derived_fixed_preimage (h := h) (by omega) hD)
    (A.comap (embedM d.radical)) (comap_mono hA) hpre
  have hAm : (A.comap (embedM d.radical)).map (embedM d.radical) = A := by
    rw [map_comap_eq,inf_eq_right]
    apply hA.trans
    rw [←radius_comap_map (h := h) (show 2 < replacementDistance h d by omega)]
    exact (radiusPreimage d).map_le_range (embedM d.radical)
  have hm := congrArg (Subgroup.map (embedM d.radical)) ht
  rwa [map_commutator,map_commutator,hAm,radius_comap_map (h := h) (show 2 < replacementDistance h d by omega)] at hm

/-- Original minimum characteristic replacement, using the canonical projection.
The source section and fixed-core premises remain with this large-distance owner. -/
theorem radius_natural_section_derived_transfer_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : replacementDistance h d = 4)
    (q : radiusPreimage d →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (hker : q.ker ≤ center (radiusPreimage d))
    (hequiv : ∀ (m : d.overgroup) (x : radiusPreimage d),
      (q (MulAut.conjNormal m x)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6)
          (SourceReduction.projection h e hz hn d m) (q x).toAdd)
    (hD : ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ V d.radical (alpha d.radical))
    (hi : A.relIndex (V d.radical (alpha d.radical)) ≤ 2) :
    ⁅A,A⁆ = ⁅V d.radical (alpha d.radical),V d.radical (alpha d.radical)⁆ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (show 2 < replacementDistance h d by omega)
  apply radius_natural_section_derived_transfer s
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb q hq hker _ hD A hA hi
  intro m x
  rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  exact hequiv m x

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
