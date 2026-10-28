module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SecondaryNatural
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalRatioBounds
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.FixedQuotientEquality
public import Theory.Representation.BinaryConjugationSection.RelativeFixedIndex
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.DisplacementPreimage
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Sharp paired images and their full fixed preimages

The natural moved section has the same original field degree as the critical
pair. The opposite secondary image lies in the marked component. Its natural
ratio bound, combined with the paired q-factor index estimate, forces both
images to have order q cubed and the full secondary fixed codimension to be
2n. No ordering of the original endpoints remains in the result.

Equality identifies the literal quotient centralizer with the opposite-kernel
intersection times Z. It also proves that every fixed vector in the natural
section has all its lifts fixed in the moved space, and that this moved space
supplements the full fixed space. The final group application expresses the
whole secondary orbit as its component commutator times that kernel supplement.
The constructed sharp section retains its original quotient coordinates.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871. The passage
from the kernel supplement to full movement, the paired-orbit contradiction,
whole-core control and the (3.7) field restriction remain to be established.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition

variable {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) J V) (C : Subgroup J) [C.Normal]
  {n : ℕ}
private theorem natural_moved_rank_bound (hn : 0 < n)
    (hnat : NaturalMovedSectionAtDegree σ C n)
    {B : Subgroup J} (hBC : B ≤ C) (hB : IsElementaryTwo B) :
    2 * rank B ≤ 3 * fixedCodim (MovedSection.ofNormal σ C).action B := by
  obtain ⟨E,hE,⟨e⟩⟩ := hnat.2.2
  let A := (B.subgroupOf C).map e.groupEquiv.toMonoidHom
  let := hB.2
  let : IsElementaryAbelian 2 (B.subgroupOf C) := IsElementaryAbelian.subgroupOf hBC
  have hA : IsElementaryTwo A := by
    refine ⟨?_,IsElementaryAbelian.map _⟩
    intro he
    have hb : B.subgroupOf C = ⊥ :=
      ((B.subgroupOf C).map_eq_bot_iff_of_injective e.groupEquiv.injective).mp he
    apply hB.1
    rw [←map_subgroupOf_eq_of_le hBC,hb,Subgroup.map_bot]
  have hf : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hh := SymplecticConjugatePair.NaturalBounds.elementary_natural_bound hf hn hA
  have he := fixedCodim_map_equivariant
    ((MovedSection.ofNormal σ C).action.comp C.subtype) (binarySymplectic E)
    e.groupEquiv.toMonoidHom e.linearEquiv e.intertwines (B.subgroupOf C)
  have hr : rank A = rank B := by
    rw [rank_map_injective e.groupEquiv.toMonoidHom e.groupEquiv.injective,rank_subgroupOf hBC]
  rw [fixedCodim_subgroupOf _ hBC] at he
  change 2 * rank A ≤ 3 * fixedCodim (binarySymplectic E) A at hh
  rwa [hr,←he] at hh


open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Sp4Four.CoreReconstruction
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h
private def reverse_secondary_path
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    CriticalPath d.radical g z a := {
  start_color := path.end_color
  walk := path.walk.reverse
  shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
  critical := critical_reverse d.radical g
    (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
    a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
    z path.end_color path.critical }

omit h [Finite H] [Finite F] [CharP F 2] [Field F] in
private theorem opposite_nonfrattini
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
  obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
  have he : act d.radical v (alpha d.radical) = a := by
    rw [hv]
    simp only [alpha,act_mVertex,one_mul]
  exact nonfrattini_at_vertex d.radical
    ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge))
    path.end_color


/-- The opposite secondary image lies in the actual marked component. -/
theorem replacement_secondary_actor_le_component
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {J : Type*} [Group J] (κ : stabilizer d.radical a →* J) (C : Subgroup J)
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ = C) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ C := by
  let S := stabilizer d.radical a
  let rev := reverse_secondary_path h d path hb
  have hl := opposite_nonfrattini d path hlarge
  have hAQ := (replacement_secondary_orbit_bounds h d rev hb hzt hat hl).1
  have hk' : κ.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hk,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hpre : C.comap κ = (Ltilde d.radical a ⊔ Q d.radical a).subgroupOf S := by
    rw [←hL,comap_map_eq,hk',subgroupOf_sup (Ltilde_le_stabilizer a)
      (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  apply map_le_iff_le_comap.mpr
  rw [hpre]
  exact comap_mono (hAQ.trans (replacement_nonfrattini_kernel_le_component h d rev hb hl))

/-- The actual quotient centralizer index is the power of two given by its
fixed codimension, with the entire Z-layer retained. -/
theorem replacement_secondary_fixed_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* J) (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    (commutatorPreimage A A' (Z d.radical a)).relIndex A =
      2 ^ fixedCodim σ ((A'.subgroupOf (stabilizer d.radical a)).map κ) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let S := stabilizer d.radical a
  let rev := reverse_secondary_path h d path hb
  have hl := opposite_nonfrattini d path hlarge
  have hAQ := (replacement_secondary_orbit_bounds h d rev hb hzt hat hl).1
  have hAS : A' ≤ S := hAQ.trans
    (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by
      rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color]
      exact hb))
  let : Finite S := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  have he := c.fixed_index_of_relative_normalizers A' hAS
    (c.section_le.trans (Z_normalized d.radical a)) (hAS.trans (Z_normalized d.radical a))
  have hfix : fixedCodim (σ.comp κ) (A'.subgroupOf S) =
      fixedCodim σ ((A'.subgroupOf S).map κ) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  rw [hfix] at he
  exact he

/-- Equality in the paired estimate forces the sharp image orders and
codimension on both the whole secondary quotient and its natural moved section. -/
theorem replacement_secondary_sharp_of_index_le
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (horder : (Q d.radical z).relIndex
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) ≤
      (Q d.radical a).relIndex
        (Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup))
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
      replacementComponent d)
    (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup) V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
    let := replacementComponent_normal h d
    (Q d.radical z).relIndex A = (2^n)^3 ∧
      (Q d.radical a).relIndex A' = (2^n)^3 ∧
      fixedCodim σ B = 2*n ∧
      fixedCodim (MovedSection.ofNormal σ (replacementComponent d)).action B = 2*n := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
  let := replacementComponent_normal h d
  let s := MovedSection.ofNormal σ (replacementComponent d)
  let : Finite (stabilizer d.radical a) := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite V := Finite.of_surjective (fun u : A => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hn := replacement_secondary_moved_natural_of_index_le h d path hb hat hzt hlarge
    horder κ hk hL σ c
  have ho := replacement_secondary_offender_of_index_le h d path hb hat hzt hlarge
    horder κ hk σ c
  have hBC := replacement_secondary_actor_le_component h d path hb hat hzt hlarge κ
    (replacementComponent d) hk hL
  have hratio := natural_moved_rank_bound σ (replacementComponent d)
    (lt_trans Nat.zero_lt_one h.nonbinary) hn hBC ho.1
  change 2 * rank B ≤ 3 * fixedCodim s.action B at hratio
  obtain ⟨_,hcard⟩ := replacement_secondary_actor_image h d path hb hat hzt hlarge κ hk
  have hprod := (replacement_paired_centralizer_index h d path hb hat hzt hlarge).1
  rw [replacement_secondary_fixed_index h d path hb hat hzt hlarge κ σ c] at hprod
  have hpower : 2^(n+fixedCodim σ B) ≤ 2^rank B := by
    rw [pow_add,←ho.1.card_eq_two_pow_rank]
    exact hprod.trans (horder.trans_eq hcard.symm)
  have hlow : n + fixedCodim σ B ≤ rank B :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpower
  have hupper := replacement_secondary_fixed_codimension h d path hb hat hzt hlarge κ σ c
  change fixedCodim σ B ≤ 2*n at hupper
  have hsection := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central B
  have hspace := fixedCodim_subrepresentation_le σ s.space B
  change fixedCodim s.action B + _ ≤ _ at hsection
  have hr : rank B = 3*n := by omega
  have hc : fixedCodim σ B = 2*n := by omega
  have hs : fixedCodim s.action B = 2*n := by omega
  have hright : (Q d.radical a).relIndex A' = (2^n)^3 := by
    rw [←hcard,ho.1.card_eq_two_pow_rank,hr,←pow_mul,Nat.mul_comm n 3]
  have hleft : (Q d.radical z).relIndex A = (2^n)^3 := by
    apply le_antisymm (horder.trans_eq hright)
    have he : 2^n * 2^fixedCodim σ B = (2^n)^3 := by
      rw [hc,←pow_add,←pow_mul]
      congr 1
      omega
    exact he ▸ hprod
  exact ⟨hleft,hright,hc,hs⟩


/-- The sharp order holds for both original endpoints, without an ordering
hypothesis or a choice of natural coordinates. -/
theorem replacement_paired_secondary_orders
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    (Q d.radical z).relIndex A = (2^n)^3 ∧
      (Q d.radical a).relIndex A' = (2^n)^3 := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  rcases le_total ((Q d.radical z).relIndex A) ((Q d.radical a).relIndex A') with ho | ho
  · let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    obtain ⟨κ,_,hk,hL,σ,c,_⟩ :=
      replacement_secondary_quotient_action h d path hb hat hzt hlarge
    have hh := replacement_secondary_sharp_of_index_le h d path hb hat hzt hlarge
      ho κ hk hL σ c
    exact ⟨hh.1,hh.2.1⟩
  · let rev := reverse_secondary_path h d path hb
    have hl := opposite_nonfrattini d path hlarge
    let := replacement_secondary_quotient_normal h d rev hb hzt hat hl
    let := replacement_secondary_quotient_elementary h d rev hb hzt hat hl
    obtain ⟨κ,_,hk,hL,σ,c,_⟩ :=
      replacement_secondary_quotient_action h d rev hb hzt hat hl
    have hh := replacement_secondary_sharp_of_index_le h d rev hb hzt hat hl
      ho κ hk hL σ c
    exact ⟨hh.2.1,hh.1⟩

/-- The full secondary quotient and its natural moved section have the same
sharp opposite fixed codimension at either critical endpoint. -/
theorem replacement_secondary_sharp_codimensions
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup))
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
      replacementComponent d)
    (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup) V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
    let := replacementComponent_normal h d
    fixedCodim σ B = 2*n ∧
      fixedCodim (MovedSection.ofNormal σ (replacementComponent d)).action B = 2*n := by
  have hh := replacement_paired_secondary_orders h d path hb hat hzt hlarge
  exact (replacement_secondary_sharp_of_index_le h d path hb hat hzt hlarge
    (by rw [hh.1,hh.2]) κ hk hL σ c).2.2

/-- Equality of the two fixed codimensions retains every kernel lift. The
moved space supplements the whole fixed space, and its fixed space is exactly
the inverse image of the natural fixed space through the original projection. -/
theorem replacement_secondary_fixed_lifting
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup))
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
      replacementComponent d)
    (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup) V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
    let := replacementComponent_normal h d
    let s := MovedSection.ofNormal σ (replacementComponent d)
    s.space.toSubmodule ⊔ fixedSpace σ B = ⊤ ∧
      fixedSpace s.space.toRepresentation B =
        (fixedSpace s.action B).comap s.central.toSubmodule.mkQ := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
  let := replacementComponent_normal h d
  let s := MovedSection.ofNormal σ (replacementComponent d)
  let : Finite (stabilizer d.radical a) := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite V := Finite.of_surjective (fun u : A => (c.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨hc,hs⟩ := replacement_secondary_sharp_codimensions h d path hb hat hzt hlarge κ hk hL σ c
  change fixedCodim σ B = 2*n at hc
  change fixedCodim s.action B = 2*n at hs
  have hq := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central B
  have hu := fixedCodim_subrepresentation_le σ s.space B
  change fixedCodim s.action B + _ ≤ _ at hq
  have he : fixedCodim s.space.toRepresentation B = fixedCodim σ B := by omega
  refine ⟨(fixedCodim_subrepresentation_eq_iff σ s.space B).mp he,?_⟩
  exact fixedSpace_eq_comap_of_fixedCodim_eq s.space.toRepresentation s.action
    s.central.toSubmodule.mkQ s.central.toSubmodule.mkQ_surjective
    (fun _ _ => rfl) B (he.trans (hc.trans hs.symm))

omit h in
private theorem index_with_normal_factor {G : Type*} [Group G]
    (A P Z : Subgroup G) (hZA : Z ≤ A) (hAP : A ≤ normalizer P) :
    P.relIndex Z * ((A ⊓ P) ⊔ Z).relIndex A = P.relIndex A := by
  let I := P.subgroupOf A
  let W := Z.subgroupOf A
  let : I.Normal := normal_subgroupOf_of_le_normalizer hAP
  have he : ((A ⊓ P) ⊔ Z).subgroupOf A = I ⊔ W := by
    rw [subgroupOf_sup (show A ⊓ P ≤ A from inf_le_left) hZA]
    exact congrArg (fun B : Subgroup A => B ⊔ W) (inf_subgroupOf_left P A)
  change _ * (((A ⊓ P) ⊔ Z).subgroupOf A).index = I.index
  rw [he]
  have hi : I.relIndex W = P.relIndex Z := relIndex_subgroupOf hZA
  rw [←hi,←relIndex_sup_left W I]
  exact relIndex_mul_index le_sup_left


/-- The opposite quotient centralizer consists exactly of the full kernel
intersection times Z. The equality retains all fixed attachments. -/
theorem replacement_paired_centralizer_eq
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    commutatorPreimage A A' (Z d.radical a) = (A ⊓ Q d.radical z) ⊔ Z d.radical a := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let D := (A ⊓ Q d.radical z) ⊔ Z d.radical a
  let C := commutatorPreimage A A' (Z d.radical a)
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  obtain ⟨κ,_,hk,hL,σ,c,_⟩ :=
    replacement_secondary_quotient_action h d path hb hat hzt hlarge
  let : Finite (stabilizer d.radical a) := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  have hAZ : Z d.radical a ≤ A :=
    secondary_orbit_contains_Z g (by omega) path.start_color path.end_color hat hzt
  have hAQ := (replacement_secondary_orbit_bounds h d path hb hat hzt hlarge).1
  have hn : A ≤ normalizer (Q d.radical z) :=
    (hAQ.trans (Q_le_stabilizer_of_dist_two d.radical a z path.start_color
      (path.critical.1.trans ((g.distance_constant a path.start_color).trans hb)))).trans
      (Q_normalized d.radical z)
  obtain ⟨_,_,hq,_,_,_⟩ := replacement_nonfrattini_root_actions h d path hb hlarge
  have hi : 2^n * D.relIndex A = (Q d.radical z).relIndex A := by
    rw [←hq]
    exact index_with_normal_factor A (Q d.radical z) (Z d.radical a) hAZ hn
  have hc := replacement_secondary_fixed_index h d path hb hat hzt hlarge κ σ c
  have hcod := (replacement_secondary_sharp_codimensions h d path hb hat hzt hlarge κ hk hL σ c).1
  dsimp only at hc
  rw [hcod] at hc
  have ho := (replacement_paired_secondary_orders h d path hb hat hzt hlarge).1
  change C.relIndex A = 2^(2*n) at hc
  change _ = (2^n)^3 at ho
  have hd : D.relIndex A = C.relIndex A := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2^n by positivity)
    rw [hi,ho,hc,←pow_add,←pow_mul]
    congr 1
    omega
  have hDC : D ≤ C := replacement_paired_centralizer_contains h d path hb hat hzt hlarge
  have hCA : C ≤ A := commutatorPreimage_le _ _ _
  have hm := relIndex_mul_relIndex D C A hDC hCA
  rw [hd] at hm
  have hindex : D.relIndex C = 1 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < C.relIndex A by rw [hc]; positivity)
    simpa only [one_mul] using hm
  exact le_antisymm (relIndex_eq_one.mp hindex) hDC


/-- Both critical endpoints, rather than only an endpoint selected by an
index comparison, have the original-degree natural moved section. -/
theorem replacement_secondary_natural_section
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    HasSecondaryNaturalSection h d path hb hat hzt hlarge := by
  have ho := replacement_paired_secondary_orders h d path hb hat hzt hlarge
  exact replacement_secondary_natural_section_of_index_le h d path hb hat hzt hlarge
    (by rw [ho.1,ho.2])

/-- The literal secondary quotient has the sharp natural section and the
full fixed-space lifting conclusion, with all actor and coordinate premises
constructed from the original replacement. -/
theorem replacement_secondary_sharp_section
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    let := replacementComponent_normal h d
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        (∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u)) ∧
        let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
        let s := MovedSection.ofNormal σ (replacementComponent d)
        NaturalMovedSectionAtDegree σ (replacementComponent d) n ∧
        IsQuadratic σ B ∧ fixedCodim σ B = 2*n ∧
        s.space.toSubmodule ⊔ fixedSpace σ B = ⊤ ∧
        fixedSpace s.space.toRepresentation B =
          (fixedSpace s.action B).comap s.central.toSubmodule.mkQ := by
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  let := replacementComponent_normal h d
  obtain ⟨κ,hκ,hk,hL,σ,c,hc,hquad,_,hnat⟩ :=
    replacement_secondary_natural_section h d path hb hat hzt hlarge
  obtain ⟨hfull,hlift⟩ := replacement_secondary_fixed_lifting h d path hb hat hzt hlarge κ hk hL σ c
  exact ⟨κ,hκ,hk,hL,σ,c,hc,hnat,hquad,
    (replacement_secondary_sharp_codimensions h d path hb hat hzt hlarge κ hk hL σ c).1,
    hfull,hlift⟩

/-- The whole secondary orbit is generated by its component commutator and
the literal opposite-kernel intersection times Z. No fixed attachment is lost. -/
theorem replacement_secondary_moved_kernel_supplement
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    A = ⁅A,Ltilde d.radical a⁆ ⊔ ((A ⊓ Q d.radical z) ⊔ Z d.radical a) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let D := (A ⊓ Q d.radical z) ⊔ Z d.radical a
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  let := replacementComponent_normal h d
  obtain ⟨κ,_,hk,hL,σ,c,_⟩ :=
    replacement_secondary_quotient_action h d path hb hat hzt hlarge
  let s := MovedSection.ofNormal σ (replacementComponent d)
  let B := (A'.subgroupOf (stabilizer d.radical a)).map κ
  have hfull := (replacement_secondary_fixed_lifting h d path hb hat hzt hlarge κ hk hL σ c).1
  change s.space.toSubmodule ⊔ fixedSpace σ B = ⊤ at hfull
  let rev := reverse_secondary_path h d path hb
  have hl := opposite_nonfrattini d path hlarge
  have hA'Q := (replacement_secondary_orbit_bounds h d rev hb hzt hat hl).1
  have hA'S : A' ≤ stabilizer d.radical a := hA'Q.trans
    (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by
      rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color]
      exact hb))
  have hDA : D ≤ A := sup_le inf_le_left c.kernel_le
  have hCA : ⁅A,Ltilde d.radical a⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans c.normalized)
  have him : c.imageSpace A = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    exact (c.mem_imageSpace_iff A v).mpr ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hmov : c.imageSpace ⁅A,Ltilde d.radical a⁆ = s.space.toSubmodule := by
    rw [commutator_comm,c.imageSpace_commutator _ _ (Ltilde_le_stabilizer a) le_rfl,
      him,subspaceCommutator_comp_map,hL]
    exact s.space_eq.symm
  have hfix : c.imageSpace D = fixedSpace σ B := by
    change c.imageSpace ((A ⊓ Q d.radical z) ⊔ Z d.radical a) = _
    rw [←replacement_paired_centralizer_eq h d path hb hat hzt hlarge]
    rw [c.fixed_image_eq A' hA'S (c.section_le.trans (Z_normalized d.radical a))]
    exact fixedSpace_comp_map σ κ (A'.subgroupOf (stabilizer d.radical a))
  let E := ⁅A,Ltilde d.radical a⁆ ⊔ D
  have hEA : E ≤ A := sup_le hCA hDA
  have hZE : Z d.radical a ≤ E := le_sup_right.trans le_sup_right
  have htop : c.imageSpace E = ⊤ := by
    apply top_unique
    rw [←hfull]
    exact sup_le (hmov ▸ c.imageSpace_mono (show ⁅A,Ltilde d.radical a⁆ ≤ E from le_sup_left))
      (hfix ▸ c.imageSpace_mono (show D ≤ E from le_sup_right))
  apply le_antisymm ?_ hEA
  intro u hu
  have hv : (c.coordinates ⟨u,hu⟩).toAdd ∈ c.imageSpace E := by rw [htop]; trivial
  have he := (c.coordinates_mem_imageSpace_iff E hEA ⟨u,hu⟩).mp hv
  rwa [sup_of_le_left hZE] at he

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
