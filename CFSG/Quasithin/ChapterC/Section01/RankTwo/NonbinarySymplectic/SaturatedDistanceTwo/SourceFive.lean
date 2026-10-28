module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.FullRadical
public import Theory.Representation.SymplecticFourOrthogonalCover.RootValues

/-!
# The full-core comparison in the source equal-attachment argument

The original symplectic cover has fixed-vector lifting for every element
of the endpoint stabilizer: write that element in LQ, and use that Q
centralizes U. Its faithful natural quotient also detects the entire core
as the stabilizer's centralizer of U.

Suppose two neighbors of the same radical have equal moved fixed kernels,
equal Z-displacements under that radical, and the second Z-layer lies in
the first core. Their mixed core/moving commutator then lies in both the
first moving group and its Frattini subgroup. Equality of the fixed kernels
puts it in the second fixed kernel. Fixed-vector lifting kills each
commutator, so faithfulness and equal core orders identify the two full
cores and their central omega layers.

This proves the core-comparison step of MS93 (3.7)(5), printed p.875.
The three antecedents are precisely those used there; their construction
in (6), and the remaining equality of the Z-layers in (5), are not asserted.
The argument applies at the original field degree and requires no order-q
hypothesis on the replacement radical.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Any individual moving displacement fixed by the component is trivial,
for the whole endpoint stabilizer and with the complete cover kernel. -/
theorem stabilizer_value_in_fixed_eq_one
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (c : EdgeMarking h d a t)
    (b : FreeAmalgam d.radical) (hbS : b ∈ stabilizer d.radical a)
    (u : FreeAmalgam d.radical) (hu : u ∈ U d.radical a)
    (hfix : ⁅b,u⁆ ∈ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅b,u⁆ = 1 := by
  let := replacementComponent_normal h d
  obtain ⟨v⟩ := replacement_initial_cover_at_vertex h d ha
  have hbprod : b ∈ Ltilde d.radical a ⊔ Q d.radical a :=
    c.residual_sup_core g hb ▸ hbS
  have hn : Ltilde d.radical a ≤ normalizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    (Ltilde_le_stabilizer _).trans (Q_normalized _ _)
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hn] at hbprod
  obtain ⟨l,hl,q,hq,rfl⟩ := hbprod
  have hqu : Commute q u :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha)
      (U_le_Z a hu) q hq)
  have heq : ⁅l*q,u⁆ = ⁅l,u⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hqu]
    simp only [mul_one,mul_inv_cancel,one_mul]
  rw [heq] at hfix ⊢
  have hk : (MovedSection.coverProjection (replacementMovedSection h d) v.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map v.embedding =
      U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨v.range_eq ▸ ⟨w,rfl⟩,(v.kernel w.toAdd).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := v.range_eq.symm ▸ hx
      exact ⟨w,(v.kernel w.toAdd).mpr hc,rfl⟩
  apply embedded_cover_value_in_kernel_eq_one (U d.radical a) (Ltilde d.radical a)
    (MovedSection.coverProjection (replacementMovedSection h d) v.equiv) v.cover
    v.embedding v.injective v.range_eq v.actor v.conjugation l hl u hu
  rw [hk]
  exact ⟨le_normalizer_iff_commutator_le_right.mp
    ((Ltilde_le_stabilizer _).trans (U_normalized a)) (commutator_mem_commutator hl hu),hfix⟩

/-- Centralizing the actual moving group detects the entire endpoint core. -/
theorem stabilizer_centralizer_moving_eq_core
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    stabilizer d.radical a ⊓ centralizer (U d.radical a : Set (FreeAmalgam d.radical)) =
      Q d.radical a := by
  let := replacementComponent_normal h d
  obtain ⟨v⟩ := replacement_ambient_initial_cover_at_vertex h d ha
  apply le_antisymm
  · rintro b ⟨hb,hc⟩
    have hact (w : (replacementMovedSection h d).space.toSubmodule) :
        (replacementMovedSection h d).space.toRepresentation (v.quotient ⟨b,hb⟩) w = w := by
      apply Multiplicative.ofAdd.injective
      apply v.injective
      rw [v.conjugation]
      have hw : v.embedding (Multiplicative.ofAdd w) ∈ U d.radical a :=
        v.range_eq ▸ (show v.embedding (Multiplicative.ofAdd w) ∈ v.embedding.range from
          ⟨Multiplicative.ofAdd w,rfl⟩)
      have he := hc _ hw
      rw [←he,mul_inv_cancel_right]
    have hnat : MovedSection.ambientAction (replacementMovedSection h d) v.equiv
        (v.quotient ⟨b,hb⟩) = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨w,rfl⟩ := v.cover.1 w
      exact (v.projection ⟨b,hb⟩ w).symm.trans
        (congrArg (MovedSection.coverProjection (replacementMovedSection h d) v.equiv) (hact w))
    have hv : v.quotient ⟨b,hb⟩ = 1 := v.faithful (hnat.trans (map_one _).symm)
    exact v.kernel_Q ▸ (show b ∈ v.quotient.ker.map (stabilizer d.radical a).subtype from
      ⟨⟨b,hb⟩,hv,rfl⟩)
  · exact le_inf (fun _ hx => hx.1) (le_centralizer_iff.mp
      ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))))

/-- The complete radical moves Z into U, using the literal LQ factorization. -/
theorem full_radical_Z_displacement_le_moving
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (c : EdgeMarking h d a t) :
    ⁅Z d.radical a,Q d.radical t⁆ ≤ U d.radical a := by
  rw [commutator_comm]
  apply (commutator_mono c.edge_le le_rfl).trans
  rw [←c.residual_sup_core g hb]
  apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
    (Ltilde d.radical a) (Q d.radical a) (Z d.radical a) (U d.radical a)
    (U_normalized a) (Ltilde_le_stabilizer _) (fun _ hx => hx.1)
  · rw [commutator_comm]
    exact le_rfl
  · rw [commutator_comm,Z_centralizes_Q d.radical a ha]
    exact bot_le

/-- The full-core part of MS93 (3.7)(5), with exactly its equal-attachment,
equal-displacement and contained-Z hypotheses. All intersections and
commutators are in the original free amalgam. -/
theorem source_five_core_equality
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    {a z t : Vertex d.radical}
    (ha : color d.radical a = false) (hz : color d.radical z = false)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hfixed : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (hmove : ⁅Z d.radical z,Q d.radical t⁆ = ⁅Z d.radical a,Q d.radical t⁆)
    (hinside : Z d.radical z ≤ Q d.radical a) :
    Q d.radical a = Q d.radical z ∧ X d.radical a = X d.radical z := by
  let := finite_stabilizer d.radical a
  let := finite_stabilizer d.radical z
  let : Finite (Q d.radical a) := Finite.of_injective
    (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q d.radical a)) := ⟨Q_isPGroup d.radical
    (replacement_isPGroup h d) (replacement_core_le h d) a ha⟩
  have hder : ⁅Q d.radical a,Q d.radical a⁆ ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype := by
    have hh := map_mono (f := (Q d.radical a).subtype)
      (commutator_le_frattini_of_isPGroup (R := Q d.radical a) (p := 2))
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  have hbound : ⁅Q d.radical a,U d.radical z⁆ ≤
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
    rw [←hfixed]
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono (U_le_Z z) c.core_le_edge).trans
        (hmove.le.trans (full_radical_Z_displacement_le_moving h d g (by omega) ha c))
    · exact ((commutator_mono le_rfl ((U_le_Z z).trans hinside)).trans hder).trans
        ((frattini_le_fixedCore h d g hb ha).trans inf_le_right)
  have hcentral : Q d.radical a ≤ centralizer (U d.radical z : Set (FreeAmalgam d.radical)) := by
    intro b hbq u hu
    exact (commutatorElement_eq_one_iff_commute.mp
      (stabilizer_value_in_fixed_eq_one h d g (by omega) hz c' b
        (c'.edge_le (c.core_le_edge hbq)) u hu
        (hbound (commutator_mem_commutator hbq hu)).2)).eq.symm
  have hle : Q d.radical a ≤ Q d.radical z := by
    rw [←stabilizer_centralizer_moving_eq_core h d hz]
    exact le_inf (c.core_le_edge.trans c'.edge_le) hcentral
  have hcard : Nat.card (Q d.radical z) = Nat.card (Q d.radical a) := by
    rw [←c.core_eq,←c'.core_eq,card_map_of_injective c.injective,
      card_map_of_injective c'.injective]
  let : Finite (Q d.radical z) := Finite.of_injective
    (inclusion (show Q d.radical z ≤ stabilizer d.radical z from fun _ hx => hx.1))
    (inclusion_injective _)
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
  exact ⟨heq,congrArg omegaCenter heq⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
