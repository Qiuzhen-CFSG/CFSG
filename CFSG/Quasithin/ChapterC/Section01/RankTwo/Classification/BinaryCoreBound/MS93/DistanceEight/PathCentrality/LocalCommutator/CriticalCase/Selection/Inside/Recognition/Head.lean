module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Conjugates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Local
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Recognition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Lift

/-!
# The literal local-span head for the inside-B recognition

Put H = <Z_a^{G_c}> inside G_c and J = Z_c[H,Q_c]. Conjugation on H/J
factors through the actual surjective projection G_c → SL₃(2), whose
kernel is Q_c. The head is a finite elementary binary group. The small
escaping-commutator bound passes to its literal image in this head.

A fixed/moving splitting of this action lifts to all the clauses of
NaturalSectionAt, including the kernel and equivariant coordinates. These
constructions leave faithfulness and recognition from escaping conjugates
explicit; they do not assert MS93 (1.6).

Source: Meierfrankenfeld--Stellmacher (1993), (1.6), pp.845–847, and its
application in (4.4.1)(2), p.891; the c-notation is defined on p.881.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] {R : Subgroup M}

noncomputable abbrev localSpan (a c : Vertex R) :=
  (localZSpan R a c).subgroupOf (stabilizer R c)

instance localSpan_normal (a c : Vertex R) : (localSpan a c).Normal :=
  localZSpan_normal R a c

noncomputable abbrev spanRadical (a c : Vertex R) :=
  Escape.radicalPreimage (localKernel c) (localSpan a c) (Escape.Initial.Natural.Splitting.localZ c)

theorem spanRadical_normal (geometry : Geometry R) (a c : Vertex R) :
    (spanRadical a c).Normal := by
  let := geometry.Z_normal c
  exact radical_normal _ _ _

/-- The full orbit span modulo its literal Q_c radical and Z_c. -/
def SpanHead (_geometry : Geometry R) (a c : Vertex R) : Type _ :=
  localSpan a c ⧸ (spanRadical a c).subgroupOf (localSpan a c)

noncomputable instance spanHead_group (geometry : Geometry R) (a c : Vertex R) :
    Group (SpanHead geometry a c) := by
  let := spanRadical_normal geometry a c
  unfold SpanHead
  infer_instance

noncomputable def spanHeadProjection (geometry : Geometry R) (a c : Vertex R) :
    localSpan a c →* SpanHead geometry a c := by
  let := spanRadical_normal geometry a c
  exact QuotientGroup.mk' _

theorem spanHeadProjection_surjective (geometry : Geometry R) (a c : Vertex R) :
    Function.Surjective (spanHeadProjection geometry a c) := by
  let := spanRadical_normal geometry a c
  exact QuotientGroup.mk'_surjective _

theorem spanHeadProjection_kernel (geometry : Geometry R) (a c : Vertex R) :
    (spanHeadProjection geometry a c).ker = (spanRadical a c).subgroupOf (localSpan a c) := by
  let := spanRadical_normal geometry a c
  exact QuotientGroup.ker_mk' _

variable [Finite M] {L : Subgroup M}

instance spanHead_finite (geometry : Geometry R) (a c : Vertex R) :
    Finite (SpanHead geometry a c) := by
  let := finite_stabilizer R c
  unfold SpanHead
  infer_instance

/-- The quotient marking is the genuine local projection, not a family tag. -/
noncomputable def spanHeadAction (source : LocalSource L R) (geometry : Geometry R)
    (a c : Vertex R) (hc : color R c = false) : SL →* MulAut (SpanHead geometry a c) := by
  let := geometry.Z_normal c
  exact headAction (localSpan a c) (Escape.Initial.Natural.Splitting.localZ c) (localKernel c)
    (localProjection source c hc) (localProjection_surjective source c hc)
    (localProjection_kernel source c hc)

theorem spanHeadAction_apply (source : LocalSource L R) (geometry : Geometry R)
    (a c : Vertex R) (hc : color R c = false)
    (g : stabilizer R c) (v : localSpan a c) :
    spanHeadAction source geometry a c hc (localProjection source c hc g)
      (spanHeadProjection geometry a c v) =
      spanHeadProjection geometry a c
        ⟨g * (v : stabilizer R c) * g⁻¹,
          (inferInstance : (localSpan a c).Normal).conj_mem v v.property g⟩ := by
  let := geometry.Z_normal c
  exact headAction_apply (localSpan a c) (Escape.Initial.Natural.Splitting.localZ c) (localKernel c)
    (localProjection source c hc) (localProjection_surjective source c hc)
    (localProjection_kernel source c hc) g v

omit [Finite M] in
theorem localSpan_elementary (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) : IsElementaryAbelian 2 (localSpan a c) := by
  let := localZSpan_elementary R hc hd hb
  exact IsElementaryAbelian.subgroupOf
    ((localZSpan_le_Q R hc hd (by omega)).trans (fun _ hx => hx.1))

omit [Finite M] in
theorem spanHead_elementary (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) : IsElementaryAbelian 2 (SpanHead geometry a c) := by
  let := localSpan_elementary geometry hb hc hd
  exact IsElementaryAbelian.of_surjective (spanHeadProjection geometry a c)
    (spanHeadProjection_surjective geometry a c)

/-- Images retain both subgroup inclusions into the actual vertex group. -/
noncomputable def spanHeadImage (geometry : Geometry R) (a c : Vertex R)
    (W : Subgroup (FreeAmalgam R)) : Subgroup (SpanHead geometry a c) :=
  ((W.subgroupOf (stabilizer R c)).subgroupOf (localSpan a c)).map
    (spanHeadProjection geometry a c)

theorem spanHeadImage_card (geometry : Geometry R)
    {a c : Vertex R} (W : Subgroup (FreeAmalgam R))
    (hW : W ≤ localZSpan R a c) :
    Nat.card (spanHeadImage geometry a c W) =
      (spanRadical a c).relIndex (W.subgroupOf (stabilizer R c)) := by
  let := finite_stabilizer R c
  rw [spanHeadImage, ← relIndex_ker, spanHeadProjection_kernel,
    relIndex_subgroupOf (show W.subgroupOf (stabilizer R c) ≤ localSpan a c from
      fun _ hx => hW hx)]

/-- Enlarging the denominator only decreases the literal displacement image. -/
theorem spanHeadImage_card_le (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) (W : Subgroup (FreeAmalgam R))
    (hW : W ≤ localZSpan R a c) :
    Nat.card (spanHeadImage geometry a c W) ≤ (Z R c).relIndex W := by
  let := finite_stabilizer R c
  rw [spanHeadImage_card geometry W hW]
  have hi := relIndex_map_map_of_injective (Escape.Initial.Natural.Splitting.localZ c)
    (W.subgroupOf (stabilizer R c)) (stabilizer R c).subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R c),
    map_subgroupOf_eq_of_le
      (hW.trans ((localZSpan_le_Q R hc hd hb).trans (fun _ hx => hx.1)))] at hi
  rw [hi]
  exact relIndex_le_of_le_left (show Escape.Initial.Natural.Splitting.localZ c ≤ spanRadical a c from le_sup_left)
    (by exact index_ne_zero_of_finite)

/-- The assumed bound on the escaping span is realized on the actual head. -/
theorem escaping_displacement_image_card_le_two (geometry : Geometry R)
    (hb : 4 < geometry.b R) {a c e : Vertex R}
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (p : CriticalPath R geometry c e) (x : stabilizer R c)
    (hsmall : (Z R c).relIndex ⁅escapingSpan a c e x, Z R e⁆ ≤ 2) :
    Nat.card (spanHeadImage geometry a c ⁅escapingSpan a c e x, Z R e⁆) ≤ 2 := by
  apply (spanHeadImage_card_le geometry (by omega) hc hd.le _ ?_).trans hsmall
  exact (commutator_mono (escapingSpan_le_localZSpan a c e x) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (localZSpan_normalized R a c)))

omit [Finite M] in
/-- Transport the source triple bound into the finite local group. -/
theorem span_local_triple (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c) :
    ⁅⁅localSpan a c, localKernel c⁆, pResidual 2 (stabilizer R c)⁆ ≤ Escape.Initial.Natural.Splitting.localZ c := by
  apply map_le_iff_le_comap.mp
  rw [map_commutator, map_commutator,
    map_subgroupOf_eq_of_le ((localZSpan_le_Q R hc hd hb).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (show Q R c ≤ stabilizer R c from fun _ hx => hx.1)]
  exact htriple

/-- The actual span consumer of the generic quotient-correspondence lift. -/
theorem naturalSectionAt_of_spanHead_splitting (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (s : NaturalActionSplitting (spanHeadAction source geometry a c hc)) :
    Nonempty (Escape.NaturalSectionAt c (localZSpan R a c) (Z R c)) := by
  let := geometry.Z_normal c
  let := localSpan_elementary geometry hb hc hd.le
  have hZ := center_Z_le_span (R := R) hc hd
  obtain ⟨localSection⟩ := singleNaturalSection_of_head_splitting
    (localSpan a c) (Escape.Initial.Natural.Splitting.localZ c) (localKernel c) (pResidual 2 (stabilizer R c))
    (localProjection source c hc) (localProjection_surjective source c hc)
    (localProjection_kernel source c hc) (fun _ hx => hZ hx) inferInstance
    (span_local_triple geometry (by omega) hc hd.le htriple) s
  exact ⟨{
    local_group := (localZSpan_le_Q R hc hd.le (by omega)).trans (fun _ hx => hx.1)
    kernel_le := hZ
    projection := localProjection source c hc
    module_section := localSection }⟩

/-- Full-module displacement recognition and the local lift give every
SingleNaturalSection clause. Obtaining this full-module bound from the
escaping-span bound is the remaining use of MS93 (1.6). -/
theorem hasNaturalSection_of_spanHead_small_involution (source : LocalSource L R)
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a c : Vertex R} (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (htriple : ⁅⁅localZSpan R a c, Q R c⁆, Ltilde R c⁆ ≤ Z R c)
    (hfaithful : Function.Injective (spanHeadAction source geometry a c hc))
    (hsmall : HasSmallInvolution (spanHeadAction source geometry a c hc)) :
    HasNaturalSection R a c := by
  let := spanHead_elementary geometry hb hc hd.le
  obtain ⟨s⟩ := naturalActionSplitting_of_small_involution
    (spanHeadAction source geometry a c hc) hfaithful hsmall
  exact naturalSectionAt_of_spanHead_splitting source geometry hb hc hd htriple s

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inside.Recognition
