module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedIndices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourLargeCoherentPaths
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths

/-!
# The actual full critical kernel join at distance four

The source intersection in MS93 (5.12)(1) is Z_v intersect Q_a: it uses
Q_a at the original start, not the other nearby kernel Q_z. The retained
second path v to a is therefore a critical path for this very intersection.
Its actual first mover normalizes the whole intersection, including its
central attachment. The fixed-radius comparison makes Z_e normalize the
intersection joined with Z_u. Both actors thus normalize the same full join.

The coherent selector producer supplies every path and orbit datum used
here. The original first selectors, second residual selector, and all
literal overlaps remain in the result. No mover equality, own movement
bound, supplied comparison, or individual-generation premise is assumed.
Source: MS93 (5.12)(1) and its normalization step, printed pp.924--926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-- The same two backward paths and selectors, with the full critical
kernel normalized by its actual first mover and the preceding endpoint. -/
@[expose] def distanceFourFullNormalizedPaths {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (c t : Vertex R) (q : ℕ) : Prop :=
  ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
    let c₁ := act R g⁻¹ c
    let t₁ := act R g⁻¹ t
    ∃ u w, (u=c₁ ∧ w=t₁ ∨ u=act R x c₁ ∧ w=act R x t₁) ∧
      Adjacent R a w ∧ Adjacent R u w ∧
      ∃ back : CriticalPath R geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ∃ v s, ∃ y ∈ Ltilde R u,
          act R y a=v ∧ act R y (back.walk.getVert 1)=s ∧
          Adjacent R u s ∧ Adjacent R v s ∧
          ¬ Z R (path.walk.getVert 2) ≤ normalizer
            ((Z R v ⊔ Z R u : Subgroup (FreeAmalgam R)) : Set _) ∧
          Subgroup.SmallMover.join (U R v) (Q R v) (Q R s) (q^2) ⊔
            Z R (path.walk.getVert 2) ≤ normalizer
              (((Z R v ⊓ Q R a) ⊔ Z R u : Subgroup (FreeAmalgam R)) : Set _) ∧
          ∃ next : CriticalPath R geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual first mover and preceding critical endpoint normalize the
full seed-kernel join; the second critical path supplies its precise kernel. -/
theorem Input.replacement_distance_four_fixed_full_kernel_normalized
    {geometry : Geometry d.radical} {a z u v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (next : CriticalPath d.radical geometry v a) (hfirst : next.walk.getVert 1=s) :
    Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ≤
      normalizer (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let W := Z d.radical v ⊓ Q d.radical a
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical s) (Nat.card F^2)
  have hroot := (h.replacement_distance_four_fixed_critical_indices d hb
    path.start_color hfixed next).1
  have hJW : J ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    have hh := unequal_first_mover_normalizes_critical_kernel h d next (by omega) hroot
    simpa only [hfirst] using hh
  have hJS : J ≤ stabilizer d.radical u :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 u (adjacent_symm _ hus))
  have hJn : J ≤ normalizer ((W ⊔ Z d.radical u :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (le_inf hJW (hJS.trans (Z_normalized d.radical u))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact sup_le hJn (h.replacement_distance_four_full_fixed_kernel_normalized d path hb
    back hmid hus hvs y hy hya hfixed)

/-- Fixed radius supplies actual coherent paths with full critical-kernel
normalization, retaining every original selector and overlap. -/
theorem Input.replacement_distance_four_fixed_full_normalized_paths
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ∃ c, Adjacent d.radical c (path.walk.getVert 1) ∧
      distanceFourFullNormalizedPaths path c (path.walk.getVert 1) (Nat.card F) := by
  obtain ⟨c,hc,g,hg,x,hx,u,w,hchoose,haw,huw,back,hfirst,hover,
    v,s,y,hy,hya,hys,hus,hvs,hn,next,hnext,hovernext⟩ :=
    h.replacement_distance_four_coherent_paths d path hb
  have hl := path.length_eq_b
  have hmid : back.walk.getVert 2=a := by
    have hh := hover 0 (by omega)
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hh
  have hnfull := h.replacement_distance_four_fixed_full_kernel_normalized d path hb back
    hmid hus hvs y (Ltilde_le_stabilizer u hy) hya hfixed next hnext
  exact ⟨c,hc,g,hg,x,hx,u,w,hchoose,haw,huw,back,hfirst,hover,
    v,s,y,hy,hya,hys,hus,hvs,hn,hnfull,next,hnext,hovernext⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
