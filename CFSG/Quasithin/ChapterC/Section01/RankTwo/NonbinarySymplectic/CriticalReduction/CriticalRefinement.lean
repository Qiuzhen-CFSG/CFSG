module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IntersectionMovement

public import Theory.SpecificGroups.SymplecticFour.QuadraticRefinementObstruction

/-!
# Refinement-free critical actors on the replacement

The original natural-cover marking supplies an inner critical actor. Below
q², reciprocal comparison identifies a full field-sized root. At order at
least q², the quadratic image contradicts the orthogonal plane bound. Thus
either branch excludes invariant refinements under the same marking.

Source: MS93 (3.3)--(3.4), printed pp.867--869. Both field parameters and the
literal vertex quotient are retained for the dual-star consumer.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.Plane.OrthogonalActors
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every actual inner critical image excludes invariant refinements. The
small branch is a full field root by reciprocal comparison; the large branch
contradicts the orthogonal 2q bound. -/
theorem Input.replacement_critical_actor_no_refinement
    {E W : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [AddCommGroup W] [Module (ZMod 2) W]
    (hEF : Nat.card E = Nat.card F)
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (σ : Representation (ZMod 2) (L (K := E)) W)
    (p : σ.IntertwiningMap (binaryNatural (K := E))) (hp : IsCover p)
    (j : Multiplicative W →* FreeAmalgam d.radical) (hj : Function.Injective j)
    (hjr : j.range = U d.radical z) (β : Z d.radical a →* L (K := E))
    (hβ : ∀ x : Z d.radical a, ∀ w : W,
      j (Multiplicative.ofAdd (σ (β x) w)) =
        (x : FreeAmalgam d.radical) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam d.radical)⁻¹)
    (hcard : Nat.card β.range = (Q d.radical z).relIndex (Z d.radical a)) :
    ¬ ∃ c : Natural (K := E), ∀ b : β.range, ∀ v,
      refinement c (binaryNatural b.val v) = refinement c v := by
  have hF : 2 < Nat.card E := by
    rw [hEF,h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  let A := β.range.map (commutator (Sp E)).subtype
  have hAcard : Nat.card A = Nat.card β.range :=
    (Nat.card_congr (β.range.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector E, x • (y • v-v)=y • v-v := by
    have hh := critical_embedded_natural_actor_quadratic path hb σ p hp j hj hjr β hβ
    rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩ v
    exact hh x hx y hy v
  have hnot : ¬ ∃ c : Vector E, ∀ b : A, ∀ v, refinement c (b.val • v)=refinement c v := by
    by_cases hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2
    · have hi := h.replacement_small_critical_indices_eq_field d path hb hsmall
      have hc : Nat.card β.range = Nat.card E := hcard.trans (hi.1.trans hEF.symm)
      have hCa : C d.radical a = Q d.radical a := MSCentralOrbit.C_eq_Q _
        (h.replacement_two_group d) (h.replacement_core_le d)
        (h.replacement_omegaOrbit_centralizer d) a path.start_color
      have hr := critical_root_coordinates_of_reciprocal_index_field path hb hCa hF
        σ p hp j hj hjr β hβ hc (hi.2.trans hEF.symm)
      exact no_refinement_of_displacement_one hF A (hAcard.trans hc) hr.1 hq
    · exact no_refinement_of_large_quadratic hF A
        (by rw [hAcard,hcard,hEF]; omega) hq
  rintro ⟨c,hc⟩
  apply hnot
  refine ⟨c,?_⟩
  rintro ⟨b,⟨b,hb,rfl⟩⟩ v
  exact hc ⟨b,hb⟩ v

open ChapterB.QuasisimpleSource MSCentralOrbit

/-- The full vertex marking supplies a refinement-free critical actor in the
same symplectic component that marks the original natural cover. -/
theorem Input.replacement_refinement_free_inner_actor
    {E J V : Type*} [Field E] [Finite E] [CharP E 2] [Algebra (ZMod 2) E]
    [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
    (hEF : Nat.card E = Nat.card F)
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0 < geometry.b d.radical)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := E)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam d.radical)
    (hj : Function.Injective j) (hjr : j.range = U d.radical z)
    (κ : stabilizer d.radical z →* J)
    (hkQ : κ.ker.map (stabilizer d.radical z).subtype = Q d.radical z)
    (hconj : ∀ (g : stabilizer d.radical z) (v : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) v)) =
        (g : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(g : FreeAmalgam d.radical)⁻¹) :
    ∃ β : Z d.radical a →* L (K := E),
      (∀ (x : Z d.radical a) (hx : (x : FreeAmalgam d.radical) ∈ stabilizer d.radical z),
        (e.groupEquiv.symm (β x) : J) = κ ⟨x,hx⟩) ∧
      ¬ ∃ c : Natural (K := E), ∀ b : β.range, ∀ v,
        refinement c (binaryNatural b.val v) = refinement c v := by
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAS)
  have hδcard : Nat.card δ.range = (Q d.radical z).relIndex (Z d.radical a) :=
    CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison.quotient_image_card _ _ _ hAS κ hkQ
  have hδ (x : Z d.radical a) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    hconj (inclusion hAS x) v
  have hFl : 2 < Nat.card E := by
    rw [hEF,h.field_card]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hAut : Nat.card (E ≃+* E) < Nat.card δ.range := by
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
      (show Nat.card E = 2^n by rw [hEF,h.field_card]),hδcard]
    have hdeg : n < Nat.card F := by rw [h.field_card]; exact n.lt_two_pow_self
    exact hdeg.trans_le (h.replacement_critical_indices_ge_field d path hb).1
  obtain ⟨β,hβcard,hβmark,hβact⟩ := critical_inner_model_actor_of_ringAut_card_lt
    path hb hFl s e hp hcent j hj hjr δ hδ hAut
  exact ⟨β,fun x hx => hβmark x,
    h.replacement_critical_actor_no_refinement d hEF path hb
      (MovedSection.coverAction s e) (MovedSection.coverProjection s e) hp
      j hj hjr β hβact (hβcard.trans hδcard)⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
