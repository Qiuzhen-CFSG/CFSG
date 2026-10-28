module
public import CFSG.Quasithin.Chapter10.SourceA5PointQuasisimple

/-!
# Literal marked core-center obstructions

The quotient of the actual local component by the center of its containing
component still has the given A₅ quotient above its two-core. Its central
kernel lies in the original two-core. The fully moved original elementary
module forces the center of that image's two-core to have at least sixteen
elements, and this lower bound transports along an actual marked isomorphism.

These interfaces connect concrete local-core calculations to the J₄ and Ru
rows in Aschbacher–Smith A.3.14 and source 10.2.9, pp.750–751. They retain the
literal restriction of the containing central quotient.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
variable {G : Type*} [Group G] [Finite G] {L I : Subgroup G}

omit [Finite G] in
private theorem a5_center_le_two_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) : center L ≤ pCore 2 L := by
  intro z hz
  apply (QuotientGroup.eq_one_iff z).mp
  apply e.injective
  rw [e.map_one]
  have hc : e (QuotientGroup.mk' (pCore 2 L) z) ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨l,hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) a
    rw [←hl]
    simpa only [Function.comp_apply,map_mul] using
      congrArg (fun x : L => e (QuotientGroup.mk' (pCore 2 L) x))
        (mem_center_iff.mp hz l)
  rwa [alternatingGroup.center_eq_bot (by simp),mem_bot] at hc

/-- Dividing by the containing center preserves the actual A₅ core quotient. -/
noncomputable def source_a5_containing_center_image_quotient
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I) :
    (((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) ≃*
        alternatingGroup (Fin 5) := by
  let A := L.subgroupOf I
  let q := QuotientGroup.mk' (center I)
  let k : L ≃* A := (subgroupOfEquivOfLe hLI).symm
  let f := (q.subgroupMap A).comp k.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective A).comp k.surjective
  have hk : f.ker ≤ center L := by
    intro l hl
    have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp hl)
    change q (inclusion hLI l) = 1 at hh
    have hc := (QuotientGroup.eq_one_iff (inclusion hLI l)).mp hh
    apply mem_center_iff.mpr
    intro m
    exact Subtype.ext (congrArg I.subtype (mem_center_iff.mp hc (inclusion hLI m)))
  have hp : IsPGroup 2 f.ker := pCore_isPGroup.to_le (hk.trans (a5_center_le_two_core e))
  exact (f.pCoreQuotientEquiv hf hp).symm.trans e

variable {T : Sylow 2 G}
  (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The source center bound transports to an actual marked model image. -/
theorem source_a5_marked_core_center_card {B : Type*} [Group B] [Finite B]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* B) :
    16 ≤ Nat.card (center (pCore 2 B)) := by
  have hlow := (source_a5_containing_center_quotient_restrictions D e hLI).1
  let ef := (f.subgroupMap (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))))).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 f))
  rwa [Nat.card_congr (centerCongr ef).toEquiv] at hlow

include D in
/-- An actual marked core with center of order below sixteen is impossible. -/
theorem source_a5_not_marked_small_core_center {B Q : Type*}
    [Group B] [Finite B] [Group Q] [Finite Q]
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (hLI : L ≤ I)
    (f : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃* B)
    (q : pCore 2 B ≃* Q) (hsmall : Nat.card (center Q) < 16) : False := by
  have hlow := source_a5_marked_core_center_card D e hLI f
  rw [Nat.card_congr (centerCongr q).toEquiv] at hlow
  omega

end CFSG.Quasithin.Chapter10
