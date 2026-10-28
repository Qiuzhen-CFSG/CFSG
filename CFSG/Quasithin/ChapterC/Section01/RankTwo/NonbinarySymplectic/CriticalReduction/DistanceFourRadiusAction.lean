module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanFixedFree
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanAction

/-!
# The actual full radius action in the retained marking

The literal fixed-radius branch puts [V_a,Q_a] in V_a intersect B_a.
Involution generation then makes the full quotient V_a/(V_a intersect B_a)
elementary abelian. Conjugation descends through the supplied full-kernel
actor map, with coordinates equal to the literal quotient map. Its fixed
space is zero by the full B-preimage criterion.

The actor map is retained exactly; no action, natural-module structure or
identification with a selected span is assumed. This supplies the full
radius section for the dual-cover step of MS93 (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

variable {H F : Type*} [Group H] [Finite H] [Field F]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full radius quotient has its actual descended action and literal
coordinates through the same supplied marking, with no fixed vectors. -/
theorem Input.replacement_radius_action_of_radius_fixed
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a = false)
    {J : Type*} [Group J] (f : stabilizer d.radical a →* J)
    (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    let W := V d.radical a
    let D := W ⊓ B d.radical a (geometry.Z_normal a)
    ∃ hD : (D.subgroupOf W).Normal,
      letI := hD
      ∃ hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W),
        letI := hEA
        ∃ σ : Representation (ZMod 2) J (Additive (W ⧸ D.subgroupOf W)),
          ∃ c : BinaryConjugationSection (stabilizer d.radical a) W D (σ.comp f),
            (∀ w : W, (c.coordinates w).toAdd =
              Additive.ofMul (QuotientGroup.mk' (D.subgroupOf W) w)) ∧
            fixedSpace σ ⊤ = ⊥ := by
  let W := V d.radical a
  let S := stabilizer d.radical a
  let B₀ := B d.radical a (geometry.Z_normal a)
  let D := W ⊓ B₀
  have hWQ : W ≤ Q d.radical a := geometry.V_le_Q hb a ha
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hWS := hWQ.trans hQS
  have hSW : S ≤ normalizer (W : Set (FreeAmalgam d.radical)) :=
    DistanceEight.V_normalized d.radical a
  have hSB : S ≤ normalizer (B₀ : Set (FreeAmalgam d.radical)) :=
    Escape.Propagation.Rigidity.B_normalized hb a ha
  have hSD : S ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (le_inf hSW hSB).trans inf_normalizer_le_normalizer_inf
  let hD : (D.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer (hWS.trans hSD)
  let := hD
  have hkill : ⁅W,Q d.radical a⁆ ≤ D := by
    apply le_inf (le_normalizer_iff_commutator_le_left.mp (hQS.trans hSW))
    intro x hx
    have hxc := (hfixed hx).2
    apply (mem_B_iff d.radical a (geometry.Z_normal a) hWS x).mpr
    refine ⟨le_normalizer_iff_commutator_le_left.mp (hQS.trans hSW) hx,?_⟩
    intro l hl
    have hc : ⁅l,x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hxc l hl)
    rw [hc]
    exact one_mem _
  let hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W) :=
    elementary_quotient_of_omega W D ((commutator_mono le_rfl hWQ).trans hkill)
      (DistanceEight.VBall_omegaOne d.radical a 2)
  let := hEA
  obtain ⟨σ,c,hcoord⟩ := BinaryConjugationSection.exists_descended_actor
    S W D hWS inf_le_left hSW hSD f hf (by
      intro s hs w hw
      have hsQ : (s : FreeAmalgam d.radical) ∈ Q d.radical a :=
        hfQ ▸ mem_map_of_mem S.subtype (show s ∈ f.ker from hs)
      rw [commutator_comm] at hkill
      exact hkill (commutator_mem_commutator hsQ hw))
  exact ⟨hD,hEA,σ,c,hcoord,
    h.replacement_radius_section_fixedSpace_eq_bot d geometry hb ha W le_rfl f σ c⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
