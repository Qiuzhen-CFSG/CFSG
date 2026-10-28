module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanAction
public import Theory.Representation.BinaryConjugationSection.SubspacePreimages
public import Theory.Representation.BinaryOffender.InvariantAction

/-!
# No fixed vectors in an actual radius section modulo its full B-intersection

Take the full coordinate preimage N of the fixed space in the given section
W/(W intersect B_a), where W lies in the actual radius. It is normalized by
the full vertex stabilizer, and [N,L_a] lies in B_a. The residual acts
idempotently on this normal two-subgroup. Thus [N,L_a] lies in
[B_a,L_a] <= Z_a, forcing N <= B_a by the definition of the full fixed
preimage B_a. The coordinate fixed space is therefore zero.

The original actor map and coordinates are retained. No surjectivity of the
actor map, fixed-radius branch, offender or natural-module hypothesis is
needed. In particular this removes the extra fixed preimage in the literal
moved section recognized by DistanceFourSpanNatural, without asserting that
the whole section is moved.
Source: the central-extension preparation for MS93 (3.10)(i), pp.879--880,
as used in (5.12)(2), p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every actual radius section modulo its full B-intersection has zero
fixed space under its given marked action. The map and quotient coordinates
are arbitrary retained data; no faithfulness or naturality is assumed. -/
theorem Input.replacement_radius_section_fixedSpace_eq_bot
    (geometry : Geometry d.radical) (hb : 2 < geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (W : Subgroup (FreeAmalgam d.radical)) (hWV : W ≤ V d.radical a)
    {J V₀ : Type*} [Group J] [AddCommGroup V₀] [Module (ZMod 2) V₀]
    (f : stabilizer d.radical a →* J) (σ : Representation (ZMod 2) J V₀)
    (c : BinaryConjugationSection (stabilizer d.radical a) W
      (W ⊓ B d.radical a (geometry.Z_normal a)) (σ.comp f)) :
    fixedSpace σ ⊤=⊥ := by
  let S := stabilizer d.radical a
  let B₀ := B d.radical a (geometry.Z_normal a)
  let ρ := σ.comp f
  let I := fixedSpace ρ ⊤
  let N := c.subspacePreimage I
  have hNW : N ≤ W := c.subspacePreimage_le I
  have hNV : N ≤ V d.radical a := hNW.trans hWV
  have hVQ := geometry.V_le_Q hb a ha
  have hVS : V d.radical a ≤ S := hVQ.trans (fun _ hx => hx.1)
  have hNS : N ≤ S := hNV.trans hVS
  have hSN : S ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    apply c.subspacePreimage_normalized S le_rfl I
    rw [subgroupOf_self]
    exact fixedSpace_stable_of_normal ρ ⊤
  have hNL : ⁅N,Ltilde d.radical a⁆ ≤ B₀ := by
    rw [commutator_comm]
    apply le_trans (c.commutator_le_of_imageSpace_fixed (Ltilde d.radical a) N
      (Ltilde_le_stabilizer a) hNW ?_) inf_le_right
    rw [c.imageSpace_subspacePreimage]
    intro v hv l
    exact hv ⟨l,mem_top _⟩
  let := finite_stabilizer d.radical a
  let A := N.subgroupOf S
  let : A.Normal := normal_subgroupOf_of_le_normalizer hSN
  have hp : IsPGroup 2 A :=
    ((Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d)
      a ha).to_le (hNV.trans hVQ)).comap_subtype
  have hAm : A.map S.subtype=N := map_subgroupOf_eq_of_le hNS
  have hid : ⁅⁅N,Ltilde d.radical a⁆,Ltilde d.radical a⁆=⁅N,Ltilde d.radical a⁆ := by
    have hh := congrArg (Subgroup.map S.subtype)
      (commutator_isPPerfect_idempotent (pResidual 2 S) A (isPPerfect_pResidual 2)
        hp le_normalizer_of_normal)
    simpa only [map_commutator,hAm,Ltilde] using hh
  have hBZ : ⁅B₀,Ltilde d.radical a⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl b hb₀
    exact ((mem_B_iff d.radical a (geometry.Z_normal a) hVS b).mp hb₀).2 l hl
  have hNZ : ⁅N,Ltilde d.radical a⁆ ≤ Z d.radical a :=
    hid.symm.le.trans ((commutator_mono hNL le_rfl).trans hBZ)
  have hNB : N ≤ B₀ := radius_le_B_of_commutator geometry hb ha N hNV hNZ
  have hI : I=⊥ := by
    apply bot_unique
    intro v hv
    have hvN : v ∈ c.imageSpace N := (c.imageSpace_subspacePreimage I).symm ▸ hv
    obtain ⟨w,hw,rfl⟩ := (c.mem_imageSpace_iff N v).mp hvN
    change (c.coordinates w).toAdd=0
    exact (c.coordinates_eq_one_iff w).mpr ⟨w.property,hNB hw⟩
  apply bot_unique
  intro v hv
  have hvI : v ∈ I := by
    intro s
    exact hv ⟨f (s : S),mem_top _⟩
  exact hI ▸ hvI

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
