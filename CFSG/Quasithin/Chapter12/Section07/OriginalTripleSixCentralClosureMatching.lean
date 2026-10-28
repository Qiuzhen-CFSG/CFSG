module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterModel
public import Theory.SpecificGroups.SymmetricSix.MatchingEightMarking

/-!
# A matching quotient for the original outer closure

Apply the proved exceptional automorphism to the original coordinate
relabeling. It sends the actual product core to the displayed matching
eight-group. The resulting quotient of the original full automizer is
surjective, has exactly the cubic scalar kernel, and preserves parity.
The prescribed K action and every original U vector remain in the
unchanged hexacode chart. This is a chosen matching marking; it is not
asserted to be the action on full-weight scalar planes.

Source: the two-conjugate construction following Aschbacher--Smith12.7.18,
printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation MatchingEightGeneration
open BinaryAlternatingSix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The actual outer automizer has a full six-letter quotient in which its
unchanged closure image is precisely the three independent matching swaps. -/
theorem original_tripleSix_central_closure_matching
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    W ≤ (T : Subgroup G) ∧
    ∃ f : Automizer U →* HexAutomorphisms, Function.Bijective f ∧
      (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (inducedAutomizer U K).map f = hexSign.ker ∧
      (∀ (b : Automizer U) (u : U),
        (tripleSixPointCoordinates D a (b.val u)).toAdd =
          Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
      ∃ r : alternatingGroup (Fin 6),
        ∃ q : Automizer U →* Equiv.Perm (Fin 6),
          (∀ b, q b = diagramAut (r.val * hexCoordinateSixHom (f b) * r.val⁻¹)) ∧
          Function.Surjective q ∧ q.ker = (zpowers hexZ).comap f ∧
          (∀ b, (q b).sign = 1 ↔ hexSign (f b) = 1) ∧
          (inducedAutomizer U W).map q = matchingEight ∧
          (inducedAutomizer U K).map q = alternatingGroup (Fin 6) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨hWT, f, hf, hfk, hK, hchart, hfix, e, r, he, _, hprod⟩ :=
    original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter
  let v := (tripleSixPointCoordinates D a z).toAdd
  let N := (inducedAutomizer U W).map f
  let B := N.subgroupOf (Hexacode.fullVectorStabilizer v)
  let c := (MulAut.conj r.val).toMonoidHom.comp hexCoordinateSixHom
  let d := diagramAut.toMonoidHom.comp c
  let q := d.comp f
  have hsurj : Function.Surjective q := diagramAut.surjective.comp
    ((MulAut.conj r.val).surjective.comp (hexCoordinateSix_surjective.comp hf.2))
  have hker : q.ker = (zpowers hexZ).comap f := by
    rw [← hexCoordinateSix_kernel]
    ext b
    change diagramAut ((MulAut.conj r.val) (hexCoordinateSixHom (f b))) = 1 ↔
      hexCoordinateSixHom (f b) = 1
    rw [diagramAut.map_eq_one_iff, (MulAut.conj r.val).map_eq_one_iff]
  have hsign (b : Automizer U) : (q b).sign = 1 ↔ hexSign (f b) = 1 := by
    change (diagramAut (r.val * hexCoordinateSixHom (f b) * r.val⁻¹)).sign = 1 ↔ _
    rw [diagram_sign_eq_one_iff]
    have hr : r.val.sign = 1 := r.property
    simp only [map_mul, map_inv, hr, one_mul, inv_one, mul_one]
    rfl
  have hN : N.map c = productCore.map duadProductHom := by
    have hc : c.comp (Hexacode.fullVectorStabilizer v).subtype =
        duadProductHom.comp e.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      exact (he x).symm
    calc
      N.map c = (B.map (Hexacode.fullVectorStabilizer v).subtype).map c := by
        rw [map_subgroupOf_eq_of_le hfix]
      _ = (B.map e.toMonoidHom).map duadProductHom := by
        rw [map_map, hc, ← map_map]
      _ = productCore.map duadProductHom := by rw [hprod]
  have hW : (inducedAutomizer U W).map q = matchingEight := by
    change (inducedAutomizer U W).map (diagramAut.toMonoidHom.comp (c.comp f)) = _
    rw [← map_map, ← map_map, hN, diagram_productCore_eq_matching]
  have hKq : (inducedAutomizer U K).map q = alternatingGroup (Fin 6) := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      have hh : f b ∈ hexSign.ker := hK ▸ mem_map_of_mem f hb
      exact (hsign b).mpr hh
    · intro p hp
      obtain ⟨b, rfl⟩ := hsurj p
      have hb : f b ∈ (inducedAutomizer U K).map f :=
        hK.symm ▸ (hsign b).mp hp
      obtain ⟨b', hb', heq⟩ := hb
      exact ⟨b, hf.1 heq ▸ hb', rfl⟩
  exact ⟨hWT, f, hf, hfk, hK, hchart, r, q, fun _ => rfl,
    hsurj, hker, hsign, hW, hKq⟩

end CFSG.Quasithin.Chapter12.Section07
