module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAutomizer

/-!
# Full automizer in the two outer closure alternatives

The central involution and elementary-eight alternatives each contain the
marked odd involution. The actual automizer already contains the full even
hexacode group. Its index-two extension is therefore the full hexacode
group, retaining the same chart and the same coordinate marking.

Source: Aschbacher--Smith12.7.15(2--3), printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem full_range_of_odd {A : Type*} [Group A]
    (f : A →* HexAutomorphisms) (hcontains : hexSign.ker ≤ f.range)
    (g : HexAutomorphisms) (hg : g ∈ f.range) (hodd : hexSign g ≠ 1) :
    f.range = ⊤ := by
  have htwo : hexSign.ker.index = 2 := by
    rw [index_ker,MonoidHom.range_eq_top.mpr hexSign_surjective,card_top]
    simp [Nat.card_eq_fintype_card]
  have hd : f.range.index ∣ 2 := htwo ▸ index_dvd_of_le hcontains
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo'
  · exact index_eq_one.mp hone
  · have hi := relIndex_mul_index hcontains
    rw [htwo,htwo'] at hi
    have hone : hexSign.ker.relIndex f.range = 1 := by omega
    exact (hodd ((relIndex_eq_one.mp hone) hg)).elim

/-- The same original marked alternatives, including the full ambient
module automizer in both outer cases. -/
theorem original_tripleSix_central_closure_automizer_cases
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    let C := centralizer ({(z : G)} : Set G)
    let R := conjugateSpanBy U C
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    let v := (tripleSixPointCoordinates D a z).toAdd
    W ≤ (T : Subgroup G) ∧
    ∃ f : Automizer U →* HexAutomorphisms, Function.Injective f ∧
      (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (inducedAutomizer U K).map f = hexSign.ker ∧
      (∀ (b : Automizer U) (u : U),
        (tripleSixPointCoordinates D a (b.val u)).toAdd =
          Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
      (let N := (inducedAutomizer U W).map f
       N ≤ Hexacode.fullVectorStabilizer v ∧ IsPGroup 2 N ∧ N ≠ ⊥ ∧
       ∃ e : Hexacode.fullVectorStabilizer v ≃* DuadProduct,
         ∃ r : alternatingGroup (Fin 6),
           (∀ g : Hexacode.fullVectorStabilizer v,
             duadProductHom (e g) = r.val * hexCoordinateSixHom g.val * r.val⁻¹) ∧
           (∀ g : Hexacode.fullVectorStabilizer v,
             hexSign g.val = 1 ↔ (e g).1 = signPermTwo (e g).2) ∧
           (let B := (N.subgroupOf (Hexacode.fullVectorStabilizer v)).map e.toMonoidHom
            (B = (⊥ : Subgroup Two).prod core ∨
              (f.range = ⊤ ∧ (B = centralFactor ∨ B = productCore))) ∧
            (IsMulCommutative W → B = (⊥ : Subgroup Two).prod core))) := by
  obtain ⟨hWT,f,hf,hfk,hK,hchart,hN,hp,hne,e,r,he,heven,hcases,hab⟩ :=
    original_tripleSix_central_closure_automizer h structural D a z hz hzT hnot
  refine ⟨hWT,f,hf,hfk,hK,hchart,hN,hp,hne,e,r,he,heven,?_,hab⟩
  rcases hcases with hR | hother
  · exact Or.inl hR
  · refine Or.inr ⟨?_,hother⟩
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    let v := (tripleSixPointCoordinates D a z).toAdd
    let N := (inducedAutomizer U W).map f
    let B := (N.subgroupOf (Hexacode.fullVectorStabilizer v)).map e.toMonoidHom
    have hmem : (Equiv.swap 0 1,1) ∈ B := by
      rcases hother with hc | hc
      · rw [show B = centralFactor from hc]
        exact ⟨mem_top _,one_mem _⟩
      · rw [show B = productCore from hc]
        exact ⟨mem_top _,one_mem _⟩
    obtain ⟨b,hb,hbmark⟩ := hmem
    have hodd : hexSign b.val ≠ 1 := by
      intro hb'
      have hh := (heven b).mp hb'
      rw [show e b = (Equiv.swap 0 1,1) from hbmark] at hh
      exact (by decide : (Equiv.swap 0 1 : Two) ≠ signPermTwo 1) hh
    have hcontains : hexSign.ker ≤ f.range := by
      rw [←hK]
      rintro _ ⟨b,_,rfl⟩
      exact ⟨b,rfl⟩
    obtain ⟨b',_,hb'⟩ := hb
    exact full_range_of_odd f hcontains b.val ⟨b',hb'⟩ hodd

end CFSG.Quasithin.Chapter12.Section07
