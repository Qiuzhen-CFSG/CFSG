module

public import Theory.Alternating.SevenQuasisimpleExtension
public import Theory.GroupTheory.ExponentFourSylowSections
public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The ambient A₇ and triple-A₇ cases with split Sylow order sixteen

The component order forces a proper ambient extension. The actual
conjugation map then identifies the ambient group with S₇ in the centerless
case. In the cubic case it constructs the normal cubic kernel, symmetric
quotient, derived triple cover, and literal inversion action of every odd
coset. The final application uses the original Goldschmidt intersection as
its Sylow subgroup; the earlier F.6.17 generalized-Fitting identity remains
explicit, as does the component model supplied by the complete sieve.

Source: Aschbacher–Smith F.6.17–18(9), printed pp.309–310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Equiv
open GLS3.Chapter5 GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterF.SourceAssembly
open Theory.AlternatingSevenExtension

variable {G : Type*} [Group G] [Finite G]

/-- An A₇ component beneath a Sylow of order sixteen gives the actual S₇ ambient group. -/
theorem symmetric_seven_of_alternating_component
    (T : Sylow 2 G) (hT : Nat.card T = 16)
    (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hFstar : generalizedFitting G = K) (j : K ≃* alternatingGroup (Fin 7)) :
    Nonempty (G ≃* Perm (Fin 7)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let f : Covering K (alternatingGroup (Fin 7)) := Covering.ofMulEquiv j
  let e : K ⧸ center K ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq f.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)
  have hc : Nat.card (center K) = 1 := by
    rw [Nat.card_congr (centerCongr j).toEquiv,
      alternatingGroup.center_eq_bot (by simp)]
    simp
  have hne := proper_of_sylow_sixteen T hT K (hc ▸ (by decide : Odd 1)) e
  have hk : (action K e).ker = ⊥ := by
    rw [action_ker K hFstar e, (eq_bot_iff_card _).mpr hc, Subgroup.map_bot]
  exact ⟨MulEquiv.ofBijective (action K e)
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hk, action_surjective K hFstar hne e⟩⟩

/-- A triple-A₇ component gives the full hatted symmetric extension data. -/
theorem triple_symmetric_seven_of_triple_component
    (T : Sylow 2 G) (hT : Nat.card T = 16)
    (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hFstar : generalizedFitting G = K) (j : K ≃* TripleSeven) :
    Nonempty (TripleSymmetricExtension G) := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let f : Covering K (alternatingGroup (Fin 7)) :=
    tripleSevenCovering.comp (Covering.ofMulEquiv j)
  let e : K ⧸ center K ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq f.ker_eq_center_of_isSimple.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom f.surjective)
  have hc : Nat.card (center K) = 3 :=
    (Nat.card_congr (centerCongr j).toEquiv).trans tripleSeven_center_card
  have hne := proper_of_sylow_sixteen T hT K (hc ▸ (by decide : Odd 3)) e
  exact ⟨tripleExtension K hFstar hne e hc⟩

/-- The complete ambient extension conclusion in both alternating-seven component cases. -/
theorem alternating_seven_extension_models_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hK : IsComponent G K)
    (hFstar : generalizedFitting G = K)
    (hm : Nonempty (K ≃* alternatingGroup (Fin 7)) ∨ Nonempty (K ≃* TripleSeven)) :
    Nonempty (G ≃* Perm (Fin 7)) ∨ Nonempty (TripleSymmetricExtension G) := by
  let : IsQuasisimple K := hK.2
  have hT : Nat.card T = 16 := (Nat.card_congr eT.toEquiv).trans split_sixteen_card
  rcases hm with hm | hm
  · obtain ⟨j⟩ := hm
    exact .inl (symmetric_seven_of_alternating_component T hT K hFstar j)
  · obtain ⟨j⟩ := hm
    exact .inr (triple_symmetric_seven_of_triple_component T hT K hFstar j)

/-- Literal F.6.18(9) ambient application on the original Goldschmidt intersection.
The complete split-sixteen component sieve supplies the two model branches. -/
theorem source_alternating_seven_extension_models
    {G₁ G₂ : Subgroup G} (h : IsGoldschmidtTriple G₁ G₂)
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (eT : (G₁ ⊓ G₂ : Subgroup G) ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (hm : Nonempty (pResidual 2 G ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (pResidual 2 G ≃* TripleSeven)) :
    Nonempty (G ≃* Perm (Fin 7)) ∨ Nonempty (TripleSymmetricExtension G) := by
  obtain ⟨T, hT⟩ := h.intersection_sylow
  exact alternating_seven_extension_models_of_split_sixteen T
    ((MulEquiv.subgroupCongr hT.symm).trans eT) (pResidual 2 G)
    ⟨(inferInstance : (pResidual 2 G).Normal).isSubnormal, hq⟩ hFstar.symm hm

end CFSG.Quasithin.ChapterF.SourceAssembly
