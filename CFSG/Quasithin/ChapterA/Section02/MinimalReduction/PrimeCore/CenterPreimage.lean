module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.TwoCore
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The center preimage in the minimal covering of a semisimple section

For the literal surjection supplied by A.2.8, the preimage of the section's
center lies in the ambient Frattini subgroup. Indeed any supplement maps
onto the perfect section, and minimal covering makes that supplement the
whole group. The Frattini argument then makes each Sylow subgroup of this
preimage normal in the ambient group, so the preimage is nilpotent.

These are the initial reductions of Aschbacher–Smith A.2.11, printed p.35.
The later exclusion of its Sylow subgroups at primes other than the offending
prime still requires the source unitary-exception and rank arguments.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
  [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.center_preimage_le_frattini
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    (center S).comap f ≤ frattini G := by
  let := h.2.2.2.1.isPerfect
  change (center S).comap f ≤ ⨅ U ∈ {L : Subgroup G | IsCoatom L}, U
  refine le_iInf fun U => le_iInf fun hU => ?_
  by_contra hle
  have hsup : U ⊔ (center S).comap f = ⊤ :=
    (hU.not_le_iff_codisjoint.mp hle).eq_top
  have hmap : U.map f ⊔ center S = ⊤ := by
    have hm := congrArg (Subgroup.map f) hsup
    simpa only [Subgroup.map_sup, map_comap_eq, MonoidHom.range_eq_top_of_surjective f hf,
      top_inf_eq, map_top_of_surjective f hf] using hm
  have himage : U.map f = ⊤ := Subgroup.eq_top_of_sup_center_eq_top _ hmap
  have hsur : Function.Surjective (f.comp U.subtype) := by
    rw [← MonoidHom.range_eq_top]
    simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using himage
  exact hU.ne_top (lemma_A_2_8 h ih (IsSectionOf.of_surjective _ hsur))

theorem CounterexampleToTheoremA.center_preimage_sylow_normal
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) (q : ℕ) [Fact q.Prime]
    (Q : Sylow q ((center S).comap f)) :
    ((Q : Subgroup ((center S).comap f)).map ((center S).comap f).subtype).Normal := by
  apply normalizer_eq_top_iff.mp
  apply frattini_nongenerating
  exact top_unique (Q.normalizer_sup_eq_top ▸
    sup_le_sup_left (h.center_preimage_le_frattini ih f hf) _)

theorem CounterexampleToTheoremA.center_preimage_isNilpotent
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    Group.IsNilpotent ((center S).comap f) := by
  apply (Group.isNilpotent_of_finite_tfae.out 0 3).mpr
  intro q _ Q
  exact (h.center_preimage_sylow_normal ih f hf q Q).of_map_subtype

/-- Every Sylow subgroup of the center preimage lies in the corresponding
ambient prime core, through the original subgroup map. -/
theorem CounterexampleToTheoremA.center_preimage_sylow_le_pCore
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) (q : ℕ) [Fact q.Prime]
    (Q : Sylow q ((center S).comap f)) :
    ((Q : Subgroup ((center S).comap f)).map ((center S).comap f).subtype) ≤
      pCore q G :=
  le_sSup ⟨h.center_preimage_sylow_normal ih f hf q Q,
    Q.isPGroup'.map ((center S).comap f).subtype⟩

/-- The center preimage has trivial Sylow two-subgroup, by A.2.10. -/
theorem CounterexampleToTheoremA.center_preimage_two_sylow_eq_bot
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f)
    (Q : Sylow 2 ((center S).comap f)) :
    (Q : Subgroup ((center S).comap f)) = ⊥ := by
  apply (map_eq_bot_iff_of_injective _ ((center S).comap f).subtype_injective).mp
  apply le_bot_iff.mp
  simpa only [lemma_A_2_10 h ih] using h.center_preimage_sylow_le_pCore ih f hf 2 Q

/-- The entire center preimage has odd order, not merely the chosen kernel. -/
theorem CounterexampleToTheoremA.center_preimage_odd_card
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    Odd (Nat.card ((center S).comap f)) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  obtain ⟨Q⟩ := Sylow.nonempty (p := 2) (G := (center S).comap f)
  exact Q.ne_bot_of_dvd_card (even_iff_two_dvd.mp he)
    (h.center_preimage_two_sylow_eq_bot ih f hf Q)


/-- The nilpotent center preimage is precisely the ambient Fitting subgroup.
This retains the original epimorphism, rather than only an abstract quotient. -/
theorem CounterexampleToTheoremA.center_preimage_eq_fitting
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) :
    (center S).comap f = fittingSubgroup G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, h.center_preimage_isNilpotent ih f hf⟩
  · apply map_le_iff_le_comap.mp
    rw [← fittingSubgroup_eq_center_of_componentLayer_eq_top h.2.2.2.1]
    exact le_sSup ⟨Normal.map inferInstance f hf,
      Group.nilpotent_of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)⟩

/-- The prime core always lies in this marked center preimage. -/
theorem CounterexampleToTheoremA.pCore_le_center_preimage
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f) (q : ℕ) [Fact q.Prime] :
    pCore q G ≤ (center S).comap f := by
  rw [h.center_preimage_eq_fitting ih f hf]
  exact pCore_le_fitting G q

/-- A.2.11's marked identity follows once the source argument has excluded
all other Sylow primes of the center preimage. -/
theorem CounterexampleToTheoremA.center_preimage_eq_pCore_of_isPGroup
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f)
    (hp : IsPGroup p ((center S).comap f)) :
    (center S).comap f = pCore p G := by
  let : Fact p.Prime := ⟨h.2.2.2.2.1⟩
  exact le_antisymm (le_sSup ⟨inferInstance, hp⟩)
    (h.pCore_le_center_preimage ih f hf p)

/-- The actual prime-core quotient and center quotient are identified by
composition with the original epimorphism. -/
noncomputable def CounterexampleToTheoremA.primeCoreQuotientEquivOfIsPGroup
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G)
    (f : G →* S) (hf : Function.Surjective f)
    (hp : IsPGroup p ((center S).comap f)) :
    G ⧸ pCore p G ≃* S ⧸ center S := by
  let q := (QuotientGroup.mk' (center S)).comp f
  have hk : q.ker = pCore p G := by
    rw [show q = (QuotientGroup.mk' (center S)).comp f from rfl,
      ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact h.center_preimage_eq_pCore_of_isPGroup ih f hf hp
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q
      ((QuotientGroup.mk'_surjective _).comp hf))

end CFSG.Quasithin.ChapterA.Section02
