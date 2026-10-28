module

public import Stellmacher.SectionTwo.NormalSupplementV
public import Stellmacher.SectionTwo.CoreCentralizerCriterion

/-!
# The core-centralizer equality in a normal supplement

Under the normalized-Sylow-supplement hypotheses, if `O₂(E)` is
Sylow in `C_E(vSubgroup S)`, then it equals
`C_Q(vSubgroup Q)`. This supplies the precise extra hypothesis
of Stellmacher (2.3) for the local group `E` used in (4.6).

The imported normal-closure comparison puts `vSubgroup S` inside
the image of `vSubgroup Q`, hence inside `E`. Its relative
centralizer is therefore the intrinsic centralizer of its restriction.
The core-centralizer criterion applied inside `E` gives the result.

Source: `refs/latex/stellmacher-n-group.tex`, (2.3) and the second
paragraph of the proof of (4.6).
-/

namespace Stellmacher.SectionTwo

/-- Sylow control of the old V-centralizer gives the (2.3) core equality
for the Sylow subgroup of the normal supplement. -/
public theorem normal_supplement_core_centralizer
    {G : Type*} [Group G] [Finite G] (E : Subgroup G) [E.Normal]
    (S : Sylow 2 G) (Q : Sylow 2 E)
    (hgen : E ⊔ (S : Subgroup G) = ⊤)
    (hQS : (Q : Subgroup E).map E.subtype ≤ (S : Subgroup G))
    (hZQ : zSubgroup S ≤ (Q : Subgroup E).map E.subtype)
    (hSN : (S : Subgroup G) ≤
      Subgroup.normalizer (((Q : Subgroup E).map E.subtype : Subgroup G) : Set G))
    (hSyl : ∃ T : Sylow 2 ((Subgroup.centralizer (vSubgroup S : Set G)).subgroupOf E),
      (T : Subgroup ((Subgroup.centralizer (vSubgroup S : Set G)).subgroupOf E)).map
        ((Subgroup.centralizer (vSubgroup S : Set G)).subgroupOf E).subtype = pCore 2 E) :
    pCore 2 E = (Q : Subgroup E) ⊓ Subgroup.centralizer (vSubgroup Q : Set E) := by
  have hVmap := vSubgroup_le_map_of_normal_supplement E S Q hgen hQS hZQ hSN
  have hVE : vSubgroup S ≤ E := hVmap.trans (Subgroup.map_subtype_le _)
  have hVsub : (vSubgroup S).subgroupOf E ≤ vSubgroup Q := by
    intro v hv
    obtain ⟨w, hw, heq⟩ := hVmap hv
    exact (E.subtype_injective heq) ▸ hw
  have hcent : (Subgroup.centralizer (vSubgroup S : Set G)).subgroupOf E =
      Subgroup.centralizer ((vSubgroup S).subgroupOf E : Set E) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx v hv)
    · intro hx
      change (x : G) ∈ Subgroup.centralizer (vSubgroup S : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact congrArg (fun e : E ↦ (e : G))
        (Subgroup.mem_centralizer_iff.mp hx ⟨v, hVE hv⟩ hv)
  rw [hcent] at hSyl
  exact twoCore_eq_sylow_centralizer_of_sylow_control Q ((vSubgroup S).subgroupOf E)
    hVsub hSyl

end Stellmacher.SectionTwo
