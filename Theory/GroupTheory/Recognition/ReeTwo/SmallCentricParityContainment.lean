module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityRepresentatives
public import Theory.GroupTheory.Recognition.ReeTwo.SmallCentricCharacterKernels
public import Theory.GroupTheory.CentricRadicalCertificates
public import Theory.GroupTheory.SubgroupEnumerationDescending
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensus
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityAutomorphisms
public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityOmegaWitnesses

/-!
# Assembly of small Ree two parity containment

A complete census of small centric Frattini survivors reduces parity
containment to nineteen explicit subgroups. Fourteen can be excluded by a
two-group automorphism group, and five by an outside normalizer element with
trivial Frattini actions on omega and its quotient. The proof transports
centricity, order and intrinsic radicality to the census representative.

The conditional assembly retains explicit census and certificate inputs. The
final theorem discharges them using the exhaustive maximal-subgroup descent,
the fourteen verified automorphism calculations and the five omega witnesses.

Source: the verified Shinoda (1975) root model, and the intrinsic radical
obstructions in `CentricRadicalObstructions`.
-/

namespace ReeTwo.SylowModel

private theorem candidate_excluded
    (ha : ∀ i : Fin 14, IsPGroup 2 (MulAut (smallParityTwoCandidate i)))
    (hw : ∀ i : Fin 5, Subgroup.HasOmegaFrattiniWitness 2 (smallParityOddCandidate i)) :
    ∀ i : Fin 19,
      Subgroup.centralizer (smallParityCandidate i : Set SylowModel) ≤ smallParityCandidate i →
      (smallParityCandidate i).normalizerMonoidHom.range ⊓
        pCore 2 (MulAut (smallParityCandidate i)) ≤
        (MulAut.conj : smallParityCandidate i →* MulAut (smallParityCandidate i)).range →
      Nat.card (smallParityCandidate i) < 1024 → False := by
  intro i
  refine Fin.addCases (m := 14) (n := 5)
    (fun j => ?_) (fun j => ?_) i
  · rw [show smallParityCandidate (Fin.castAdd 5 j) = smallParityTwoCandidate j by
      simp only [smallParityCandidate, Fin.addCases_left]]
    intro hc hr hn
    exact not_isPGroup_mulAut_of_small_intrinsic_radical
      (smallParityTwoCandidate j) hc hr hn (ha j)
  · rw [show smallParityCandidate (Fin.natAdd 14 j) = smallParityOddCandidate j by
      simp only [smallParityCandidate, Fin.addCases_right]]
    intro hc hr _
    exact Subgroup.not_hasOmegaFrattiniWitness_of_intrinsic_radical
      (smallParityOddCandidate j)
      ((IsPGroup.of_card (n := 12) card).to_subgroup _) hc hr (hw j)

/-- Complete coverage and the two independent families of local certificates
imply the desired parity containment, with the original hypotheses. -/
public theorem small_le_character_ker_of_census_of_certificates
    (hcensus : ∀ U : Subgroup SylowModel,
      Subgroup.centralizer (U : Set SylowModel) ≤ U →
      Nat.card U < 1024 →
      (∀ g : Subgroup.normalizer (U : Set SylowModel),
        Subgroup.quotientAut (frattini U) (U.normalizerMonoidHom g) = 1 →
        (g : SylowModel) ∈ U) →
      U ≤ character.ker ∨ ∃ (i : Fin 19) (g : SylowModel),
        U.map (MulAut.conj g).toMonoidHom = smallParityCandidate i)
    (ha : ∀ i : Fin 14, IsPGroup 2 (MulAut (smallParityTwoCandidate i)))
    (hw : ∀ i : Fin 5, Subgroup.HasOmegaFrattiniWitness 2 (smallParityOddCandidate i))
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) : U ≤ character.ker := by
  have hfr := Subgroup.mem_of_intrinsic_radical_of_frattini_action_eq_one
    U ((IsPGroup.of_card (n := 12) card).to_subgroup U) hcent hrad
  rcases hcensus U hcent hcard hfr with hp | ⟨i, g, hg⟩
  · exact hp
  · have hc := Theory.GroupTheory.SubgroupEnumeration.centralizer_le_map
      U (MulAut.conj g) hcent
    have hr := Subgroup.intrinsic_radical_map U (MulAut.conj g) 2 hrad
    have hn : Nat.card (U.map (MulAut.conj g).toMonoidHom) < 1024 := by
      calc
        Nat.card (U.map (MulAut.conj g).toMonoidHom) = Nat.card U :=
          Nat.card_congr (U.equivMapOfInjective (MulAut.conj g).toMonoidHom
            (MulAut.conj g).injective).toEquiv.symm
        _ < 1024 := hcard
    rw [hg] at hc hr hn
    exact (candidate_excluded ha hw i hc hr hn).elim

/-- Every centric intrinsic radical subgroup of order less than 1024 lies in
the parity character kernel. The census and all local exclusions are proved
in the verified Sylow model. -/
public theorem small_le_character_ker_of_intrinsic_radical
    (U : Subgroup SylowModel)
    (hcent : Subgroup.centralizer (U : Set SylowModel) ≤ U)
    (hrad : U.normalizerMonoidHom.range ⊓ pCore 2 (MulAut U) ≤
      (MulAut.conj : U →* MulAut U).range)
    (hcard : Nat.card U < 1024) : U ≤ character.ker := by
  exact small_le_character_ker_of_census_of_certificates
    smallParityCensus smallParityTwo_isPGroup_mulAut
    smallParityOddCandidate_hasOmegaFrattiniWitness U hcent hrad hcard

end ReeTwo.SylowModel
