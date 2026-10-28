module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Sylow

/-!
# Simultaneous source selection (16A)–(16E)

Conjugating the swapping involution by D preserves the literal two-point
stabilizer. Thus the maximal trace choice remains maximal while the swapping
involution is made to commute with it. A Sylow subgroup of C_M(u) then supplies
a distinguished z in its center and is also Sylow in C_G(u).

Source: GLS4, Chapter 2, the notation preceding Lemma 16.2.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- The D-conjugate swapping involution determines exactly the same D. -/
public theorem residualPairStabilizer_conj_swapping_eq {t : G}
    (d : residualPairStabilizer M t) :
    residualPairStabilizer M (MulAut.conj (d : G) t) = residualPairStabilizer M t := by
  have hM : M.conjBy (d : G)⁻¹ = M := mem_normalizer_iff_map_conj_eq.mp
    (M.le_normalizer (M.inv_mem d.property.1))
  have hD : (M.conjBy t⁻¹).conjBy (d : G) = M.conjBy t⁻¹ :=
    mem_normalizer_iff_map_conj_eq.mp ((rightConjugate M t).le_normalizer d.property.2)
  change M ⊓ M.conjBy (MulAut.conj (d : G) t)⁻¹ = M ⊓ M.conjBy t⁻¹
  simp only [MulAut.conj_apply, mul_inv_rev, inv_inv, conjBy_mul, hM, hD]

/-- A maximal selected u, a swapping t₁ for the same two points, and the
actual Sylow T₁ with z in its center. No local recognition is assumed. -/
public theorem exists_source_centralizer_configuration
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hn : ¬ IsStronglyEmbedded M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M) :
    ∃ u t₁ : G, u ∈ residualPairStabilizer M t₁ ∧
      IsInvolution u ∧ u ∉ Z ∧ t₁ ∈ Z ∧ t₁ ∉ M ∧ Commute t₁ u ∧
      residualPairStabilizer M t₁ = residualPairStabilizer M t ∧
      (∀ v ∈ residualPairStabilizer M t₁, IsInvolution v →
        (residualCentralizerTrace Z M v).ncard ≤ (residualCentralizerTrace Z M u).ncard) ∧
      ∃ S : Sylow 2 (centralizer ({u} : Set G) ⊓ M : Subgroup G),
        let H := centralizer ({u} : Set G) ⊓ M
        let T₁ := (S : Subgroup H).map H.subtype
        u ∈ T₁ ∧ ∃ z ∈ Z, z ∈ T₁ ∧ T₁ ≤ centralizer ({z} : Set G) ∧
          ∃ P : Sylow 2 (centralizer ({u} : Set G)),
            (P : Subgroup (centralizer ({u} : Set G))).map
              (centralizer ({u} : Set G)).subtype = T₁ := by
  obtain ⟨u,huD,hu,huZ,hmax,_,_,_,_,_,d,hdt,hdtM,hdtc⟩ :=
    exists_maximal_centralizer_marked_pair h r ha hn ht htM
  let t₁ := MulAut.conj (d : G) t
  have hpair : residualPairStabilizer M t₁ = residualPairStabilizer M t :=
    residualPairStabilizer_conj_swapping_eq d
  let S : Sylow 2 (centralizer ({u} : Set G) ⊓ M : Subgroup G) := default
  exact ⟨u,t₁,hpair.symm ▸ huD,hu,huZ,hdt,hdtM,hdtc,hpair,hpair.symm ▸ hmax,S,
    involutionCentralizer_sylow_and_marked_center h r hu huD.1 S⟩

end BenderSuzuki.ZD
