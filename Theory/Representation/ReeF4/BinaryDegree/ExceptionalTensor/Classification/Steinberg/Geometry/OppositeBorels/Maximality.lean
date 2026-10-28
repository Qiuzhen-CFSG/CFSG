module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Candidates
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Unipotence
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Maximality.NormalizerWords
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.CharacterSeparation.Generation.RootUniqueness.TangentSpan.DimensionBound.DenseParameters.CarrierBruhat
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition
public import Theory.AlgebraicGroup.Borel.Conjugation.theorem_1_6_2_b

/-!
# Maximal connected solvability of the literal F4 candidates

In a connected solvable overgroup of the fixed maximal torus, write a torus
normalizer point as a torus point times a radical point. Its commutator with
any torus point belongs to both the torus and the unipotent radical, so is
trivial. The concrete F4 torus centralizer is the torus itself.

Literal positive–normalizer–positive word coverage now proves maximality:
for a point of a solvable overgroup of the positive candidate, both positive
factors already lie in that candidate; the remaining normalizer word lies in
the overgroup, hence in the torus. The checked opposition word conjugates
this candidate to the negative candidate, proving maximality there as well.
The coverage proof uses root collection and rank-one exchange independently
of Borel certification. No extra geometric premise is assumed.

This proves the Borel clause of GLS3, Theorem 1.11.2 and Steinberg (6.2)(a)
(`refs/KGroup/GLS3/Chapter1.tex` and `Chapter2St2.tex`) for the corrected F4
root model and its unchanged positive roots. The existing `Unipotence` module
supplies connected solvability and the separate radical identifications.
-/

public noncomputable section

open Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private lemma solvable_normalizer_mem_centralizer (T S : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hc : _root_.IsConnected (S : Set (Variety.Point G)))
    (hs : Group.IsSolvable (Variety.Point S.carrierVariety)) (hTS : T ≤ S)
    (n : Variety.Point G) (hn : n ∈ S) (hN : n ∈ T.normalizer) :
    n ∈ T.centralizer := by
  obtain ⟨U, hU, _⟩ := exists_unipotentRadical_of_connected_solvable S hc hs
  obtain ⟨hfactor, _, hdisj⟩ :=
    maximalTorus_unipotentRadical_decomposition_of_connected_solvable hc hs hU hT hTS
  obtain ⟨a, v, ha, hv, rfl⟩ := hfactor n hn
  apply Subgroup.mem_centralizer_iff.mpr
  intro t ht
  have hcT (x y : Variety.Point G) (hx : x ∈ T) (hy : y ∈ T) : x * y = y * x := by
    exact (Subgroup.mem_centralizer_iff.mp (maximalTorus_le_centralizer hT hx) y hy).symm
  have hcommT : a * v * t * (a * v)⁻¹ * t⁻¹ ∈ T :=
    T.toSubgroup.mul_mem ((Subgroup.mem_normalizer_iff.mp hN t).mp ht)
      (T.toSubgroup.inv_mem ht)
  have hcommU : a * v * t * (a * v)⁻¹ * t⁻¹ ∈ U := by
    have hv' := hU.2.2.1 t (hTS ht) v⁻¹ (U.toSubgroup.inv_mem hv)
    have h := hU.2.2.1 a (hTS ha) (v * (t * v⁻¹ * t⁻¹)) (U.toSubgroup.mul_mem hv hv')
    have he : a * (v * (t * v⁻¹ * t⁻¹)) * a⁻¹ =
        a * v * t * (a * v)⁻¹ * t⁻¹ := by
      have hat := hcT t⁻¹ a⁻¹ (T.toSubgroup.inv_mem ht) (T.toSubgroup.inv_mem ha)
      simp only [mul_inv_rev, mul_assoc] at *
      rw [hat]
    rwa [he] at h
  have hone : a * v * t * (a * v)⁻¹ * t⁻¹ = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hdisj]
    exact ⟨hcommT, hcommU⟩
  have hnt : a * v * t = t * (a * v) := by
    have h := congrArg (fun z => z * t * (a * v)) hone
    simpa only [mul_assoc, inv_mul_cancel_left, one_mul, mul_inv_cancel_left, inv_mul_cancel, mul_one] using h
  exact hnt.symm


open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.F4Chevalley
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
open RootModel.Corrected
variable (F : Type u) [Field F] [IsAlgClosed F] [CharP F 2]
local instance : InvolutiveNeg Root := typeF4RootPairing.indexNeg
local instance (S : ClosedSubgroup (Carrier (k := F))) : AlgebraicGroup S.carrierVariety :=
  S.carrierAlgebraicGroup

/-- A connected solvable overgroup of the fixed torus has no further
torus-normalizer points. Relative radical normality is used inside that overgroup. -/
lemma normalizer_mem_torus (S : ClosedSubgroup (Carrier (k := F)))
    (hc : _root_.IsConnected (S : Set (Variety.Point (Carrier (k := F)))))
    (hs : Group.IsSolvable (Variety.Point S.carrierVariety))
    (hTS : splitTorus (k := F) ≤ S)
    (n : Variety.Point (Carrier (k := F))) (hn : n ∈ S)
    (hN : n ∈ (splitTorus (k := F)).normalizer) : n ∈ splitTorus (k := F) := by
  have h := solvable_normalizer_mem_centralizer (splitTorus (k := F)) S
    RootModel.Corrected.splitTorus_isMaximal hc hs hTS n hn hN
  change n ∈ (splitTorus (k := F)).centralizer.toSubgroup at h
  rwa [TorusConjugacy.splitTorus_centralizer_eq] at h

private lemma word_positive_le_candidate :
    DenseParameters.CarrierBruhat.positiveUnipotent (k := F) ≤
      (positiveCandidate F).toSubgroup := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨r, t, hr, rfl⟩
  exact rootGenerated_le_torusRootGenerated F _
    (rootElement_mem_rootGenerated F _ r hr t)

/-- The literal positive torus-and-root candidate is a Borel subgroup.
Bruhat coverage and solvable torus normalization prove maximality. -/
theorem positiveCandidate_isBorel : IsBorelSubgroup (positiveCandidate F) := by
  refine ⟨torusRootGenerated_connected F _, positiveCandidate_solvable, ?_⟩
  intro S hc hs hBS
  apply SetLike.coe_injective
  apply Set.Subset.antisymm ?_ hBS
  intro g hg
  obtain ⟨u, hu, n, hn, v, hv, hfactor⟩ :=
    DenseParameters.CarrierBruhat.exists_unrestricted_factors_of_rootTransport
      (fun _ hn => DenseParameters.normalizerWords_rootTransport hn) g
  have huB := word_positive_le_candidate F hu
  have hvB := word_positive_le_candidate F hv
  have hnS : n ∈ S := by
    have h := S.toSubgroup.mul_mem
      (S.toSubgroup.mul_mem (S.toSubgroup.inv_mem (hBS huB)) hg)
      (S.toSubgroup.inv_mem (hBS hvB))
    change u⁻¹ * g * v⁻¹ ∈ S at h
    simpa only [hfactor, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  have hnT := normalizer_mem_torus F S hc hs
    (fun _ ht => hBS (torus_le_torusRootGenerated F _ ht)) n hnS
    (Maximality.normalizerWords_le_normalizer hn)
  rw [hfactor]
  exact (positiveCandidate F).toSubgroup.mul_mem
    ((positiveCandidate F).toSubgroup.mul_mem huB (torus_le_torusRootGenerated F _ hnT)) hvB

private lemma rootGenerated_le_of_rootElements (A : Set (Roots F))
    (H : Subgroup (Variety.Point (Carrier (k := F))))
    (h : ∀ (r : Root), (⟨r⟩ : Roots F) ∈ A → ∀ t : F, algebraicRootElement r t ∈ H) :
    (rootGenerated F A).toSubgroup ≤ H := by
  rw [rootGenerated_toSubgroup, RootSubgroupGenerated_le_iff]
  rintro ⟨r⟩ hr x hx
  change x ∈ F4Chevalley.rootSubgroup r at hx
  obtain ⟨q, rfl⟩ := hx
  have hq : kPlusPoint (q.val PUnit.unit) = q := by
    apply (additiveGroupPointEquiv F).injective
    rfl
  simpa only [algebraicRootElement, hq] using h r hr (q.val PUnit.unit)

private lemma torusRootGenerated_le_opposition_conjugate
    (A B : Set (Roots F))
    (hneg : ∀ r : Root, (⟨r⟩ : Roots F) ∈ A → (⟨-r⟩ : Roots F) ∈ B) :
    torusRootGenerated F A ≤
      (torusRootGenerated F B).conjugate (Maximality.opposition (F := F)) := by
  change (splitTorus (k := F)).toSubgroup ⊔ (rootGenerated F A).toSubgroup ≤ _
  apply sup_le
  · intro t ht
    apply (ClosedSubgroup.mem_conjugate_iff _ _ _).mpr
    apply torus_le_torusRootGenerated F B
    have hN := (splitTorus (k := F)).normalizer.toSubgroup.inv_mem
      Maximality.opposition_mem_normalizer
    have h := (Subgroup.mem_normalizer_iff.mp hN t).mp ht
    change (Maximality.opposition (F := F))⁻¹ * t * (Maximality.opposition⁻¹)⁻¹ ∈ splitTorus (k := F) at h
    rw [inv_inv] at h
    exact h
  · apply rootGenerated_le_of_rootElements F A
    intro r hr t
    apply (ClosedSubgroup.mem_conjugate_iff _ _ _).mpr
    have he : (Maximality.opposition (F := F))⁻¹ * algebraicRootElement r t *
        Maximality.opposition = algebraicRootElement (-r) t := by
      simpa only [Maximality.opposition_inv] using Maximality.opposition_conj_root r t
    rw [he]
    exact rootGenerated_le_torusRootGenerated F B
      (rootElement_mem_rootGenerated F B (-r) (hneg r hr) t)

/-- The concrete opposition word conjugates the published positive candidate
to the published negative candidate, with the original root labels. -/
theorem opposition_conjugate_positiveCandidate :
    (positiveCandidate F).conjugate (Maximality.opposition (F := F)) = negativeCandidate F := by
  have hp := torusRootGenerated_le_opposition_conjugate F (positiveRoots F) (negativeRoots F)
    (fun r hr => by
      change typeF4RootPairing_base.IsPos (-(-r))
      change typeF4RootPairing_base.IsPos r at hr
      simpa only [neg_neg] using hr)
  have hn := torusRootGenerated_le_opposition_conjugate F (negativeRoots F) (positiveRoots F)
    (fun _ hr => hr)
  apply SetLike.coe_injective
  apply Set.Subset.antisymm ?_ hn
  intro x hx
  have h := (ClosedSubgroup.mem_conjugate_iff _ _ _).mp
    (hp ((ClosedSubgroup.mem_conjugate_iff _ _ _).mp hx))
  have he : (Maximality.opposition (F := F))⁻¹ *
      (Maximality.opposition⁻¹ * x * Maximality.opposition) * Maximality.opposition = x := by
    calc
      _ = Maximality.opposition * (Maximality.opposition⁻¹ * x * Maximality.opposition) *
          Maximality.opposition⁻¹ := by simp only [Maximality.opposition_inv]
      _ = x := by group
  rwa [he] at h

/-- The literal negative candidate is a Borel subgroup. -/
theorem negativeCandidate_isBorel : IsBorelSubgroup (negativeCandidate F) := by
  rw [← opposition_conjugate_positiveCandidate F]
  exact (positiveCandidate_isBorel F).conjugate _

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels
