module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.FixedAutomorphisms
public import Theory.SpecificGroups.SU3.HomocyclicSlice
public import Theory.SpecificGroups.SU3.OuterSylowFirstCoordinates
public import Theory.GroupTheory.InvolutionJoinNormalizer
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Marked homocyclic factors in the source unitary configuration

The binary Hermitian slice constructs T₀ inside the specified Sylow image T,
including the whole distinguished subgroup A. This works for both genuine
special and projective unitary covers with their two field cardinalities.
For V, A is the entire omega subgroup and embedded center. Relative
characteristicity proves preservation by the source involution, and the
actual distinguished element supplies a fixed nonidentity involution in the
supplied Sylow subgroup of the second centralizer.

The corrected normalizer U is detected by displacement into A. The outer
involution coordinate theorem aligns the supplied Sylow with the graph
action, preserving its fixed distinguished involution. Transport through
the actual special or projective model identifies U with the homocyclic
slice. The final theorem constructs both marked factors from the original
source inputs and the explicit second-centralizer data.

Source: GLS4, Chapter 2, the definitions before and the construction after
Lemma 13.4 (Chapter2.tex, lines2385–2420); Chapter 4, Lemma 3.4(d4–5).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory PFchapter1section1 PFAppendixIII BenderSuzuki.MatrixGroups
universe v

/-- Homocyclic subgroups in a supplied Sylow group of either actual unitary cover. -/
public theorem unitaryCover_homocyclic_sylow
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H) (P : Sylow 2 H) :
    ∃ R : Subgroup H, R ≤ P ∧
      Nonempty (R ≃* StandardHomocyclicCover (Fin n) 4) ∧
      ∀ x : H, x ∈ P → x ^ 2 = 1 → x ∈ R := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hmodel⟩ := hcover
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have finish (e : P ≃* External.hermitianUnipotentCoord J) :
      ∃ R : Subgroup H, R ≤ P ∧
        Nonempty (R ≃* StandardHomocyclicCover (Fin n) 4) ∧
        ∀ x : H, x ∈ P → x ^ 2 = 1 → x ∈ R := by
    obtain ⟨R, ⟨f⟩, hR⟩ := HermitianForm.HomocyclicSlice.exists_subgroup_of_equiv
      J hcard hfixed e rfl
    refine ⟨R.map (P : Subgroup H).subtype, map_subtype_le R, ?_, ?_⟩
    · exact ⟨(R.equivMapOfInjective (P : Subgroup H).subtype Subtype.val_injective).symm.trans f⟩
    · intro x hx hx2
      exact ⟨⟨x, hx⟩, hR ⟨x, hx⟩ (Subtype.ext hx2), rfl⟩
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    exact finish (((P : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective).trans
      (HermitianForm.SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ Q))
  · obtain ⟨e⟩ := hmodel
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    exact finish ((((P : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective).trans
      (HermitianForm.SylowOmega.specialSylowEquivProjective J Q)).trans
      (HermitianForm.SylowOmega.projectiveSylowEquivCoords J hn hcard hfixed hJ _))

/-- Centers and omega coincide in every supplied Sylow subgroup of either cover. -/
public theorem unitaryCover_sylow_omega
    {H : Type*} [Group H] [Finite H] {n : ℕ} (hn : 2 ≤ n)
    (hcover : IsUnitaryCentralizerCoverAt n H) (P : Sylow 2 H) :
    omegaOneAmbient (P : Subgroup H) = (center P).map (P : Subgroup H).subtype := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hmodel⟩ := hcover
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    exact (HermitianForm.SylowOmega.omega_of_projective_equiv J hn hcard hfixed hJ e P).1
  · obtain ⟨e⟩ := hmodel
    exact (HermitianForm.SylowOmega.omega_of_special_equiv J hn hcard hfixed hJ e P).1

private theorem map_omegaOneAmbient {H K : Type*} [Group H] [Group K]
    (P : Subgroup H) (f : H →* K) (hf : Function.Injective f) :
    (omegaOneAmbient P).map f = omegaOneAmbient (P.map f) := by
  change ((omega P (p := 2) 1).map P.subtype).map f =
    (omega (P.map f) (p := 2) 1).map (P.map f).subtype
  rw [map_map]
  exact map_omega_eq_of_injective_of_range_eq (f.comp P.subtype) (P.map f).subtype
    (hf.comp Subtype.val_injective) Subtype.val_injective
    (by rw [MonoidHom.range_comp, range_subtype, range_subtype]) 2 1

variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- Construct the source's marked subgroup T₀ inside the actual T. -/
public theorem exists_marked_T₀
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hn : 2 ≤ n) (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (d : SecondCentralizerData Z M z t u n) :
    ∃ T₀ : Subgroup G, T₀ ≤ localT Z M u ∧
      Nonempty (T₀ ≃* StandardHomocyclicCover (Fin n) 4) ∧
      closure (Z ∩ (M : Set G)) ≤ T₀ := by
  obtain ⟨S, hS⟩ := sylow_T h.disconnected r htM huD hu hn hunitary
  obtain ⟨R, hRS, ⟨eR⟩, hR⟩ := unitaryCover_homocyclic_sylow hn (hunitary u huD hu).2 S
  obtain ⟨_, _, _, hZ⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hAT : closure (Z ∩ (M : Set G)) ≤ localT Z M u :=
    (localT_inf_sourceLocalU h r ha hz hzM ht htM hL heven huD hu d e).symm.le.trans inf_le_left
  refine ⟨R.map (centralizerClosure Z u).subtype, ?_, ?_, ?_⟩
  · exact hS ▸ map_mono hRS
  · exact ⟨(R.equivMapOfInjective (centralizerClosure Z u).subtype Subtype.val_injective).symm.trans eR⟩
  · intro x hx
    have hxT := hAT hx
    have hx2 : x ^ 2 = 1 := congrArg Subtype.val
      ((localT_involutions h.disconnected r htM huD hu hZ ⟨x, hxT⟩).mp hx)
    obtain ⟨s, hs, rfl⟩ := hS.symm ▸ hxT
    exact ⟨s, hR s hs (Subtype.ext hx2), rfl⟩

/-- All square-one elements of V are precisely the marked subgroup A. -/
public theorem localV_involutions
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (d : SecondCentralizerData Z M z t u n)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    (x : localV Z M d.torus) :
    (x : G) ∈ closure (Z ∩ (M : Set G)) ↔ x ^ 2 = 1 := by
  have hx := localTwoCore_le M (distinguishedCentralizer Z d.torus) x.property
  constructor
  · intro hxA
    by_cases he : (x : G) = 1
    · exact Subtype.ext (by simp only [coe_pow, coe_one, he, one_pow])
    · have hi := h.involutions x ((hZ.symm ▸ ⟨hxA, he⟩ : (x : G) ∈ Z ∩ (M : Set G)).1)
      exact Subtype.ext hi.sq_eq_one
  · intro hs
    by_cases he : (x : G) = 1
    · rw [he]
      exact one_mem _
    · exact subset_closure ⟨second_involutions_distinguished h r hz hzM htM d hx.2
        ⟨he, congrArg Subtype.val hs⟩, hx.1⟩

/-- A is literally the first omega subgroup of V, in the ambient group. -/
public theorem localV_omega
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (d : SecondCentralizerData Z M z t u n) :
    omegaOneAmbient (localV Z M d.torus) = closure (Z ∩ (M : Set G)) := by
  obtain ⟨hAL, hMA, hA, hZ⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hAV : closure (Z ∩ (M : Set G)) ≤ localV Z M d.torus :=
    (distinguishedClosure_le_sourceLocalU hAL hMA hA d).trans inf_le_left
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hs
    exact (localV_involutions h.disconnected r hz hzM htM d hZ ⟨x, hx⟩).mpr (Subtype.ext hs)
  · intro x hx
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl x (hAV hx)
      (congrArg Subtype.val ((localV_involutions h.disconnected r hz hzM htM d hZ ⟨x, hAV hx⟩).mp hx))

/-- A is also the entire embedded center of the specified V. -/
public theorem localV_center
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (d : SecondCentralizerData Z M z t u n) :
    (center (localV Z M d.torus)).map (localV Z M d.torus).subtype =
      closure (Z ∩ (M : Set G)) := by
  obtain ⟨S, hS⟩ := sylow_V r hz hzM htM hn d
  have hs := congrArg (fun K => K.map (distinguishedCentralizer Z d.torus).subtype)
    (unitaryCover_sylow_omega hn d.second_cover S)
  rw [map_omegaOneAmbient _ _ Subtype.val_injective,
    map_embeddedCenter _ _ Subtype.val_injective, hS] at hs
  exact hs.symm.trans (localV_omega h r ha hz hzM ht htM hL heven d)

omit [Finite G] in
/-- The ambient involution preserves the literal V by relative characteristicity. -/
public theorem u_normalizes_localV (huD : u ∈ residualPairStabilizer M t)
    (d : SecondCentralizerData Z M z t u n) :
    u ∈ normalizer (localV Z M d.torus : Set G) := by
  apply normalizer_le_normalizer_characteristic_image
    (M ⊓ distinguishedCentralizer Z d.torus)
    (pCore 2 (M ⊓ distinguishedCentralizer Z d.torus : Subgroup G))
  apply mem_normalizer_iff.mpr
  intro x
  exact and_congr (mem_normalizer_iff.mp (M.le_normalizer huD.1) x)
    (mem_normalizer_iff.mp d.normalizes x)

/-- Restriction of conjugation by u to the specified V. -/
@[expose] public def localVInvolution (huD : u ∈ residualPairStabilizer M t)
    (d : SecondCentralizerData Z M z t u n) : MulAut (localV Z M d.torus) :=
  (localV Z M d.torus).normalizerMonoidHom ⟨u, u_normalizes_localV huD d⟩

omit [Finite G] in
/-- The source action preserves the supplied Sylow subgroup, with its literal image. -/
public theorem secondInvolution_preserves_sylow
    (huD : u ∈ residualPairStabilizer M t)
    (d : SecondCentralizerData Z M z t u n)
    (S : Sylow 2 (distinguishedCentralizer Z d.torus))
    (hS : (S : Subgroup (distinguishedCentralizer Z d.torus)).map
      (distinguishedCentralizer Z d.torus).subtype = localV Z M d.torus)
    (x : distinguishedCentralizer Z d.torus) (hx : x ∈ S) :
    secondInvolution d x ∈ S := by
  have hxV : (x : G) ∈ localV Z M d.torus :=
    hS ▸ mem_map_of_mem (distinguishedCentralizer Z d.torus).subtype hx
  have hyV := (mem_normalizer_iff.mp (u_normalizes_localV huD d) x.val).mp hxV
  change (secondInvolution d x).val ∈ localV Z M d.torus at hyV
  rw [← hS] at hyV
  obtain ⟨y, hy, he⟩ := hyV
  exact (Subtype.ext he : y = secondInvolution d x) ▸ hy

/-- The actual distinguished z supplies a fixed nonidentity involution in that Sylow group. -/
public theorem second_sylow_fixed_involution
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (d : SecondCentralizerData Z M z t u n)
    (S : Sylow 2 (distinguishedCentralizer Z d.torus))
    (hS : (S : Subgroup (distinguishedCentralizer Z d.torus)).map
      (distinguishedCentralizer Z d.torus).subtype = localV Z M d.torus) :
    ∃ x : distinguishedCentralizer Z d.torus,
      x ∈ S ∧ x ≠ 1 ∧ x ^ 2 = 1 ∧ secondInvolution d x = x := by
  obtain ⟨hAL, hMA, hA, _⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hzA : z ∈ closure (Z ∩ (M : Set G)) := subset_closure ⟨hz, hzM⟩
  have hzV := (distinguishedClosure_le_sourceLocalU hAL hMA hA d hzA).1
  obtain ⟨x, hx, he⟩ := hS.symm ▸ hzV
  change (x : G) = z at he
  have hi := h.disconnected.involutions z hz
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · intro hx1
    exact hi.ne_one (he.symm.trans (congrArg Subtype.val hx1))
  · apply Subtype.ext
    simpa only [coe_pow, coe_one, he] using hi.sq_eq_one
  · apply Subtype.ext
    change u * x.val * u⁻¹ = x.val
    rw [he]
    have hfix : z ∈ distinguishedCentralizer Z d.torus ⊓ centralizer ({u} : Set G) :=
      d.fixed.symm ▸ hAL hzA
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hfix.2).symm

/-- The literal U condition is fixation modulo the marked A. -/
public theorem mem_sourceLocalU_iff_displacement
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hMA : M ≤ normalizer (closure (Z ∩ (M : Set G)) : Set G))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) (x : localV Z M d.torus) :
    (x : G) ∈ sourceLocalU Z M d.torus u ↔
      ((localVInvolution huD d x * x⁻¹ : localV Z M d.torus) : G) ∈
        closure (Z ∩ (M : Set G)) := by
  have huF : u ∉ distinguishedCentralizer Z d.torus := by
    intro huF
    exact d.noninner ⟨u, huF, fun _ _ => rfl⟩
  have hx := localTwoCore_le M (distinguishedCentralizer Z d.torus) x.property
  change (x.val ∈ localV Z M d.torus ∧ x.val ∈ normalizer
    ((closure (Z ∩ (M : Set G)) ⊔ zpowers u : Subgroup G) : Set G)) ↔ _
  rw [and_iff_right x.property]
  exact mem_normalizer_join_involution_iff _ _ u x.val
    (hAL.trans (d.intersection ▸ inf_le_left)) huF hu.sq_eq_one
    (hMA huD.1) hx.2 (hMA hx.1)

/-- Every root-coordinate identification takes the marked A to first coordinate zero. -/
public theorem localV_coord_first_zero_iff
    {E : Type*} [Field E] [CharP E 2] (J : HermitianForm 3 E)
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (htM : t ∉ M)
    (d : SecondCentralizerData Z M z t u n)
    (hZ : Z ∩ (M : Set G) = (closure (Z ∩ (M : Set G)) : Set G) \ {1})
    (c : localV Z M d.torus ≃* External.hermitianUnipotentCoord J)
    (x : localV Z M d.torus) :
    (c x).val.1 = 0 ↔ (x : G) ∈ closure (Z ∩ (M : Set G)) := by
  rw [← HermitianForm.EvenSemilinear.square_eq_one_iff_first_zero,
    ← map_pow, ← c.map_one, c.injective.eq_iff]
  exact (localV_involutions h r hz hzM htM d hZ x).symm

/-- Once the actual involution acts as conjugation on the first coordinate,
the literal source normalizer is the homocyclic slice. -/
public theorem sourceLocalU_homocyclic_of_graph_coordinates
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {a : E // J.conj a = a} = 2 ^ n)
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n)
    (c : localV Z M d.torus ≃* External.hermitianUnipotentCoord J)
    (hact : ∀ x : localV Z M d.torus,
      (c (localVInvolution huD d x)).val.1 = J.conj (c x).val.1) :
    Nonempty (sourceLocalU Z M d.torus u ≃* StandardHomocyclicCover (Fin n) 4) := by
  obtain ⟨hAL, hMA, _, hZ⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hmem (x : localV Z M d.torus) :
      (x : G) ∈ sourceLocalU Z M d.torus u ↔
        c x ∈ HermitianForm.HomocyclicSlice.slice J := by
    rw [mem_sourceLocalU_iff_displacement hAL hMA huD hu d,
      ← localV_coord_first_zero_iff J h.disconnected r hz hzM htM d hZ c]
    rw [map_mul, map_inv]
    change (c (localVInvolution huD d x)).val.1 + -(c x).val.1 = 0 ↔
      J.conj (c x).val.1 = (c x).val.1
    rw [hact, ← sub_eq_add_neg, sub_eq_zero]
  let f : sourceLocalU Z M d.torus u →* HermitianForm.HomocyclicSlice.slice J := {
    toFun := fun x => ⟨c ⟨x.val, x.property.1⟩, (hmem _).mp x.property⟩
    map_one' := Subtype.ext c.map_one
    map_mul' := by
      intro x y
      apply Subtype.ext
      exact c.map_mul ⟨x.val, x.property.1⟩ ⟨y.val, y.property.1⟩ }
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (congrArg (fun q : localV Z M d.torus => (q : G)) (c.injective (congrArg Subtype.val hxy)))
    · intro y
      refine ⟨⟨(c.symm y.val).val, (hmem (c.symm y.val)).mpr ?_⟩, ?_⟩
      · simpa only [c.apply_symm_apply] using y.property
      · exact Subtype.ext (c.apply_symm_apply y.val)
  obtain ⟨e⟩ := HermitianForm.HomocyclicSlice.homocyclic J hcard hfixed rfl
  exact ⟨(MulEquiv.ofBijective f hf).trans e⟩

/-- Assemble both marked factors from the single remaining action-coordinate input.
The T₀ construction and the literal U normalizer calculation are discharged. -/
public theorem homocyclicFactors_of_graph_coordinates
    {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {a : E // J.conj a = a} = 2 ^ n)
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hn : 2 ≤ n) (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (d : SecondCentralizerData Z M z t u n)
    (c : localV Z M d.torus ≃* External.hermitianUnipotentCoord J)
    (hact : ∀ x : localV Z M d.torus,
      (c (localVInvolution huD d x)).val.1 = J.conj (c x).val.1) :
    Nonempty (HomocyclicFactors Z M z t u n d) := by
  obtain ⟨T₀, hT₀, heT₀, hAT₀⟩ := exists_marked_T₀ h r ha hz hzM ht htM hL heven
    huD hu hn e hunitary d
  exact ⟨{
    U_homocyclic := sourceLocalU_homocyclic_of_graph_coordinates J hcard hfixed
      h r ha hz hzM ht htM hL heven huD hu d c hact
    T₀ := T₀
    T₀_le := hT₀
    T₀_homocyclic := heT₀
    A_le_T₀ := hAT₀ }⟩

/-- Construct both marked homocyclic factors from the original source inputs.

The model action is transported through the actual isomorphism in
`SecondCentralizerData.second_cover`.  The supplied Sylow subgroup is carried
to the model Sylow, and the fixed distinguished involution supplies the
nontrivial fixed point required by the outer-coordinate theorem.  This keeps
the source normalizer literal while retaining both the projective and special
unitary cover alternatives.
-/
public theorem homocyclicFactors_of_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (_hlocal : ResidualCentralizerLocalData Z M z t)
    (_hshear : ResidualCentralizerShearing Z M t)
    (_hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w)
    (hn : 2 ≤ n) (_hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    Nonempty (HomocyclicFactors Z M z t u n d) := by
  obtain ⟨S, hS⟩ := sylow_V r hz hzM htM hn d
  obtain ⟨E, _, _, J, hJ, hfieldcard, hfixed, hmodel⟩ := d.second_cover
  let F := distinguishedCentralizer Z d.torus
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [Nat.card_eq_fintype_card, pow_mul] using hfieldcard)
  have finish (c : localV Z M d.torus ≃* External.hermitianUnipotentCoord J)
      (hact : ∀ x : localV Z M d.torus,
        (c (localVInvolution huD d x)).val.1 = J.conj (c x).val.1) :
      Nonempty (HomocyclicFactors Z M z t u n d) :=
    homocyclicFactors_of_graph_coordinates J hfieldcard hfixed h r ha hz hzM ht htM hL
      heven huD hu hn eL hunitary d c hact
  rcases hmodel with hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let a := MulAut.congr e (secondInvolution d)
    have ha2 : a ^ 2 = 1 := by
      change (MulAut.congr e (secondInvolution d)) ^ 2 = 1
      rw [← map_pow, secondInvolution_sq_eq_one hu d, map_one]
    have haouter : ¬ ∃ x, a = MulAut.conj x := by
      exact fun hi => (secondInvolution_not_inner d)
        ((MulAut.congr_inner_iff e (secondInvolution d)).mp hi)
    have hstable (x : ProjectiveSpecialUnitaryMatrixGroup J) (hx : x ∈ Q) :
        a x ∈ Q := by
      obtain ⟨y, hy, rfl⟩ := hx
      change (MulAut.congr e (secondInvolution d)) (e y) ∈ Q
      have hy' : e ((secondInvolution d) y) ∈
          (S : Subgroup F).map e.toMonoidHom :=
        mem_map_of_mem e.toMonoidHom
          (secondInvolution_preserves_sylow huD d S hS y hy)
      rw [show (MulAut.congr e (secondInvolution d)) (e y) =
        e ((secondInvolution d) y) by simp [MulAut.congr_apply]]
      exact hy'
    obtain ⟨x, hx, hxne, hx2, hxf⟩ := second_sylow_fixed_involution h r ha hz hzM ht htM
      hL heven d S hS
    let z' := e x
    have hzQ : z' ∈ Q := mem_map_of_mem e.toMonoidHom hx
    have hzne : z' ≠ 1 := by
      intro heq
      apply hxne
      apply e.injective
      simpa [z'] using heq
    have hz2 : z' ^ 2 = 1 := by
      simpa [z'] using congrArg e (show x ^ 2 = 1 from hx2)
    have hfix : a z' = z' := by
      simpa [a, z', MulAut.congr_apply] using congrArg e hxf
    obtain ⟨cQ, hcQ⟩ :=
      BenderSuzuki.MatrixGroups.HermitianForm.OuterSylowFirstCoordinates.projective_first_coordinates
        J hJ hn hfieldcard hfixed Q a ha2 haouter hstable z' hzQ hzne hz2 hfix
    let fS : (S : Subgroup F) ≃* Q :=
      (S : Subgroup F).equivMapOfInjective e.toMonoidHom e.injective |>.trans
        (MulEquiv.subgroupCongr (by rfl))
    let iS := (S : Subgroup F).equivMapOfInjective F.subtype F.subtype_injective
    let g : localV Z M d.torus ≃* (S : Subgroup F) :=
      (MulEquiv.subgroupCongr hS.symm).trans iS.symm
    let fV : localV Z M d.torus ≃* Q := g.trans fS
    have hgval (q : localV Z M d.torus) : ((g q : F) : G) = q := by
      have hh := congrArg (fun r : (S : Subgroup F).map F.subtype => (r : G))
        (iS.apply_symm_apply (MulEquiv.subgroupCongr hS.symm q))
      exact hh
    have htransport (x : localV Z M d.torus) :
        fV (localVInvolution huD d x) =
          (MulAut.congr e (secondInvolution d)) (fV x) := by
      have hgy : g (localVInvolution huD d x) = secondInvolution d (g x) := by
        apply Subtype.ext
        have hh : ((g (localVInvolution huD d x) : F) : G) =
            u * ((g x : F) : G) * u⁻¹ := by
          rw [hgval, hgval]
          rfl
        simpa [localVInvolution, secondInvolution] using hh
      have hfV (q : localV Z M d.torus) :
          (fV q : ProjectiveSpecialUnitaryMatrixGroup J) = e (g q) := by
        rfl
      change (fV (localVInvolution huD d x) :
        ProjectiveSpecialUnitaryMatrixGroup J) =
        (MulAut.congr e (secondInvolution d)) (fV x)
      rw [hfV, hfV]
      rw [hgy]
      simp [MulAut.congr_apply]
    let c := fV.trans cQ
    apply finish c
    intro x
    have hp : c (localVInvolution huD d x) =
        cQ ⟨a (fV x), hstable (fV x) (fV x).property⟩ := by
      change cQ (fV (localVInvolution huD d x)) = _
      apply congrArg cQ
      apply Subtype.ext
      exact htransport x
    rw [hp]
    exact hcQ (fV x)
  · obtain ⟨e⟩ := hmodel
    let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let a := MulAut.congr e (secondInvolution d)
    have ha2 : a ^ 2 = 1 := by
      change (MulAut.congr e (secondInvolution d)) ^ 2 = 1
      rw [← map_pow, secondInvolution_sq_eq_one hu d, map_one]
    have haouter : ¬ ∃ x, a = MulAut.conj x := by
      exact fun hi => (secondInvolution_not_inner d)
        ((MulAut.congr_inner_iff e (secondInvolution d)).mp hi)
    have hstable (x : J.specialSubgroup) (hx : x ∈ Q) : a x ∈ Q := by
      obtain ⟨y, hy, rfl⟩ := hx
      change (MulAut.congr e (secondInvolution d)) (e y) ∈ Q
      have hy' : e ((secondInvolution d) y) ∈
          (S : Subgroup F).map e.toMonoidHom :=
        mem_map_of_mem e.toMonoidHom
          (secondInvolution_preserves_sylow huD d S hS y hy)
      rw [show (MulAut.congr e (secondInvolution d)) (e y) =
        e ((secondInvolution d) y) by simp [MulAut.congr_apply]]
      exact hy'
    obtain ⟨x, hx, hxne, hx2, hxf⟩ := second_sylow_fixed_involution h r ha hz hzM ht htM
      hL heven d S hS
    let z' := e x
    have hzQ : z' ∈ Q := mem_map_of_mem e.toMonoidHom hx
    have hzne : z' ≠ 1 := by
      intro heq
      apply hxne
      apply e.injective
      simpa [z'] using heq
    have hz2 : z' ^ 2 = 1 := by
      simpa [z'] using congrArg e (show x ^ 2 = 1 from hx2)
    have hfix : a z' = z' := by
      simpa [a, z', MulAut.congr_apply] using congrArg e hxf
    obtain ⟨cQ, hcQ⟩ :=
      BenderSuzuki.MatrixGroups.HermitianForm.OuterSylowFirstCoordinates.special_first_coordinates
        J hJ hn hfieldcard hfixed Q a ha2 haouter hstable z' hzQ hzne hz2 hfix
    let fS : (S : Subgroup F) ≃* Q :=
      (S : Subgroup F).equivMapOfInjective e.toMonoidHom e.injective |>.trans
        (MulEquiv.subgroupCongr (by rfl))
    let iS := (S : Subgroup F).equivMapOfInjective F.subtype F.subtype_injective
    let g : localV Z M d.torus ≃* (S : Subgroup F) :=
      (MulEquiv.subgroupCongr hS.symm).trans iS.symm
    let fV : localV Z M d.torus ≃* Q := g.trans fS
    have hgval (q : localV Z M d.torus) : ((g q : F) : G) = q := by
      have hh := congrArg (fun r : (S : Subgroup F).map F.subtype => (r : G))
        (iS.apply_symm_apply (MulEquiv.subgroupCongr hS.symm q))
      exact hh
    have htransport (x : localV Z M d.torus) :
        fV (localVInvolution huD d x) =
          (MulAut.congr e (secondInvolution d)) (fV x) := by
      have hgy : g (localVInvolution huD d x) = secondInvolution d (g x) := by
        apply Subtype.ext
        have hh : ((g (localVInvolution huD d x) : F) : G) =
            u * ((g x : F) : G) * u⁻¹ := by
          rw [hgval, hgval]
          rfl
        simpa [localVInvolution, secondInvolution] using hh
      have hfV (q : localV Z M d.torus) : (fV q : J.specialSubgroup) = e (g q) := by
        rfl
      change (fV (localVInvolution huD d x) : J.specialSubgroup) =
        (MulAut.congr e (secondInvolution d)) (fV x)
      rw [hfV, hfV]
      rw [hgy]
      simp [MulAut.congr_apply]
    let c := fV.trans cQ
    apply finish c
    intro x
    have hp : c (localVInvolution huD d x) =
        cQ ⟨a (fV x), hstable (fV x) (fV x).property⟩ := by
      change cQ (fV (localVInvolution huD d x)) = _
      apply congrArg cQ
      apply Subtype.ext
      exact htransport x
    rw [hp]
    exact hcQ (fV x)

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
