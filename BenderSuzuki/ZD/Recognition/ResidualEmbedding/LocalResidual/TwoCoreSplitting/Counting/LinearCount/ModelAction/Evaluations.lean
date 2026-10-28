module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.Counting.LinearCount.LocalAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.Torus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.SuzukiGeometry
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.ModelTransport
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Counting.UniformCases.Numerics.LocalGeometry.BorelDegree
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Theory.SpecificGroups.Suzuki.BorelSolvable
public import Theory.GroupTheory.OddInvolutionNormalizer
public import Theory.GroupTheory.SylowNormalizerCentralQuotient

/-!
# The four concrete Section 17 local actions

The marked involution lies in B = C_G(u)°. Conjugating it into the chosen
Sylow subgroup makes that Sylow meet Z, so product disconnection puts its
normalizer in M. Maximality of the model Borel then identifies M ∩ B with
that very normalizer. The original D ∩ B is its literal two-point subgroup.

The model root orders give the degrees q+1, q²+1, q³+1, q³+1. The full and
fixed torus orders give relative centralizer index q−1 in all four cases.
For SU₃ the actual central quotient preserves the Borel index, while the
Sylow comparison is injective on the two-subgroup. A genuine Hermitian basis
change permits arbitrary input forms without changing either field order.

Source: GLS4, Chapter 4, Lemma 3.2(a–e), and Chapter 2, (17D), Lemma 17.2(a).
The four exports retain the original residual hypotheses and local data.
-/

noncomputable section

namespace BenderSuzuki.ZD.Section17.ModelAction
open Subgroup PFAppendixIII PFchapter1section1 RankOneModelGeometry Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

omit [Finite G] in
/-- The marked outside involution lies in the original centralizer circle. -/
public theorem t_mem_circle (d : TwoCoreLocalData Z M) :
    d.t ∈ centralizerClosure Z ((d.u : M) : G) :=
  mem_centralizerClosure d.t_mem d.commutes_t.symm

omit [Finite G] in
private theorem circle_stabilizer_ne_top (d : TwoCoreLocalData Z M) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype ≠ ⊤ := by
  intro he
  exact d.t_not_mem (show (⟨d.t, t_mem_circle d⟩ : centralizerClosure Z ((d.u : M) : G)) ∈
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype from he ▸ mem_top _)

private theorem normalizer_le_circle_stabilizer (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M) :
    normalizer (P : Set _) ≤ M.comap (centralizerClosure Z ((d.u : M) : G)).subtype := by
  let B := centralizerClosure Z ((d.u : M) : G)
  let t : B := ⟨d.t, t_mem_circle d⟩
  have ht : orderOf t = 2 ^ 1 := by
    rw [Subgroup.orderOf_mk, pow_one]
    exact orderOf_eq_prime (h.involutions d.t d.t_mem).sq_eq_one
      (h.involutions d.t d.t_mem).ne_one
  obtain ⟨s, hs⟩ := P.exists_isConj_of_orderOf_eq_prime_pow ht
  obtain ⟨g, hg⟩ := isConj_iff.mp hs
  have hsZ : ((s : B) : G) ∈ Z := by
    have he : MulAut.conj (g : G) d.t = ((s : B) : G) := congrArg Subtype.val hg
    rw [← he]
    exact h.invariant (g : G) d.t d.t_mem
  have hn := normalizer_le h hPM ⟨((s : B) : G), hsZ, mem_map_of_mem _ s.property⟩
  intro x hx
  exact hn (le_normalizer_map B.subtype (mem_map_of_mem _ hx))

private theorem circle_stabilizer_eq_of_coatom (h : IsProductDisconnected Z M)
    (d : TwoCoreLocalData Z M) (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M)
    (hc : IsCoatom (normalizer (P : Set (centralizerClosure Z ((d.u : M) : G))))) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype = normalizer (P : Set _) := by
  exact (hc.le_iff_eq (circle_stabilizer_ne_top d)).mp (normalizer_le_circle_stabilizer h d P hPM)

omit [Finite G] in
/-- The literal ambient intersection, moved into its circle, is the two-point subgroup. -/
public theorem circle_pair_eq (d : TwoCoreLocalData Z M) :
    let B := centralizerClosure Z ((d.u : M) : G)
    (residualPairStabilizer M d.t ⊓ B).subgroupOf B =
      twoPoint (M.comap B.subtype) (⟨d.t, t_mem_circle d⟩ : B) := by
  dsimp only
  ext x
  simp only [mem_subgroupOf, mem_inf, residualPairStabilizer, twoPoint, mem_comap,
    LinearGeometry.mem_rightConjugate]
  exact ⟨fun hx => ⟨hx.1.1, hx.1.2⟩, fun hx => ⟨hx, x.property⟩⟩

omit [Finite G] in
/-- The intrinsic two-point centralizer index equals the original ambient relative index. -/
public theorem circle_pair_index_eq (d : TwoCoreLocalData Z M) :
    let B := centralizerClosure Z ((d.u : M) : G)
    let t : B := ⟨d.t, t_mem_circle d⟩
    (centralizer ({t} : Set B)).relIndex (twoPoint (M.comap B.subtype) t) =
      (centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ B) := by
  dsimp only
  rw [← circle_pair_eq d]
  let B := centralizerClosure Z ((d.u : M) : G)
  let t : B := ⟨d.t, t_mem_circle d⟩
  have he : centralizer ({t} : Set B) = (centralizer ({d.t} : Set G)).comap B.subtype := by
    ext x
    simp only [mem_centralizer_singleton_iff, mem_comap]
    exact Subtype.ext_iff
  change (centralizer ({t} : Set B)).relIndex _ = _
  rw [he, relIndex_comap, map_subgroupOf_eq_of_le inf_le_right]


private theorem coatom_of_borel {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (hN : normalizer (P : Set H) ≠ ⊤)
    (hb : IsBorelSubgroup (normalizer (P : Set H))) (hm : IsSimpleBenderGroup H) :
    IsCoatom (normalizer (P : Set H)) := by
  let N := normalizer (P : Set H)
  let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN
  let : MulAction.IsPreprimitive H (H ⧸ N) :=
    MulAction.isPreprimitive_of_is_two_pretransitive
      (simpleBender_borel_coset_twoTransitive hb hm)
  change IsCoatom N
  rw [← MulAction.stabilizer_quotient N]
  exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive _ _

private theorem borel_transport {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (e : H ≃* K) (P : Sylow 2 H)
    (hb : IsBorelSubgroup (normalizer
      (P.mapSurjective (f := e.toMonoidHom) e.surjective : Set K))) :
    IsBorelSubgroup (normalizer (P : Set H)) := by
  have h := hb.map_mulEquiv e.symm
  change IsBorelSubgroup ((normalizer ((P : Subgroup H).map e.toMonoidHom : Set K)).map
    e.symm.toMonoidHom) at h
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id H := by
    ext x
    exact e.symm_apply_apply x
  rwa [← map_equiv_normalizer_eq, map_map, he, map_id] at h

private theorem circle_stabilizer_eq_of_borel
    (h : IsProductDisconnected Z M) (d : TwoCoreLocalData Z M)
    (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M)
    (hb : IsBorelSubgroup (normalizer (P : Set (centralizerClosure Z ((d.u : M) : G)))))
    (hm : IsSimpleBenderGroup (centralizerClosure Z ((d.u : M) : G))) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype = normalizer (P : Set _) := by
  apply circle_stabilizer_eq_of_coatom h d P hPM
  apply coatom_of_borel P _ hb hm
  intro he
  exact circle_stabilizer_ne_top d (top_le_iff.mp (he ▸
    normalizer_le_circle_stabilizer h d P hPM))

open _root_.BenderSuzuki.MatrixGroups

private theorem linear_borel {H : Type*} [Group H] [Finite H] {n : ℕ}
    (e : H ≃* PSL2BinaryMatrixGroup n) (P : Sylow 2 H) :
    IsBorelSubgroup (normalizer (P : Set H)) := by
  apply borel_transport e P
  refine ⟨?_, _, rfl⟩
  exact Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_projective_sylow_normalizer
    2 (BinaryGaloisField n) (by decide) _

private theorem suzuki_borel {H : Type*} [Group H] [Finite H] {m : ℕ}
    (hm : 1 ≤ m) (e : H ≃* SuzukiMatrixGroup m) (P : Sylow 2 H) :
    IsBorelSubgroup (normalizer (P : Set H)) := by
  obtain ⟨f, _, hB⟩ := suzukiSylow_aligned_equiv hm e P
  refine ⟨?_, P, rfl⟩
  rw [← hB]
  let := suzukiBorelSubgroup_isSolvable m hm
  exact Group.isSolvable_of_surjective (f.toMonoidHom.subgroupMap_surjective _)

/-- The original Section 17 action in PSL₂ has Sylow order q, degree q+1 and torus index q−1. -/
public theorem linear_action
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (_ha : ResidualAction Z M) (_hnM : ¬ IsStronglyEmbedded M)
    (_hg : ResidualGeneration Z M)
    (_hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (d : TwoCoreLocalData Z M)
    {n : ℕ} (hn : 2 ≤ n)
    (e : centralizerClosure Z ((d.u : M) : G) ≃* PSL2BinaryMatrixGroup n)
    (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype = normalizer (P : Set _) ∧
      Nat.card P = 2 ^ n ∧
      (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index = Nat.card P + 1 ∧
      (centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) = 2 ^ n - 1 := by
  have h := h.disconnected
  let B := centralizerClosure Z ((d.u : M) : G)
  let t : B := ⟨d.t, t_mem_circle d⟩
  have hm : IsSimpleBenderGroup B := .isPSL2 ⟨n, hn, ⟨e⟩⟩
  have hb := linear_borel e P
  have heq := circle_stabilizer_eq_of_borel h d P hPM hb hm
  have ht : IsInvolution t := IsInvolution.subtype (h.involutions d.t d.t_mem) (t_mem_circle d)
  have htN : t ∉ normalizer (P : Set B) := by
    rw [← heq]
    exact d.t_not_mem
  refine ⟨heq, LinearGeometry.sylow_card (by omega) e P, ?_, ?_⟩
  · rw [heq]
    exact LocalGeometry.borel_index_eq_sylow_card_add_one hb hm P
  · rw [← circle_pair_index_eq d, heq]
    change (centralizer ({t} : Set B)).relIndex
      (twoPoint (normalizer ((P : Subgroup B) : Set B)) t) = _
    have hd := (LinearGeometry.twoPoint_cyclic_card (by omega) e P ht htN).2
    rw [centralizer_relIndex_eq_card_of_odd_inverted _ ?_ t ?_, hd]
    · rw [hd]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one
    · intro x hx
      simpa only [rightConjugateElem, ht.inv_eq_self] using
        LinearGeometry.twoPoint_inverted e P ht htN hx

/-- The original Suzuki action has Sylow order q² and degree q²+1 at the same odd source exponent. -/
public theorem suzuki_action
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (_ha : ResidualAction Z M) (_hnM : ¬ IsStronglyEmbedded M)
    (_hg : ResidualGeneration Z M)
    (_hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (d : TwoCoreLocalData Z M)
    {n m : ℕ} (_hn : 2 ≤ n) (hm : 1 ≤ m) (hnm : n = 2*m+1)
    (e : centralizerClosure Z ((d.u : M) : G) ≃* SuzukiMatrixGroup m)
    (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype = normalizer (P : Set _) ∧
      Nat.card P = (2 ^ n) ^ 2 ∧
      (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index = Nat.card P + 1 ∧
      (centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) = 2 ^ n - 1 := by
  subst n
  have h := h.disconnected
  let B := centralizerClosure Z ((d.u : M) : G)
  let t : B := ⟨d.t, t_mem_circle d⟩
  have hmodel : IsSimpleBenderGroup B := .isSuzuki ⟨m, hm, ⟨e⟩⟩
  have hb := suzuki_borel hm e P
  have heq := circle_stabilizer_eq_of_borel h d P hPM hb hmodel
  have ht : IsInvolution t := IsInvolution.subtype (h.involutions d.t d.t_mem) (t_mem_circle d)
  have htN : t ∉ normalizer (P : Set B) := by
    rw [← heq]
    exact d.t_not_mem
  refine ⟨heq, suzukiSylow_card hm e P, ?_, ?_⟩
  · rw [heq]
    exact LocalGeometry.borel_index_eq_sylow_card_add_one hb hmodel P
  · rw [← circle_pair_index_eq d, heq]
    change (centralizer ({t} : Set B)).relIndex (twoPoint (normalizer (P : Set B)) t) = _
    obtain ⟨_, hd, hi, _⟩ := suzuki_twoPoint_geometry hm e P t ht htN
    rw [centralizer_relIndex_eq_card_of_odd_inverted _ ?_ t ?_, hd]
    · rw [hd]
      exact Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one
    · intro x hx
      simpa only [rightConjugateElem, ht.inv_eq_self] using hi x hx

private theorem eq_normalizer_of_central_image
    {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]
    (f : H →* K) (hf : Function.Surjective f) (hk : f.ker ≤ center H)
    (P : Sylow 2 H) (A : Subgroup H) (hA : A ≠ ⊤)
    (hNA : normalizer (P : Set H) ≤ A)
    (hc : IsCoatom (normalizer (P.mapSurjective hf : Set K))) :
    A = normalizer (P : Set H) := by
  have hkA : f.ker ≤ A := hk.trans ((center_le_normalizer _).trans hNA)
  have hpre : (A.map f).comap f = A := comap_map_eq_self hkA
  have hproper : A.map f ≠ ⊤ := by
    intro he
    apply hA
    rw [← hpre, he, comap_top]
  have hNA' : normalizer (P.mapSurjective hf : Set K) ≤ A.map f := by
    change normalizer ((P : Subgroup H).map f : Set K) ≤ A.map f
    rw [← P.normalizer_map_surjective f hf]
    exact map_mono hNA
  rw [← hpre, (hc.le_iff_eq hproper).mp hNA']
  exact P.normalizer_comap_of_central_kernel f hf hk

private theorem centralizer_index_of_card_factor {H : Type*} [Group H] [Finite H]
    (D : Subgroup H) (t : H) {k : ℕ}
    (hcard : Nat.card D = k * Nat.card (D ⊓ centralizer ({t} : Set H) : Subgroup H)) :
    (centralizer ({t} : Set H)).relIndex D = k := by
  have hc : Nat.card ((centralizer ({t} : Set H)).subgroupOf D) =
      Nat.card (D ⊓ centralizer ({t} : Set H) : Subgroup H) := by
    have he := Nat.card_congr (subgroupOfEquivOfLe
      (show D ⊓ centralizer ({t} : Set H) ≤ D from inf_le_left)).toEquiv
    rwa [inf_subgroupOf_left] at he
  have hm := ((centralizer ({t} : Set H)).subgroupOf D).index_mul_card
  change (centralizer ({t} : Set H)).relIndex D * _ = _ at hm
  rw [hc, hcard] at hm
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hm

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

private theorem projective_sylow_card {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hc : Nat.card E = (2 ^ n)^2)
    (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) : Nat.card P = (2^n)^3 := by
  rw [Nat.card_congr (Sylow.equiv P (HermitianForm.EvenTwoRank.rootSylow J hJ (by omega) hc hf)).toEquiv]
  exact HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup_card J hJ _ hc hf

open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport

/-- The original PSU₃ action has Sylow order q³, degree q³+1 and torus index q−1, for any Hermitian form. -/
public theorem projective_unitary_action
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (_ha : ResidualAction Z M) (_hnM : ¬ IsStronglyEmbedded M)
    (_hg : ResidualGeneration Z M)
    (_hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (d : TwoCoreLocalData Z M)
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2 ^ n)^2)
    (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : centralizerClosure Z ((d.u : M) : G) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype = normalizer (P : Set _) ∧
      Nat.card P = (2^n)^3 ∧
      (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index = Nat.card P + 1 ∧
      (centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) = 2^n-1 := by
  have h := h.disconnected
  obtain ⟨f⟩ := exists_projectiveEquiv J (2^n) hc hf
  let e' := e.trans f
  let B := centralizerClosure Z ((d.u : M) : G)
  let t : B := ⟨d.t, t_mem_circle d⟩
  let Q := P.mapSurjective (f := e'.toMonoidHom) e'.surjective
  have hm : IsSimpleBenderGroup B :=
    .isPSU3 ⟨n, hn, E, inferInstance, inferInstance, standardForm J, rfl, hc, hf, ⟨e'⟩⟩
  have hb := borel_transport e' P (unitary_projective_borel (standardForm J) hn hc hf rfl Q)
  have heq := circle_stabilizer_eq_of_borel h d P hPM hb hm
  have ht : IsInvolution t := IsInvolution.subtype (h.involutions d.t d.t_mem) (t_mem_circle d)
  have htN : t ∉ normalizer (P : Set B) := by rw [← heq]; exact d.t_not_mem
  have hP : Nat.card P = (2^n)^3 := by
    rw [Nat.card_congr ((P : Subgroup B).equivMapOfInjective e'.toMonoidHom e'.injective).toEquiv]
    exact projective_sylow_card (standardForm J) hn rfl hc hf Q
  refine ⟨heq, hP, ?_, ?_⟩
  · rw [heq]
    exact LocalGeometry.borel_index_eq_sylow_card_add_one hb hm P
  · rw [← circle_pair_index_eq d, heq]
    obtain ⟨_, hd, _, _, _, _, hct⟩ := unitary_projective_tori_of_equiv
      (standardForm J) hn rfl hc hf e' P t ht htN
    apply centralizer_index_of_card_factor
    rw [hd, hct]
    have hfac : (2^n)^2 - 1 = (2^n-1) * (2^n+1) := by
      simpa [mul_comm] using Nat.sq_sub_sq (2^n) 1
    rw [hfac, Nat.mul_div_assoc _ (Nat.gcd_dvd_right 3 _)]

/-- The SU₃ action retains its scalar center and still has Sylow order q³, degree q³+1 and torus index q−1. -/
public theorem special_unitary_action
    (h : MinimalCounterexample Z M) (_r : SimpleReduction Z M)
    (_ha : ResidualAction Z M) (_hnM : ¬ IsStronglyEmbedded M)
    (_hg : ResidualGeneration Z M)
    (_hlocal : ∀ Y : Subgroup G, closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (d : TwoCoreLocalData Z M)
    {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card E = (2 ^ n)^2)
    (hf : Nat.card {x : E // J.conj x = x} = 2^n)
    (e : centralizerClosure Z ((d.u : M) : G) ≃* J.specialSubgroup)
    (P : Sylow 2 (centralizerClosure Z ((d.u : M) : G)))
    (hPM : (P : Subgroup _).map (centralizerClosure Z ((d.u : M) : G)).subtype ≤ M) :
    M.comap (centralizerClosure Z ((d.u : M) : G)).subtype = normalizer (P : Set _) ∧
      Nat.card P = (2^n)^3 ∧
      (M.comap (centralizerClosure Z ((d.u : M) : G)).subtype).index = Nat.card P + 1 ∧
      (centralizer ({d.t} : Set G)).relIndex
        (residualPairStabilizer M d.t ⊓ centralizerClosure Z ((d.u : M) : G)) = 2^n-1 := by
  have h := h.disconnected
  obtain ⟨C, hC⟩ := exists_standard_basis J (2^n) hc hf
  let J' := standardForm J
  let e' := e.trans (specialEquiv J C hC)
  let B := centralizerClosure Z ((d.u : M) : G)
  let t : B := ⟨d.t, t_mem_circle d⟩
  let f := J'.specialToProjective.comp e'.toMonoidHom
  have hsurj : Function.Surjective f := J'.specialToProjective_surjective.comp e'.surjective
  have hk : f.ker ≤ center B := by
    intro x hx
    have hx' : e' x ∈ center J'.specialSubgroup := J'.specialToProjective_ker_le_center hx
    rw [mem_center_iff] at hx' ⊢
    intro y
    apply e'.injective
    simpa only [map_mul] using hx' (e' y)
  let Q := P.mapSurjective hsurj
  have hbQ := unitary_projective_borel J' hn hc hf rfl Q
  let A := M.comap B.subtype
  have hNA := normalizer_le_circle_stabilizer h d P hPM
  have hkA : f.ker ≤ A := hk.trans ((center_le_normalizer _).trans hNA)
  have hproper : A.map f ≠ ⊤ := by
    intro he
    apply circle_stabilizer_ne_top d
    change A = ⊤
    rw [← comap_map_eq_self hkA, he, comap_top]
  have hNQ : normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J')) ≤ A.map f := by
    change normalizer ((P : Subgroup B).map f : Set _) ≤ A.map f
    rw [← P.normalizer_map_surjective f hsurj]
    exact map_mono hNA
  have hm : IsSimpleBenderGroup (ProjectiveSpecialUnitaryMatrixGroup J') :=
    .isPSU3 ⟨n, hn, E, inferInstance, inferInstance, J', rfl, hc, hf, ⟨MulEquiv.refl _⟩⟩
  have hcoatom := coatom_of_borel Q (fun he => hproper (top_le_iff.mp (he ▸ hNQ))) hbQ hm
  have heq : A = normalizer (P : Set B) :=
    eq_normalizer_of_central_image f hsurj hk P A (circle_stabilizer_ne_top d) hNA hcoatom
  have hP : Nat.card P = (2^n)^3 := by
    let S := P.mapSurjective (f := e'.toMonoidHom) e'.surjective
    rw [Nat.card_congr ((P : Subgroup B).equivMapOfInjective e'.toMonoidHom e'.injective).toEquiv]
    change Nat.card S = _
    rw [Nat.card_congr (HermitianForm.SylowOmega.specialSylowEquivProjective J' S).toEquiv]
    exact projective_sylow_card J' hn rfl hc hf _
  have ht : IsInvolution t := IsInvolution.subtype (h.involutions d.t d.t_mem) (t_mem_circle d)
  have htN : t ∉ normalizer (P : Set B) := by rw [← heq]; exact d.t_not_mem
  refine ⟨heq, hP, ?_, ?_⟩
  · change A.index = Nat.card P + 1
    rw [← A.index_map_eq hsurj hkA, heq, P.normalizer_map_surjective f hsurj]
    change (normalizer (Q : Set (ProjectiveSpecialUnitaryMatrixGroup J'))).index = _
    rw [LocalGeometry.psu3_borel_index J' hn rfl hc hf hbQ, hP]
  · rw [← circle_pair_index_eq d]
    change (centralizer ({t} : Set B)).relIndex (twoPoint A t) = _
    rw [heq]
    obtain ⟨_, hd, _, _, _, _, hct⟩ := unitary_special_tori_of_equiv
      J' hn rfl hc hf e' P t ht htN
    apply centralizer_index_of_card_factor
    rw [hd, hct]
    simpa [mul_comm] using Nat.sq_sub_sq (2^n) 1

end BenderSuzuki.ZD.Section17.ModelAction
