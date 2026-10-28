module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Geometry

/-!
# Nontrivial displacement of the second layer by an escaping two-subgroup

The original nonzero residual triple forces the full actor to act
nontrivially on U/Z. Its two-core fixes this quotient. A two-subgroup
escaping that core has reflection image in the genuine S3 quotient;
conjugates of a reflection generate S3, so it cannot fix U/Z.

Pulling the selected original layer back through the midpoint transporter
and then mapping forward gives the lower bound two with denominator
Z_middle. Normality is used only in the finite local actor, and the
nonzero triple retains the original tilded residual.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8)(3), printed p.906,
and the midpoint comparison on printed p.907. This is a lower bound,
not the reverse comparison or a construction of a natural moving factor.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
open Incident.Pairing.Transport.Natural.Kernel

private theorem reflection_conjugates : ∀ x y : BinaryS3.Actor,
    x ^ 2 = 1 → x ≠ 1 → ∃ a b : BinaryS3.Actor,
      y = a * x * a⁻¹ * (b * x * b⁻¹) ∨ y = a * x * a⁻¹ ∨ y = 1 := by
  decide +kernel

private theorem normal_eq_top_of_reflection (N : Subgroup BinaryS3.Actor) [N.Normal]
    (x : BinaryS3.Actor) (hx : x ∈ N) (hx2 : x ^ 2 = 1) (hxn : x ≠ 1) : N = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨a, b, h | h | h⟩ := reflection_conjugates x y hx2 hxn
  · rw [h]
    exact N.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx a)
      (Subgroup.Normal.conj_mem inferInstance x hx b)
  · rw [h]
    exact Subgroup.Normal.conj_mem inferInstance x hx a
  · rw [h]
    exact N.one_mem

private theorem reflection_of_two (H : Subgroup BinaryS3.Actor) (hH : IsPGroup 2 H)
    (x : BinaryS3.Actor) (hx : x ∈ H) : x ^ 2 = 1 := by
  have orders : ∀ y : BinaryS3.Actor, y ^ 2 = 1 ∨ y ^ 3 = 1 := by decide +kernel
  rcases orders x with h | h
  · exact h
  · have hc := hH.orderOf_coprime (by decide : Nat.Coprime 2 3) (⟨x, hx⟩ : H)
    have hd : orderOf (⟨x, hx⟩ : H) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (show (⟨x, hx⟩ : H) ^ 3 = 1 from Subtype.ext h)
    have he : (⟨x, hx⟩ : H) = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd)
    have he' : x = 1 := congrArg Subtype.val he
    simp only [he', one_pow]

private theorem actor_commutator_le_of_escaping_two {G : Type*} [Group G]
    (P K U Z E : Subgroup G)
    (π : P →* BinaryS3.Actor) (hπ : Function.Surjective π)
    (hker : π.ker = K.subgroupOf P)
    (hPZ : P ≤ normalizer Z) (hPU : P ≤ normalizer U)
    (hKU : ⁅K,U⁆ ≤ Z) (hEP : E ≤ P) (hE : IsPGroup 2 E)
    (hnot : ¬ E ≤ K) (hEU : ⁅E,U⁆ ≤ Z) : ⁅P,U⁆ ≤ Z := by
  let C := commutatorPreimage P U Z
  have hCP : C ≤ P := commutatorPreimage_le _ _ _
  let : (C.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer
    (commutatorPreimage_normalized P U Z P hPZ P.le_normalizer hPU hPZ)
  have hEC : E ≤ C := le_commutatorPreimage hEP hEU
  have hKC : K.subgroupOf P ≤ C.subgroupOf P := by
    intro k hk
    exact (le_commutatorPreimage (show K ⊓ P ≤ P from inf_le_right)
      ((commutator_mono inf_le_left le_rfl).trans hKU)) ⟨hk, k.property⟩
  let N := (C.subgroupOf P).map π
  let : N.Normal := Subgroup.Normal.map inferInstance π hπ
  obtain ⟨e, he, hen⟩ := SetLike.not_le_iff_exists.mp hnot
  let ep : P := ⟨e, hEP he⟩
  have hxn : π ep ≠ 1 := by
    intro h
    have hk : ep ∈ π.ker := h
    rw [hker] at hk
    exact hen hk
  have hx2 : (π ep) ^ 2 = 1 := reflection_of_two ((E.subgroupOf P).map π)
    (hE.comap_subtype.map π) _ (mem_map_of_mem π he)
  have htop : N = ⊤ := normal_eq_top_of_reflection N (π ep)
    (mem_map_of_mem π (hEC he)) hx2 hxn
  have hPC : P ≤ C := by
    intro x hx
    have hxN : π (⟨x,hx⟩ : P) ∈ N := htop ▸ mem_top _
    obtain ⟨c, hc, hcx⟩ := hxN
    have hdiff : c⁻¹ * (⟨x,hx⟩ : P) ∈ π.ker := by
      change π (c⁻¹ * (⟨x,hx⟩ : P)) = 1
      rw [map_mul, map_inv, hcx, inv_mul_cancel]
    rw [hker] at hdiff
    have hh := (C.subgroupOf P).mul_mem hc (hKC hdiff)
    simpa only [mul_inv_cancel_left, mem_subgroupOf] using hh
  exact (commutator_mono hPC le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hPZ)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem local_barProjection (source : LocalSource L R) (i : Bool) (d : M) :
    ∃ π : localFlagActor source i d →* BinaryS3.Actor,
      Function.Surjective π ∧
      π.ker = (localFlagKernel source i d).subgroupOf (localFlagActor source i d) := by
  obtain ⟨π, hπ, hk⟩ := exists_barProjection source i
  let e := MulAut.conj (embedM R d)
  let j := e.subgroupMap (flagParabolic source i)
  refine ⟨π.comp j.symm.toMonoidHom, hπ.comp j.symm.surjective, ?_⟩
  ext x
  change π (j.symm x) = 1 ↔ (x : FreeAmalgam R) ∈ (flagKernel source i).map e.toMonoidHom
  rw [← MonoidHom.mem_ker, hk, mem_map_equiv]
  rfl

/-- Every escaping two-subgroup moves the second layer modulo the original Z. -/
theorem second_commutator_not_le_Z_of_escape
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (d : M)
    (E : Subgroup (FreeAmalgam R)) (hEP : E ≤ localFlagActor source (!i) d)
    (hE : IsPGroup 2 E) (hnot : ¬ E ≤ localFlagKernel source (!i) d) :
    ¬ ⁅E, secondFlagLayer source i d⁆ ≤ Z R (alpha R) := by
  intro h
  obtain ⟨π, hπ, hk⟩ := local_barProjection source (!i) d
  have hh := actor_commutator_le_of_escaping_two
    (localFlagActor source (!i) d) (localFlagKernel source (!i) d)
    (secondFlagLayer source i d) (Z R (alpha R)) E π hπ hk
    ((localFlagActor_le_stabilizer source (!i) d).trans (Z_normalized R _))
    (Incident.secondFlagLayer_normalized source geometry common.large_distance i d)
    (by rw [commutator_comm]; exact
      Incident.secondFlagLayer_commutator_le_Z source geometry common.large_distance i d)
    hEP hE hnot h
  rw [commutator_comm] at hh
  exact Y_core_residual_triple_not_le source geometry i p d
    ((commutator_mono (Y_core_le_second source geometry common early i hkernel d)
      (map_mono (flagResidual_le source (!i)))).trans hh)

/-- The actual transported second-layer commutator has index at least two
modulo Z_middle at any selected escaping actor. -/
theorem middle_second_commutator_index_ge_two
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M)
    (hactor : secondFlagLayer source i p.delta0 ≤
      (localFlagActor source (!i) e).map t.conjugation.toMonoidHom)
    (hescape : ¬ secondFlagLayer source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom) :
    2 ≤ (Z R p.middle).relIndex
      ⁅secondFlagLayer source i p.delta0,
        (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ := by
  let E := secondFlagLayer source i p.delta0
  let A := E.map t.conjugation.symm.toMonoidHom
  have hback : A.map t.conjugation.toMonoidHom = E :=
    (map_symm_eq_iff_map_eq A (e := t.conjugation)).mp rfl
  have hAP : A ≤ localFlagActor source (!i) e := by
    apply (map_le_map_iff_of_injective (f := t.conjugation.toMonoidHom)
      t.conjugation.injective).mp
    rw [hback]
    exact hactor
  have hp : IsPGroup 2 A :=
    ((Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le
      ((secondFlagLayer_le_radius source i p.delta0).trans
        (V_le_Q geometry common.large_distance _ rfl))).map _
  have hn : ¬ A ≤ localFlagKernel source (!i) e := by
    intro h
    have hh := map_mono (f := t.conjugation.toMonoidHom) h
    rw [hback] at hh
    exact hescape hh
  have hnon := second_commutator_not_le_Z_of_escape source geometry common early
    i hkernel p e A hAP hp hn
  have hnon' : ¬ ⁅E,(secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ ≤
      Z R p.middle := by
    intro h
    apply hnon
    apply (map_le_map_iff_of_injective (f := t.conjugation.toMonoidHom)
      t.conjugation.injective).mp
    rw [map_commutator, hback, t.map_Z_alpha]
    exact h
  let := Incident.secondFlagLayer_finite source geometry common.large_distance i e
  let : Finite ((secondFlagLayer source i e).map t.conjugation.toMonoidHom) :=
    Finite.of_equiv (secondFlagLayer source i e)
      (t.conjugation.subgroupMap (secondFlagLayer source i e)).toEquiv
  have hcomm : ⁅E,(secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ ≤
      (secondFlagLayer source i e).map t.conjugation.toMonoidHom :=
    le_normalizer_iff_commutator_le_right.mp (hactor.trans
      ((map_mono (Incident.secondFlagLayer_normalized source geometry
        common.large_distance i e)).trans (le_normalizer_map _)))
  let : Finite (⁅E,(secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ :
      Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hcomm) (inclusion_injective _)
  have hpos : (Z R p.middle).relIndex
      ⁅E,(secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ ≠ 0 :=
    index_ne_zero_of_finite
  have hne : (Z R p.middle).relIndex
      ⁅E,(secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆ ≠ 1 :=
    fun h => hnon' (relIndex_eq_one.mp h)
  change 2 ≤ (Z R p.middle).relIndex
    ⁅E,(secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
