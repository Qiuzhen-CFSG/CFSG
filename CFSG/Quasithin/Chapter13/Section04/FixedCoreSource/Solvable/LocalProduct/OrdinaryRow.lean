module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.PairQuotient
public import Theory.SpecificGroups.AlternatingSix.CubicPreimageRank
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The ordinary row from the rank of the original centralizer residual

The five-dimensional marking descends through the literal L/O₂(L).
Its central kernel has order one or three. In the latter case the
preimage of a cubic in the marked vector stabilizer contains E₉.
The map from C_L(z) to this preimage has a two-group kernel, so it
preserves three-rank. Taking O^{3′} also preserves three-rank. Thus
m₃(L₁) ≤ 1 excludes the cubic cover and proves L/O₂(L) ≅ A₆.

The same maps prove the {2,3}-order and cubic divisor of L₁ in both
covering rows. This removes the ordinary-row assumption formerly needed
to obtain those numerical premises. OrdinaryProduct applies these results
to the actual centralizer and the existing Thompson-factor construction.

Source: Aschbacher–Smith, 13.4.8, printed pp.904–905; the original
five-dimensional augmentation core and O^{3′}(C_L(z)) are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 BinaryNaturalDual.VectorStabilizers Stellmacher
open Chapter14.Section03.FaithfulSource Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def actionProjection {D : ChosenModule T L V} (m : CoreMarking D) :
    L →* alternatingGroup (Fin 6) :=
  m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))

omit [Finite G] in
private theorem actionProjection_ker {D : ChosenModule T L V} (m : CoreMarking D) :
    (actionProjection m).ker = centralCore L := by
  ext l
  change m.quotient (QuotientGroup.mk' (centralCore L) l) = 1 ↔ l ∈ centralCore L
  rw [m.quotient.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff l

private def coverProjection {D : ChosenModule T L V} (m : CoreMarking D) :
    (L ⧸ pCore 2 L) →* alternatingGroup (Fin 6) :=
  QuotientGroup.lift (pCore 2 L) (actionProjection m) (by
    intro l hl
    rw [actionProjection_ker]
    change QuotientGroup.mk' (pCore 2 L) l ∈ center _
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
    rw [he]
    exact one_mem _)

omit [Finite G] in
private theorem coverProjection_surjective {D : ChosenModule T L V} (m : CoreMarking D) :
    Function.Surjective (coverProjection m) := by
  intro a
  obtain ⟨b,rfl⟩ := m.quotient.surjective a
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) b
  exact ⟨QuotientGroup.mk' (pCore 2 L) l,rfl⟩

omit [Finite G] in
private theorem coverProjection_ker {D : ChosenModule T L V} (m : CoreMarking D) :
    (coverProjection m).ker = center (L ⧸ pCore 2 L) := by
  ext x
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) x
  change actionProjection m l = 1 ↔ QuotientGroup.mk' (pCore 2 L) l ∈ center _
  change l ∈ (actionProjection m).ker ↔ l ∈ centralCore L
  rw [actionProjection_ker]

private theorem coverProjection_kernel_card {D : ChosenModule T L V} (m : CoreMarking D)
    [IsQuasisimple (L ⧸ pCore 2 L)] :
    Nat.card (coverProjection m).ker = 1 ∨ Nat.card (coverProjection m).ker = 3 := by
  let E := L ⧸ pCore 2 L
  let e : (E ⧸ center E) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq (coverProjection_ker m).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (coverProjection_surjective m))
  have hn : ¬ 2 ∣ Nat.card (center E) :=
    PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) (center E) le_rfl
  have ho : Odd (Nat.card (center E)) :=
    Nat.not_even_iff_odd.mp (fun he => hn (even_iff_two_dvd.mp he))
  rw [coverProjection_ker]
  exact (GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) e ho).imp_right
    (fun h => h.2)

omit [Finite G] in
private theorem actionProjection_mem_stabilizer {D : ChosenModule T L V} (m : CoreMarking D)
    (z : V) (l : L) :
    actionProjection m l ∈ BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd ↔
      l.val ∈ centralizer ({z.val} : Set G) := by
  change BinaryPermutation.coreRepresentation (Fin 6)
    (m.quotient (QuotientGroup.mk' (centralCore L) l)).val (m.coordinate z).toAdd =
      (m.coordinate z).toAdd ↔ _
  rw [← m.equivariant l z]
  rw [Multiplicative.toAdd.injective.eq_iff,m.coordinate.injective.eq_iff,Subtype.ext_iff]
  change l.val * z.val * l.val⁻¹ = z.val ↔ _
  rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]

private def stabilizerProjection {D : ChosenModule T L V} (m : CoreMarking D) (z : V) :
    (L ⊓ centralizer ({z.val} : Set G) : Subgroup G) →*
      (BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd).comap
        (coverProjection m) :=
  ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion inf_le_left)).codRestrict _
    (fun c => (actionProjection_mem_stabilizer m z (inclusion inf_le_left c)).mpr c.property.2)

omit [Finite G] in
private theorem stabilizerProjection_surjective {D : ChosenModule T L V} (m : CoreMarking D)
    (z : V) : Function.Surjective (stabilizerProjection m z) := by
  intro a
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) a.val
  have hs : actionProjection m l ∈
      BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd := by
    change coverProjection m (QuotientGroup.mk' (pCore 2 L) l) ∈ _
    rw [hl]
    exact a.property
  exact ⟨⟨l.val,l.property,(actionProjection_mem_stabilizer m z l).mp hs⟩,Subtype.ext hl⟩

omit [Finite G] in
private theorem stabilizerProjection_kernel_two {D : ChosenModule T L V} (m : CoreMarking D)
    (z : V) : IsPGroup 2 (stabilizerProjection m z).ker := by
  have hk : (stabilizerProjection m z).ker = (pCore 2 L).comap (inclusion inf_le_left) := by
    ext x
    change (⟨QuotientGroup.mk' (pCore 2 L) (inclusion inf_le_left x),_⟩ :
      (BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd).comap
        (coverProjection m)) = 1 ↔ inclusion inf_le_left x ∈ pCore 2 L
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  rw [hk]
  exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)

omit [Finite G] in
private theorem stabilizer_card {D : ChosenModule T L V} (m : CoreMarking D)
    (z : V) (hz : z.val ∉ centralizer (L : Set G)) :
    ∃ n : ℕ, Nat.card (BinaryPermutation.SixCoreStabilizer.stabilizer
      (m.coordinate z).toAdd) = 2 ^ n * 3 := by
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd
  have hfix : ¬ ∀ a : alternatingGroup (Fin 6),
      BinaryPermutation.alternatingCoreRepresentation (Fin 6) a (m.coordinate z).toAdd =
        (m.coordinate z).toAdd := by
    intro h
    exact hz ((m.mem_fixed_iff z).mpr
      ((BinaryPermutation.core_fixed_iff_constant (by simp) _).mp h))
  obtain ⟨e⟩ := BinaryPermutation.SixCoreStabilizer.quotient_equiv (m.coordinate z).toAdd hfix
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := S)).exists_card_eq
  have hq : Nat.card (S ⧸ pCore 2 S) = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  refine ⟨n+1,?_⟩
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 S),hq,hn,pow_succ]
  ring

/-- The literal prime-to-three residual retains the three-rank of C_L(z). -/
theorem firstCentralizerResidual_threeRank (z : G) :
    primeRank 3 (firstCentralizerResidual L z) =
      primeRank 3 (L ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  rw [firstCentralizerResidual_eq,
    ← primeRank_congr 3 ((primeToResidual 3 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ centralizer ({z} : Set G)).subtype (L ⊓ centralizer ({z} : Set G)).subtype_injective)]
  exact primeRank_eq_of_not_dvd_index _
    (Nat.prime_three.coprime_iff_not_dvd.mp (primeToResidual_index_coprime 3))

/-- Cubic rank one excludes the genuine triple-cover row at the original vector. -/
theorem ordinary_of_firstCentralizerResidual_threeRank
    (D : ChosenModule T L V) (m : CoreMarking D) [IsQuasisimple (L ⧸ pCore 2 L)]
    (z : V) (hz : z.val ∉ centralizer (L : Set G))
    (hr : primeRank 3 (firstCentralizerResidual L z.val) ≤ 1) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd
  let f := stabilizerProjection m z
  rcases coverProjection_kernel_card m with hc | hc
  · exact ⟨MulEquiv.ofBijective (coverProjection m)
      ⟨(MonoidHom.ker_eq_bot_iff _).mp ((eq_bot_iff_card _).mpr hc),
        coverProjection_surjective m⟩⟩
  · obtain ⟨n,hn⟩ := stabilizer_card m z hz
    have hr2 := Theory.SpecificGroups.AlternatingSix.CubicPreimageRank.two_le_rank_preimage
      (coverProjection m) (coverProjection_surjective m) (coverProjection_ker m ▸ le_rfl) hc
      S (hn ▸ dvd_mul_left 3 (2^n))
    have hcop : Nat.Coprime 3 (Nat.card f.ker) := by
      obtain ⟨k,hk⟩ := (stabilizerProjection_kernel_two m z).exists_card_eq
      rw [hk]
      exact (by decide : Nat.Coprime 3 2).pow_right k
    have he := primeRank_eq_of_surjective_of_coprime 3 f
      (stabilizerProjection_surjective m z) hcop
    rw [firstCentralizerResidual_threeRank] at hr
    change primeRank 3 (L ⊓ centralizer ({z.val} : Set G) : Subgroup G) = _ at he
    have bad : 2 ≤ 1 := hr2.trans (he ▸ hr)
    omega

/-- Both central-cover rows give the residual's {2,3}-order and its cubic divisor. -/
theorem firstCentralizerResidual_order_of_marking
    (D : ChosenModule T L V) (m : CoreMarking D) [IsQuasisimple (L ⧸ pCore 2 L)]
    (z : V) (hz : z.val ∉ centralizer (L : Set G)) :
    (∃ a b : ℕ, Nat.card (firstCentralizerResidual L z.val) ∣ 2 ^ a * 3 ^ b) ∧
      3 ∣ Nat.card (firstCentralizerResidual L z.val) := by
  let C := L ⊓ centralizer ({z.val} : Set G)
  let S := BinaryPermutation.SixCoreStabilizer.stabilizer (m.coordinate z).toAdd
  let q := coverProjection m
  let P := S.comap q
  let f := stabilizerProjection m z
  obtain ⟨n,hn⟩ := stabilizer_card m z hz
  have hP : Nat.card P = Nat.card S * Nat.card q.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup (q.ker.subgroupOf P),
      card_quotient_subgroupOf_comap_eq (f := q) (hf := coverProjection_surjective m) (H := S),
      Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap (f := q) (H := S))).toEquiv]
  obtain ⟨k,hk⟩ := (stabilizerProjection_kernel_two m z).exists_card_eq
  have hC : Nat.card C = Nat.card P * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
        (stabilizerProjection_surjective m z)).toEquiv]
  have hcard : ∃ a b : ℕ, Nat.card C = 2 ^ a * 3 ^ (b+1) := by
    rw [hC,hP,hn,hk]
    rcases coverProjection_kernel_card m with hc | hc
    · refine ⟨n+k,0,?_⟩
      rw [hc,pow_add]
      ring
    · refine ⟨n+k,1,?_⟩
      rw [hc,pow_add]
      ring
  obtain ⟨a,b,hcard⟩ := hcard
  have hA : Nat.card (firstCentralizerResidual L z.val) = Nat.card (primeToResidual 3 C) := by
    rw [firstCentralizerResidual_eq,card_map_of_injective]
    exact C.subtype_injective
  rw [hA]
  refine ⟨⟨a,b+1,?_⟩,?_⟩
  · simpa only [← hcard] using (primeToResidual 3 C).card_subgroup_dvd_card
  · have h3 : 3 ∣ Nat.card C := by rw [hcard]; exact dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) _
    rw [← (primeToResidual 3 C).card_mul_index] at h3
    exact (Nat.prime_three.dvd_mul.mp h3).resolve_right
      (Nat.prime_three.coprime_iff_not_dvd.mp (primeToResidual_index_coprime 3))
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
