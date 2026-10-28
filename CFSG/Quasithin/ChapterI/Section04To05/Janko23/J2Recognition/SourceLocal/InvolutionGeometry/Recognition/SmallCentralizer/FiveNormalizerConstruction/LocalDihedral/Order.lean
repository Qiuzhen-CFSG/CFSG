module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConsequences
public import Theory.GroupAction.SubgroupCentralizerCongruence
public import Theory.GroupTheory.CoprimeQuotientNormalizer

/-!
# The order and core intersection of the literal local five-normalizer

Put H = C_G(z) and Q = F*(H). The conjugation action of a Sylow five-subgroup
P on Q gives |C_Q(P)| congruent to 32 modulo five. Its order divides 32,
so it is two or 32. The latter would put P inside C_H(Q) ≤ Q, which is
impossible. Since Q and P have coprime orders, N_Q(P) = C_Q(P) = Z(H).

The quotient map H → H/Q carries N_H(P) onto the normalizer of the image
of P. In the simple quotient of order sixty, the Sylow congruence and
simplicity force that normalizer to have order ten. Thus |N_H(P)| = 20.
This calculation does not yet assert that the extension is dihedral.

Source: Aschbacher, *Sporadic Groups* (1994), §46 and the proof of 47.1,
printed p.260. The quotient and core are the literal source subgroups.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The source Sylow five-subgroup has order five inside H. -/
theorem localFive_card (D : Seed G) (P : Sylow 5 (involutionCentralizer D.z)) :
    Nat.card P = 5 := by
  rw [P.card_eq_multiplicity, D.localType.centralizer_card]
  decide +kernel

/-- The five-subgroup fixes precisely two elements of the extraspecial core. -/
theorem localFive_core_centralizer_card (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z)) :
    Nat.card (localCore D.z ⊓ centralizer (P : Set (involutionCentralizer D.z)) :
      Subgroup (involutionCentralizer D.z)) = 2 := by
  let Q := localCore D.z
  let C := Q ⊓ centralizer (P : Set (involutionCentralizer D.z))
  have hm := card_modEq_card_inf_centralizer (P : Subgroup _) Q P.isPGroup'
    (by rw [normalizer_eq_top]; exact le_top)
  change Nat.card Q % 5 = Nat.card C % 5 at hm
  have hQ : Nat.card Q = 32 := D.localType.core_card
  rw [hQ] at hm
  have hd : Nat.card C ∣ 32 := hQ ▸ card_dvd_of_le (show C ≤ Q from inf_le_left)
  have hn : Nat.card C ≠ 32 := by
    intro hc
    have he : C = Q := eq_of_le_of_card_ge inf_le_left (by omega)
    have hQP : Q ≤ centralizer (P : Set (involutionCentralizer D.z)) := he ▸ inf_le_right
    have hPQ : (P : Subgroup _) ≤ Q :=
      (le_centralizer_iff.mp hQP).trans (centralizer_generalizedFitting_le _)
    have hh := card_dvd_of_le hPQ
    rw [localFive_card, hQ] at hh
    norm_num at hh
  obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Nat.card C ∣ 2^5 from hd)
  change Nat.card C = 2
  interval_cases k <;> norm_num only [Nat.reducePow] at he <;> omega

/-- Coprime orders make every core element normalizing P centralize it. -/
theorem localFive_core_normalizer_eq_centralizer (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z)) :
    localCore D.z ⊓ normalizer (P : Set (involutionCentralizer D.z)) =
      localCore D.z ⊓ centralizer (P : Set (involutionCentralizer D.z)) := by
  let Q := localCore D.z
  let N := Q ⊓ normalizer (P : Set (involutionCentralizer D.z))
  have hdis : Disjoint Q (P : Subgroup _) :=
    IsPGroup.disjoint_of_coprime D.localType.core_isPGroup P.isPGroup' (by decide)
  have hc : ⁅N, (P : Subgroup (involutionCentralizer D.z))⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdis.eq_bot]
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono le_rfl (show N ≤ Q from inf_le_left)).trans
        (le_normalizer_iff_commutator_le_right.mp (by rw [normalizer_eq_top]; exact le_top))
    · exact le_normalizer_iff_commutator_le_right.mp inf_le_right
  exact le_antisymm (le_inf inf_le_left (commutator_eq_bot_iff_le_centralizer.mp hc))
    (inf_le_inf_left _ (centralizer_le_normalizer _))


private theorem five_normalizer_card_of_simple_sixty
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (hH : Nat.card H = 60) (A : Subgroup H) (hA : Nat.card A = 5) :
    Nat.card (normalizer (A : Set H)) = 10 := by
  let N := normalizer (A : Set H)
  have hd : Nat.card N ∣ 60 := hH ▸ N.card_subgroup_dvd_card
  have hm := Sylow.card_normalizer_modEq_card (p := 5) (n := 1)
    (show Nat.card A = 5^1 from hA)
  change Nat.card N % 25 = Nat.card H % 25 at hm
  rw [hH] at hm
  have hn : Nat.card N ≠ 60 := by
    intro he
    have htop : N = ⊤ := N.eq_top_of_card_eq (he.trans hH.symm)
    have : A.Normal := normalizer_eq_top_iff.mp htop
    rcases this.eq_bot_or_eq_top with he | he
    · simp only [he, card_bot] at hA
      omega
    · simp only [he, card_top, hH] at hA
      omega
  change Nat.card N = 10
  have hmem := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show (60 : ℕ).divisors = {1,2,3,4,5,6,10,12,15,20,30,60} by decide] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  omega

/-- The literal local normalizer has order twenty. -/
theorem localFive_normalizer_card (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z)) :
    Nat.card (normalizer (P : Set (involutionCentralizer D.z))) = 20 := by
  let Q := localCore D.z
  let N := normalizer (P : Set (involutionCentralizer D.z))
  let π := QuotientGroup.mk' Q
  have hdis : Disjoint Q (P : Subgroup _) :=
    IsPGroup.disjoint_of_coprime D.localType.core_isPGroup P.isPGroup' (by decide)
  have hmapP : Nat.card ((P : Subgroup _).map π) = 5 := by
    have he := relIndex_ker (K := (P : Subgroup _)) π
    rw [QuotientGroup.ker_mk', ← inf_relIndex_right, hdis.eq_bot, relIndex_bot_left] at he
    exact he.symm.trans (localFive_card D P)
  have hmapN : Nat.card (N.map π) = 10 := by
    let : Fact (IsPGroup 5 (P : Subgroup (involutionCentralizer D.z))) := ⟨P.isPGroup'⟩
    have hn : N.map π = normalizer (((P : Subgroup (involutionCentralizer D.z)).map π) :
        Set (involutionCentralizer D.z ⧸ Q)) :=
      (normalizer_map_quotient_eq_map_normalizer 5
        (P : Subgroup (involutionCentralizer D.z)) Q inferInstance
        (by change Nat.Coprime 5 (Nat.card (localCore D.z)); rw [D.localType.core_card]; decide)).symm
    rw [hn]
    let : IsSimpleGroup (involutionCentralizer D.z ⧸ Q) := D.localType.quotient_isSimpleGroup
    exact five_normalizer_card_of_simple_sixty D.localType.quotient_card _ hmapP
  have hker : Nat.card (Q ⊓ N : Subgroup _) = 2 := by
    rw [show Q ⊓ N = Q ⊓ centralizer (P : Set (involutionCentralizer D.z)) from
      localFive_core_normalizer_eq_centralizer D P]
    exact localFive_core_centralizer_card D P
  have hi := relIndex_ker (K := N) π
  rw [QuotientGroup.ker_mk', hmapN] at hi
  have hc := relIndex_mul_relIndex (⊥ : Subgroup (involutionCentralizer D.z))
    (Q ⊓ N) N bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_right, hi, hker] at hc
  exact hc.symm


/-- The two-element kernel of the local normalizer in H/Q is precisely Z(H). -/
theorem localFive_core_normalizer_eq_center (D : Seed G)
    (P : Sylow 5 (involutionCentralizer D.z)) :
    localCore D.z ⊓ normalizer (P : Set (involutionCentralizer D.z)) =
      center (involutionCentralizer D.z) := by
  rw [localFive_core_normalizer_eq_centralizer D P]
  have hz : Nat.card (center (involutionCentralizer D.z)) = 2 := by
    rw [← card_map_of_injective (K := center (involutionCentralizer D.z))
      (involutionCentralizer D.z).subtype_injective,
      D.localType.centralizer_center_image, Nat.card_zpowers, D.localType.involution]
  exact (eq_of_le_of_card_ge
    (le_inf HTypeAt.center_le_core (center_le_centralizer _))
    (by rw [localFive_core_centralizer_card D P, hz])).symm


end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
