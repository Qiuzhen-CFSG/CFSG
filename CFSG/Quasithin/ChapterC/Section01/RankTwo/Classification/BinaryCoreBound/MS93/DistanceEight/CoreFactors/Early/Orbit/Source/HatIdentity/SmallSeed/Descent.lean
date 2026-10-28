module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed.Failure

/-!
# Descent for the actual hat-fixed seed

The third product containment makes D Z_a normal in the local group. Its
commutator with Q_a is an invariant proper subgroup of the natural
eight-group, so it vanishes. The elementary seed then lies in Z_a; the
literal common-edge intersection places it in Z_b and finishes the hat
identity. This uses only the smaller hat-fixed seed, not a full-radius
splitting.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(i), printed p.898.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
private theorem span_le_of_normalized {A P K : Subgroup (FreeAmalgam R)}
    (hA : A ≤ K) (hn : P ≤ normalizer K) : conjugatesIn A P ≤ K := by
  apply iSup_le
  intro g
  rintro _ ⟨x, hx, rfl⟩
  exact le_normalizer_iff.mp hn g⁻¹ (P.inv_mem g.property) x (hA hx)

private theorem normalizes_commutator {G : Type*} [Group G] (S A B : Subgroup G)
    (hA : S ≤ normalizer A) (hB : S ≤ normalizer B) :
    S ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hg),
    mem_normalizer_iff_map_conj_eq.mp (hB hg)]

private theorem commutator_sup_central {G : Type*} [Group G] (A C Q : Subgroup G)
    (hA : A ≤ Q) (hC : C ≤ Q) (hc : ⁅C,Q⁆ = ⊥) : ⁅A ⊔ C,Q⁆ = ⁅A,Q⁆ := by
  let f : Bool → Subgroup G := fun b => if b then A else C
  have hf : (⨆ b, f b) = A ⊔ C := by simp [iSup_bool_eq, f]
  have h := commutator_iSup_of_le f Q (by intro b; cases b <;> assumption)
  rw [hf] at h
  simpa [iSup_bool_eq, f, hc] using h

private theorem span_join_Z_normalized [Finite M]
    {a b t f : Vertex R} (hf : color R f = false)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (hproduct : (span R a b t : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    stabilizer R a ≤ normalizer (span R a b t ⊔ Z R a : Subgroup (FreeAmalgam R)) := by
  let D := span R a b t
  let J := D ⊔ Z R a
  have hZG : Z R f ≤ stabilizer R a := le_sup_right.trans hgen.le
  rw [← hgen]
  apply sup_le
  · exact (le_inf (conjugatesIn_normalized _ _)
      ((show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans
        (Z_normalized R a))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · apply le_normalizer_iff.mpr
    intro g hg x hx
    have hn := Z_normalized R a (hZG hg)
    have hmap : J.map (MulAut.conj g).toMonoidHom ≤ J := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨d, hd, rfl⟩
        obtain ⟨z, hz, q, hq, heq⟩ := hproduct hd
        have hqJ : q ∈ J := by
          have hh := J.mul_mem (J.inv_mem (mem_sup_right hz)) (mem_sup_left hd)
          rw [← heq] at hh
          simpa only [inv_mul_cancel_left] using hh
        have hqfix : g * q * g⁻¹ = q := by
          have hc := (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R f hf)) hg q hq
          rw [← hc]
          simp [mul_assoc]
        change g * d * g⁻¹ ∈ J
        rw [← heq]
        have he : g * (z * q) * g⁻¹ = (g * z * g⁻¹) * q := by
          calc
            _ = (g * z * g⁻¹) * (g * q * g⁻¹) := by group
            _ = _ := by rw [hqfix]
        rw [he]
        exact J.mul_mem (mem_sup_right (le_normalizer_iff.mp (Z_normalized R a)
          g (hZG hg) z hz)) hqJ
      · exact (mem_normalizer_iff_map_conj_eq.mp hn).le.trans le_sup_right
    exact hmap (mem_map_of_mem _ hx)

/-- The last paragraph of the D argument: the third containment and the
small commutator force the actual conjugate span into Z at the center. -/
theorem span_le_Z_of_product [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t f : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hf : color R f = false) (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (hsmall : ⁅span R a b t, Q R a⁆ ≤ H R b)
    (hproduct : (span R a b t : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    span R a b t ≤ Z R a := by
  let D := span R a b t
  have hDQ : D ≤ Q R a := (span_le_full hmove.1).trans (span_le_Q earlier hb hmove.1)
  have hZQ : Z R a ≤ Q R a := by rw [← common.X_eq_Z a ha]; exact omegaCenter_le _
  have hnorm : stabilizer R a ≤ normalizer (⁅D,Q R a⁆ : Subgroup (FreeAmalgam R)) := by
    have hn := normalizes_commutator (stabilizer R a) (D ⊔ Z R a) (Q R a)
      (span_join_Z_normalized hf hgen hproduct) (Q_normalized R a)
    rwa [commutator_sup_central D (Z R a) (Q R a) hDQ hZQ (Z_centralizes_Q R a ha)] at hn
  have hHU : H R b ≤ U R a := H_le_neighbor_U common earlier hb hmove
  have hzero : ⁅D,Q R a⁆ = ⊥ := by
    rcases Third.natural_subgroup_dichotomy common ha _ (hsmall.trans hHU) hnorm with h | h
    · exact h
    · have hcard := H_card_le_four common earlier hb
      let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
      let : Finite (H R b) := Finite.of_injective (inclusion hHU) (inclusion_injective hHU)
      have hle : Nat.card (U R a) ≤ Nat.card (H R b) := Nat.card_le_card_of_injective _ (inclusion_injective (h ▸ hsmall))
      rw [common.natural.card_at a ha] at hle
      omega
  have hseed : seed R b a ≤ Z R a := by
    rw [← common.X_eq_Z a ha]
    let := V_elementary_of_four_lt R hb (by rw [earlier.distance]; decide)
    intro x hx
    have hxD := seed_le_span a b t hx
    exact mem_omegaCenter_iff.mpr ⟨hDQ hxD,
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V R b) x ((seed_le_fixedSeed hmove.1 hx).1),
      commutator_eq_bot_iff_le_centralizer.mp hzero hxD⟩
  exact span_le_of_normalized hseed
    ((show relativeNormalizer R a t ≤ stabilizer R a from inf_le_left).trans (Z_normalized R a))



theorem hat_eq_of_product [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a b t f : Vertex R} (ha : color R a = false) (hb : color R b = false)
    (hf : color R f = false) (hat : Adjacent R a t) (hbt : Adjacent R b t)
    (hmove : a ∈ Escape.movingNeighbors geometry b)
    (hgen : relativeNormalizer R a t ⊔ Z R f = stabilizer R a)
    (hsplit : hatV R b a ≤ Vcirc R b ⊔ seed R b a)
    (hsmall : ⁅span R a b t, Q R a⁆ ≤ H R b)
    (hproduct : (span R a b t : Set (FreeAmalgam R)) ⊆
      (Z R a : Set (FreeAmalgam R)) * (Q R f : Set (FreeAmalgam R))) :
    hatV R b a = Vcirc R b ⊔ Z R b := by
  have hDZ := span_le_Z_of_product common earlier ha hb hf hmove hgen hsmall hproduct
  have hseed : seed R b a ≤ Z R b := by
    have h := le_inf ((seed_le_span a b t).trans hDZ)
      ((seed_le_fixedSeed hmove.1).trans (fixedSeed_le_B common hb))
    rw [moving_Z_inf_B common earlier ha hb hat hbt hmove] at h
    exact h.trans (Escape.EdgeTransfer.edge_Z_le b t hb hbt)
  apply le_antisymm (hsplit.trans (sup_le_sup_left hseed _))
  exact sup_le (moving_le_hatV source earlier hb hmove) (Z_le_hatV hb hmove.1)
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.SmallSeed
