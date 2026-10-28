module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Quotients
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The literal index-two normalizer extension in J.2.7

The centralizer quotient embeds canonically as the specified centralizer
image in the normalizer quotient. Its kernel, range and evaluation equations
retain the original B and both original quotient maps. Conjugation on B makes
this image normal. When |B| = 3, an involution inverting B realizes the full
automizer of order two, and its image generates the normalizer quotient over
the centralizer image.

This constructs the extension from an actual inverter. The source construction
of that inverter and the distinction between the direct product and Aut(A6)
remain separate obligations; neither is assumed to hold by a source theorem here.

Source: Aschbacher–Smith, J.2.7(3), printed p.436 (PDF p.447).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The original centralizer maps to the normalizer quotient by inclusion. -/
noncomputable def centralizerToNormalizer : c.GB →* c.NormalizerQuotient :=
  c.normalizerQuotientMap.comp (inclusion c.GB_le_NB)

/-- The kernel is exactly the original restricted cubic subgroup. -/
theorem centralizerToNormalizer_ker : c.centralizerToNormalizer.ker = c.cubicKernel := by
  ext x
  change c.normalizerQuotientMap (inclusion c.GB_le_NB x) = 1 ↔ (x : G) ∈ c.B
  exact QuotientGroup.eq_one_iff _

/-- The range is the specified centralizer image, without a change of marking. -/
theorem centralizerToNormalizer_range : c.centralizerToNormalizer.range = c.centralizerImage := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨inclusion c.GB_le_NB y, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The canonical first-isomorphism identification of the two cubic quotient models. -/
noncomputable def cubicEquivCentralizerImage : c.CubicQuotient ≃* c.centralizerImage :=
  (QuotientGroup.quotientMulEquivOfEq c.centralizerToNormalizer_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange c.centralizerToNormalizer).trans
      (MulEquiv.subgroupCongr c.centralizerToNormalizer_range))

/-- The identification commutes with the literal quotient maps. -/
theorem cubicEquivCentralizerImage_mk (x : c.GB) :
    (c.cubicEquivCentralizerImage (c.cubicQuotientMap x) : c.NormalizerQuotient) =
      c.normalizerQuotientMap (inclusion c.GB_le_NB x) := rfl

instance centralizerInNormalizer_normal : (c.GB.subgroupOf c.NB).Normal := by
  rw [← c.B.normalizerMonoidHom_ker]
  infer_instance

instance centralizerImage_normal : c.centralizerImage.Normal :=
  (c.centralizerInNormalizer_normal).map _ c.normalizerQuotientMap_surjective

/-- Pulling the image back recovers the full centralizer inside the normalizer. -/
theorem centralizerImage_comap (hB : Nat.card c.B = 3) :
    c.centralizerImage.comap c.normalizerQuotientMap = c.GB.subgroupOf c.NB := by
  change ((c.GB.subgroupOf c.NB).map c.normalizerQuotientMap).comap _ = _
  rw [comap_map_eq, c.normalizerQuotientMap_ker, sup_of_le_left]
  exact fun x hx => c.B_le_GB_of_card hB hx

/-- A noncentral normalizer element realizes the full automizer of a group of order three. -/
theorem centralizerImage_index_of_noncentral
    (hB : Nat.card c.B = 3) (u : c.NB) (hu : (u : G) ∉ c.GB) :
    c.centralizerImage.index = 2 := by
  let : IsCyclic c.B := isCyclic_of_prime_card hB
  have hd := card_dvd_of_injective _ (QuotientGroup.kerLift_injective c.B.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker, ← index, IsCyclic.card_mulAut, hB] at hd
  have hd' : (c.GB.subgroupOf c.NB).index ∣ 2 := by
    simpa only [Nat.totient_prime (by decide : Nat.Prime 3)] using hd
  have hn : (c.GB.subgroupOf c.NB).index ≠ 1 := by
    intro he
    have ht := index_eq_one.mp he
    apply hu
    change u ∈ c.GB.subgroupOf c.NB
    rw [ht]
    trivial
  have hi : (c.GB.subgroupOf c.NB).index = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hd' |>.resolve_left hn
  rw [← c.centralizerImage_comap hB, index_comap_of_surjective _ c.normalizerQuotientMap_surjective] at hi
  exact hi


/-- Inversion on the original subgroup, using left conjugation. -/
def InvertsB (u : G) : Prop := ∀ b ∈ c.B, u*b*u⁻¹ = b⁻¹

/-- The local inverter-transport conclusion to be constructed from the Ru2 action.
It keeps the transporting element in H and the inverted subgroup equal to B. -/
def InverterTransport : Prop :=
  ∀ i ∈ d.toTypeRuSetup.K, i ∉ d.toTypeRuSetup.Q → orderOf i = 2 →
    ∃ h ∈ d.toTypeRuSetup.H, c.InvertsB (h*i*h⁻¹)

/-- An inverter normalizes the original finite subgroup. -/
theorem mem_NB_of_inverts {u : G} (hu : c.InvertsB u) : u ∈ c.NB := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro y ⟨b, hb, rfl⟩
    change u*b*u⁻¹ ∈ c.B
    rw [hu b hb]
    exact c.B.inv_mem hb
  · rw [card_map_of_injective (K := c.B) (MulAut.conj u).injective]

/-- Inversion on a subgroup of order three is nontrivial. -/
theorem not_mem_GB_of_inverts (hB : Nat.card c.B = 3)
    {u : G} (hu : c.InvertsB u) : u ∉ c.GB := by
  intro huC
  let : Nontrivial c.B := Finite.one_lt_card_iff_nontrivial.mp (by rw [hB]; decide)
  obtain ⟨b, hb⟩ := exists_ne (1 : c.B)
  have hb2 : b ^ 2 = 1 := by
    apply Subtype.ext
    change (b : G) ^ 2 = 1
    have he : (b : G) = (b : G)⁻¹ := by
      calc
        (b : G) = u * (b : G) * u⁻¹ := by rw [← huC b b.property]; simp [mul_assoc]
        _ = (b : G)⁻¹ := hu b b.property
    calc
      (b : G) ^ 2 = (b : G) * b := pow_two _
      _ = (b : G)⁻¹ * b := congrArg (fun a : G => a * b) he
      _ = 1 := inv_mul_cancel _
  have hd3 : orderOf b ∣ 3 := hB ▸ orderOf_dvd_natCard b
  have hd2 := orderOf_dvd_of_pow_eq_one hb2
  exact hb (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 2) hd3 hd2))

/-- An actual involutory inverter gives the index-two extension and its generator. -/
theorem normalizer_extension_of_inverter (hB : Nat.card c.B = 3)
    (u : G) (hu : c.InvertsB u) (hu2 : orderOf u = 2) :
    let v : c.NB := ⟨u, c.mem_NB_of_inverts hu⟩
    orderOf (c.normalizerQuotientMap v) = 2 ∧
    c.centralizerImage.index = 2 ∧
    c.centralizerImage ⊔ zpowers (c.normalizerQuotientMap v) = ⊤ := by
  let v : c.NB := ⟨u, c.mem_NB_of_inverts hu⟩
  have hn : u ∉ c.GB := c.not_mem_GB_of_inverts hB hu
  have hi := c.centralizerImage_index_of_noncentral hB v hn
  have hv : c.normalizerQuotientMap v ∉ c.centralizerImage := by
    intro hv
    have hm : v ∈ c.centralizerImage.comap c.normalizerQuotientMap := hv
    rw [c.centralizerImage_comap hB] at hm
    exact hn hm
  refine ⟨orderOf_eq_prime ?_ ?_, hi, ?_⟩
  · rw [← map_pow]
    have hv2 : v ^ 2 = 1 := Subtype.ext (hu2 ▸ pow_orderOf_eq_one u)
    rw [hv2, map_one]
  · intro he
    exact hv (he ▸ c.centralizerImage.one_mem)
  · apply top_unique
    intro y _
    by_cases hy : y ∈ c.centralizerImage
    · exact mem_sup_left hy
    · have hyv : y * (c.normalizerQuotientMap v)⁻¹ ∈ c.centralizerImage := by
        rw [c.centralizerImage.mul_mem_iff_of_index_two hi, inv_mem_iff]
        exact iff_of_false hy hv
      have hm := (c.centralizerImage ⊔ zpowers (c.normalizerQuotientMap v)).mul_mem
        (mem_sup_left hyv) (mem_sup_right (mem_zpowers _))
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
