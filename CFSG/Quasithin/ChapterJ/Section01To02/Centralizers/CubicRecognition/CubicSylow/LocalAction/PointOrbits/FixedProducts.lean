module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.CubicSylow.LocalAction.Actions
public import Theory.GroupAction.KleinFourFactorization
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.SpecificGroups.AlternatingSix.M10.Action.Extension

/-!
# The actual fixed subgroups and ordered factorization in J.2.7

The two transposition involutions are fused to z. Sylow containment in
H = C_G(z) bounds both fixed subgroups by three. The Brauer–Wielandt
formula for the commuting involutions f and fz forces equality, since
|R| = 27 and C_R(z) = B has order three. The odd-order Klein-four
factorization then gives the literal ordered set product C_R(f) C_R(fz) B.
The original ambient conjugator fusing C_R(f) to B is retained.

Compatibility with the specified M₁₀ also proves that either marked
transposition lift inverts B. No abelian-branch exclusion is used.

Source: Aschbacher–Smith, J.2.7, printed p.437 (PDF p.448).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.PointOrbits
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The subgroup fixed by a specified ambient element. -/
abbrev fixed (R : Sylow 3 c.NB) (t : G) : Subgroup G :=
  ambient c R ⊓ centralizer ({t} : Set G)

theorem fixed_card_le_three (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (R : Sylow 3 c.NB) (t : G) (g : G) (hg : g * t * g⁻¹ = c.z) :
    Nat.card (fixed c R t) ≤ 3 := by
  let C := fixed c R t
  let U := C.map (MulAut.conj g).toMonoidHom
  have hUH : U ≤ d.toTypeRuSetup.H := by
    rintro _ ⟨x, hx, rfl⟩
    rw [c.H_eq_centralizer_z, mem_centralizer_singleton_iff]
    have he : (MulAut.conj g) t = c.z := hg
    simpa only [map_mul, he, MulEquiv.coe_toMonoidHom] using congrArg (MulAut.conj g)
      (mem_centralizer_singleton_iff.mp hx.2)
  have hp : IsPGroup 3 (U.subgroupOf d.toTypeRuSetup.H) :=
    (((ambient_isPGroup c R).of_injective (inclusion (show C ≤ ambient c R from inf_le_left))
      (inclusion_injective _)).map (MulAut.conj g).toMonoidHom).comap_subtype
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hle := card_le_of_le hQ
  have hQP : Nat.card Q = Nat.card P := by
    rw [Q.card_eq_multiplicity, P.card_eq_multiplicity]
  have hPc : Nat.card P = 3 := by
    calc
      Nat.card P = Nat.card ((P : Subgroup d.toTypeRuSetup.H).map
        d.toTypeRuSetup.H.subtype) := (card_map_of_injective
          d.toTypeRuSetup.H.subtype_injective).symm
      _ = 3 := by rw [hP, hB]
  have hUc : Nat.card (U.subgroupOf d.toTypeRuSetup.H) = Nat.card C := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv,
      card_map_of_injective (MulAut.conj g).injective]
  rwa [hUc, hQP, hPc] at hle

theorem action_fixed_card (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (t : TR c R Tplus) :
    Nat.card (action c R Tplus t).fixedSubgroup = Nat.card (fixed c R (t : G)) :=
  Nat.card_congr ((Equiv.subtypeEquivRight (fun x =>
    MulAut.mem_fixedSubgroup (action c R Tplus t) x)).trans (fixedEquiv c R Tplus t))

private theorem action_involutive (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (t : TR c R Tplus) (ht : t ^ 2 = 1) : Function.Involutive (action c R Tplus t) := by
  have he : action c R Tplus t ^ 2 = 1 := by rw [← map_pow, ht, map_one]
  exact fun x => congrArg (fun a : MulAut (ambient c R) => a x) he

/-- Fusion gives upper bounds; the four-group order formula makes both exact. -/
theorem fixed_cards (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (f : TR c R Tplus) (hf : f ^ 2 = 1) (hzT : c.z ∈ TR c R Tplus)
    (hcomm : Commute f (⟨c.z, hzT⟩ : TR c R Tplus))
    (hfusion : ∃ g : G, g * (f : G) * g⁻¹ = c.z)
    (hfusion' : ∃ g : G, g * ((f : G) * c.z) * g⁻¹ = c.z) :
    Nat.card (fixed c R (f : G)) = 3 ∧
      Nat.card (fixed c R ((f : G) * c.z)) = 3 := by
  let z : TR c R Tplus := ⟨c.z, hzT⟩
  have hz2 : z ^ 2 = 1 := Subtype.ext (hz ▸ pow_orderOf_eq_one c.z)
  have hfz : (f * z) ^ 2 = 1 := by rw [hcomm.mul_pow, hf, hz2, one_mul]
  have ha : Commute (action c R Tplus f) (action c R Tplus (f * z)) :=
    (Commute.refl f |>.mul_right hcomm).map (action c R Tplus)
  have hprod : action c R Tplus f * action c R Tplus (f * z) = action c R Tplus z := by
    rw [← map_mul, ← mul_assoc, ← pow_two, hf, one_mul]
  have hodd : Odd (Nat.card (ambient c R)) := by rw [ambient_card c hB e R]; decide
  have hc := Theory.GroupAction.brauerWielandt_fixedSubgroup_card hodd
    (action c R Tplus f) (action c R Tplus (f * z))
    (action_involutive c R Tplus f hf) (action_involutive c R Tplus (f * z) hfz) ha
  rw [ambient_card c hB e R, hprod, action_fixed_card, action_fixed_card,
    action_fixed_card, show (z : G) = c.z from rfl, show fixed c R c.z = c.B from
      centralizer_z_eq c hB P hP R, hB] at hc
  obtain ⟨g, hg⟩ := hfusion
  obtain ⟨g', hg'⟩ := hfusion'
  have hle := fixed_card_le_three c hB P hP R (f : G) g hg
  have hle' := fixed_card_le_three c hB P hP R ((f : G) * c.z) g' hg'
  have hpos : 0 < Nat.card ↥((action c R Tplus f).fixedSubgroup ⊓
      (action c R Tplus (f * z)).fixedSubgroup) := Nat.card_pos
  change 27 * _ ^ 2 = Nat.card (fixed c R (f : G)) *
    Nat.card (fixed c R ((f : G) * c.z)) * 3 at hc
  constructor <;> nlinarith [sq_pos_of_pos hpos]

/-- The ordered product in the source is a setwise product of the actual factors. -/
theorem setwise_product (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (f : TR c R Tplus) (hf : f ^ 2 = 1) (hzT : c.z ∈ TR c R Tplus)
    (hcomm : Commute f (⟨c.z, hzT⟩ : TR c R Tplus)) :
    (ambient c R : Set G) = (fixed c R (f : G) : Set G) *
      (fixed c R ((f : G) * c.z) : Set G) * (c.B : Set G) := by
  let z : TR c R Tplus := ⟨c.z, hzT⟩
  have hz2 : z ^ 2 = 1 := Subtype.ext (hz ▸ pow_orderOf_eq_one c.z)
  have hfz : (f * z) ^ 2 = 1 := by rw [hcomm.mul_pow, hf, hz2, one_mul]
  have ha : Commute (action c R Tplus f) (action c R Tplus (f * z)) :=
    (Commute.refl f |>.mul_right hcomm).map (action c R Tplus)
  have hprod : action c R Tplus f * action c R Tplus (f * z) = action c R Tplus z := by
    rw [← map_mul, ← mul_assoc, ← pow_two, hf, one_mul]
  have hodd : Odd (Nat.card (ambient c R)) := by rw [ambient_card c hB e R]; decide
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, b, v, ha, hb, hv, he⟩ := MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card
      hodd (action c R Tplus f) (action c R Tplus (f * z))
      (action_involutive c R Tplus f hf) (action_involutive c R Tplus (f * z) hfz) ha
      (⟨x, hx⟩ : ambient c R)
    rw [hprod] at hv
    have hva : (v : G) ∈ c.B := by
      rw [← centralizer_z_eq c hB P hP R]
      exact (fixedEquiv c R Tplus z ⟨v, hv⟩).property
    exact Set.mem_mul.mpr ⟨(a : G) * (b : G), Set.mem_mul.mpr
      ⟨a, (fixedEquiv c R Tplus f ⟨a, ha⟩).property,
        b, (fixedEquiv c R Tplus (f * z) ⟨b, hb⟩).property, rfl⟩,
      v, hva, (congrArg Subtype.val he).symm⟩
  · rintro x ⟨ab, ⟨a, ha, b, hb, rfl⟩, v, hv, rfl⟩
    exact (ambient c R).mul_mem ((ambient c R).mul_mem ha.1 hb.1) (B_le c hB R hv)

/-- The actual transposition marking in the given quotient model. -/
def TranspositionMark (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (t : c.NB) : Prop :=
  ∃ u : Equiv.Perm (Fin 6), u.IsSwap ∧
    markedMap c e t = AlternatingSix.ShadowLocal.permutationAction u

/-- A transposition lift lies outside the original centralizer of B. -/
theorem marked_not_mem_GB
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (t : c.NB) (ht : TranspositionMark c e t) : (t : G) ∉ c.GB := by
  obtain ⟨u, hu, he⟩ := ht
  intro h
  apply AlternatingSix.M10.Action.swap_not_mem_extension u hu
  rw [← he, ← hM]
  exact mem_map_of_mem e.toMonoidHom (mem_map_of_mem c.normalizerQuotientMap h)

/-- Compatibility with M₁₀ forces a marked involution to invert the original B. -/
theorem marked_inverts_B (hB : Nat.card c.B = 3)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (t : c.NB) (ht2 : t ^ 2 = 1) (ht : TranspositionMark c e t) :
    ∀ b ∈ c.B, (t : G) * b * (t : G)⁻¹ = b⁻¹ := by
  rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one c.B
    (by rw [hB]; decide) (t : G) (congrArg Subtype.val ht2) t.property with hc | hi
  · exact (marked_not_mem_GB c e hM t ht (fun b hb => (hc b hb).symm)).elim
  · exact hi

/-- A marked transposition cannot have a trivial lift. -/
theorem marked_ne_one
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (t : c.NB) (ht : TranspositionMark c e t) : t ≠ 1 := by
  obtain ⟨u, hu, he⟩ := ht
  intro ht1
  apply AlternatingSix.M10.Action.swap_not_mem_extension u hu
  rw [← he, ht1, map_one]
  exact one_mem _

/-- The embedded center identity gives commutation with the literal z. -/
theorem commute_z_of_center (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB)
    (hcenter : (center (TR c R Tplus)).map (TR c R Tplus).subtype = zpowers c.z)
    (hzT : c.z ∈ TR c R Tplus) (t : TR c R Tplus) :
    Commute t (⟨c.z, hzT⟩ : TR c R Tplus) := by
  have hzmem : c.z ∈ (center (TR c R Tplus)).map (TR c R Tplus).subtype := by
    rw [hcenter]
    exact mem_zpowers c.z
  obtain ⟨v, hv, he⟩ := hzmem
  have hvz : v = (⟨c.z, hzT⟩ : TR c R Tplus) := Subtype.ext he
  rw [← hvz]
  exact (mem_center_iff.mp hv t)

/-- Under primitive marked placement, both fixed groups have order three,
the product is the literal ordered set product, and the first factor is fused to B. -/
theorem marked_fixed_data (hB : Nat.card c.B = 3)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (hz : orderOf c.z = 2)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (h7 : TranspositionFusion c e)
    (R : Sylow 3 c.NB) (Tplus : Sylow 2 c.NB) (r f : TR c R Tplus)
    (hr4 : (r : G) ^ 4 = c.z) (hf : orderOf f = 2)
    (hcenter : (center (TR c R Tplus)).map (TR c R Tplus).subtype = zpowers c.z)
    (ht : TranspositionMark c e (inclusion (TR_le_NB c R Tplus) f))
    (ht' : TranspositionMark c e
      ((inclusion (TR_le_NB c R Tplus) f) * ⟨c.z, c.GB_le_NB c.z_mem_GB⟩)) :
    Nat.card (fixed c R (f : G)) = 3 ∧
      Nat.card (fixed c R ((f : G) * c.z)) = 3 ∧
      (ambient c R : Set G) = (fixed c R (f : G) : Set G) *
        (fixed c R ((f : G) * c.z) : Set G) * (c.B : Set G) ∧
      ∃ g : G, (fixed c R (f : G)).map (MulAut.conj g).toMonoidHom = c.B := by
  have hzT : c.z ∈ TR c R Tplus := hr4 ▸ (TR c R Tplus).pow_mem r.property 4
  let z : TR c R Tplus := ⟨c.z, hzT⟩
  have hz2 : z ^ 2 = 1 := Subtype.ext (hz ▸ pow_orderOf_eq_one c.z)
  have hf2 : f ^ 2 = 1 := hf ▸ pow_orderOf_eq_one f
  have hcomm := commute_z_of_center c R Tplus hcenter hzT f
  have hfz2 : (f * z) ^ 2 = 1 := by rw [hcomm.mul_pow, hf2, hz2, one_mul]
  let j := inclusion (TR_le_NB c R Tplus)
  have hjf : orderOf (j f) = 2 := (orderOf_injective j (inclusion_injective _) f).trans hf
  have hjfz : orderOf (j (f * z)) = 2 := orderOf_eq_prime
    (by rw [← map_pow, hfz2, map_one]) (marked_ne_one c e _ ht')
  obtain ⟨hcf, hcfz⟩ := fixed_cards c hB P hP hz e R Tplus f hf2 hzT hcomm
    (h7 (j f) hjf ht) (h7 (j (f * z)) hjfz ht')
  exact ⟨hcf, hcfz, setwise_product c hB P hP hz e R Tplus f hf2 hzT hcomm,
    centralizer_f_conjugate_B c hB P hP e h7 R (j f) hjf ht hcf⟩

end CFSG.Quasithin.ChapterJ.Centralizers.CubicSylow.LocalAction.PointOrbits
