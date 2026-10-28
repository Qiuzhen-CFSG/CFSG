module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.BarMarking.Action
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic.Cosets
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The original flag and its barred pair stabilizer

The fifteen nonzero vectors of the natural four-space are its duad vectors.
The nonidentity element of the order-two flag V₁ therefore determines an
actual unordered pair. Conjugation fixes that vector precisely when it
normalizes V₁, proving the pair stabilizer identity before and after taking
the source centralizer quotient.

The two source residual conventions agree because LT/L is a two-group:
the two-residual of N_LT(V₁) is contained in N_L(V₁) and remains two-perfect.
The Sylow supplement then gives L₁T = N_LT(V₁).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, p.877; Notation 13.3.3, p.885; 13.7, pp.935–936;
and 13.8.6(5), p.948. No stabilizer equality is assumed in the construction.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking
open BinaryPermutation
variable {G : Type*} [Group G]
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open BinaryPermutation.SixPairsQuadratic

private theorem normalizer_two_iff (A : Subgroup G) (z : A) (hz : z ≠ 1)
    (hzuniq : ∀ a : A, a ≠ 1 → a = z) (g : G) :
    g ∈ normalizer (A : Set G) ↔ g * (z : G) * g⁻¹ = z := by
  constructor
  · intro hg
    let z' : A := ⟨g * (z : G) * g⁻¹, (hg z).mp z.property⟩
    have hn : z' ≠ 1 := by
      intro h
      apply hz
      apply Subtype.ext
      have h' : g * (z : G) * g⁻¹ = 1 := congrArg Subtype.val h
      have hh := congrArg (fun a => g⁻¹ * a * g) h'
      simpa [mul_assoc] using hh
    exact congrArg Subtype.val (hzuniq z' hn)
  · intro hg
    apply centralizer_le_normalizer (A : Set G)
    intro a ha
    by_cases h : (⟨a, ha⟩ : A) = 1
    · have haone : a = 1 := congrArg Subtype.val h
      simp [haone]
    · have haz : a = z := congrArg Subtype.val (hzuniq ⟨a, ha⟩ h)
      rw [haz]
      exact (mul_inv_eq_iff_eq_mul.mp hg).symm

/-- Every order-two flag determines its actual coordinate duad. -/
theorem exists_pair_of_flag (P V A : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : P ≤ normalizer (V : Set G)) (hAV : A ≤ V) (hcard : Nat.card A = 2)
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 6))
    (f : P →* Equiv.Perm (Fin 6))
    (he : ∀ p v, e (conjugationRepresentation P V hn p v) =
      naturalRepresentation (Fin 6) (f p) (e v)) :
    ∃ s : Pair, ∀ p : P,
      (p : G) ∈ normalizer (A : Set G) ↔ pairPerm (f p) s = s := by
  obtain ⟨z, hz, hzu⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  let v : Additive V := Additive.ofMul ⟨z, hAV z.property⟩
  have hv : e v ≠ 0 := by
    intro h
    have hv0 := e.map_eq_zero_iff.mp h
    apply hz
    apply Subtype.ext
    exact congrArg (fun u : Additive V => (u.toMul : G)) hv0
  obtain ⟨d, hd⟩ := (vector_cases (e v)).resolve_left hv
  let s : Pair := ⟨{d.val.1, d.val.2}, by simp [ne_of_lt d.property]⟩
  refine ⟨s, fun p => ?_⟩
  rw [normalizer_two_iff A z hz hzu]
  have hvfix : (p : G) * (z : G) * (p : G)⁻¹ = z ↔
      naturalRepresentation (Fin 6) (f p) (e v) = e v := by
    rw [← he]
    rw [e.injective.eq_iff]
    constructor
    · intro h
      apply Additive.toMul.injective
      exact Subtype.ext h
    · intro h
      exact congrArg (fun u : Additive V => (u.toMul : G)) h
  rw [hvfix, hd]
  change naturalRepresentation (Fin 6) (f p) (pairVector d.val.1 d.val.2) =
    pairVector d.val.1 d.val.2 ↔ _
  rw [pairVector_map, pairVector_eq_iff ((f p).injective.ne (ne_of_lt d.property))
    (ne_of_lt d.property)]
  change ({f p d.val.1, f p d.val.2} : Finset (Fin 6)) = {d.val.1, d.val.2} ↔ _
  rw [Subtype.ext_iff]
  change _ ↔ ({d.val.1, d.val.2} : Finset (Fin 6)).map (f p).toEmbedding = {d.val.1, d.val.2}
  simp only [Finset.map_insert, Finset.map_singleton, Equiv.toEmbedding_apply]

/-- The source residual together with T is exactly the relative flag normalizer. -/
theorem residual_normalizer_sup_sylow [Finite G] (P A : Subgroup G) (T : Sylow 2 G)
    (hTP : (T : Subgroup G) ≤ P) (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    (pResidual 2 ↥(P ⊓ normalizer (A : Set G))).map
      (P ⊓ normalizer (A : Set G)).subtype ⊔ (T : Subgroup G) =
      P ⊓ normalizer (A : Set G) := by
  have hT : (T : Subgroup G) ≤ P ⊓ normalizer (A : Set G) := le_inf hTP hTA
  have h := congrArg (fun B : Subgroup ↥(P ⊓ normalizer (A : Set G)) =>
    B.map (P ⊓ normalizer (A : Set G)).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hT))
  simpa only [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hT,
    ← MonoidHom.range_eq_map, range_subtype] using h
/-- The marked normalizer descends to the actual barred parabolic. -/
theorem bar_pair_stabilizer (P V A R : Subgroup G) (hn : P ≤ normalizer (V : Set G))
    (hAV : A ≤ V) (hR : R = P ⊓ normalizer (A : Set G))
    (f : P →* Equiv.Perm (Fin 6)) (hker : f.ker = actorKernel P V)
    (s : Pair) (hs : ∀ p : P, (p : G) ∈ normalizer (A : Set G) ↔ pairPerm (f p) s = s) :
    letI := actorKernel_normal P V hn
    ∀ a : P ⧸ actorKernel P V,
      a ∈ (R.subgroupOf P).map (QuotientGroup.mk' (actorKernel P V)) ↔
        pairPerm (barHom P V hn f hker a) s = s := by
  let := actorKernel_normal P V hn
  let q := QuotientGroup.mk' (actorKernel P V)
  have hNR : actorKernel P V ≤ R.subgroupOf P := by
    intro p hp
    rw [hR]
    exact ⟨p.property, centralizer_le_normalizer (A : Set G) ((centralizer_le hAV) hp)⟩
  have hpre : ((R.subgroupOf P).map q).comap q = R.subgroupOf P := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNR]
  intro a
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (actorKernel P V) a
  have hm : q p ∈ (R.subgroupOf P).map q ↔ (p : G) ∈ R :=
    Iff.of_eq (congrArg (fun B : Subgroup P => p ∈ B) hpre)
  rw [barHom_mk, hm, hR]
  exact (and_iff_right p.property).trans (hs p)
/-- The two residual conventions in 13.2.1 and 13.3.3 agree: adjoining
normalizing two-elements does not change the residual of a flag normalizer. -/
theorem normalizer_residual_eq [Finite G] (L A T : Subgroup G)
    (hT : IsPGroup 2 T) (hTL : T ≤ normalizer (L : Set G)) :
    (pResidual 2 ↥((L ⊔ T) ⊓ normalizer (A : Set G))).map
        ((L ⊔ T) ⊓ normalizer (A : Set G)).subtype =
      (pResidual 2 ↥(L ⊓ normalizer (A : Set G))).map
        (L ⊓ normalizer (A : Set G)).subtype := by
  let P := L ⊔ T
  let M := P ⊓ normalizer (A : Set G)
  let X := L ⊓ normalizer (A : Set G)
  let R := (pResidual 2 M).map M.subtype
  have hLP : L ≤ P := le_sup_left
  let : (L.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  have hgen : L.subgroupOf P ⊔ T.subgroupOf P = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hLP,
      map_subgroupOf_eq_of_le (show T ≤ P from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 (P ⧸ L.subgroupOf P) :=
    isPGroup_quotient_of_sup_eq_top _ _ hT.comap_subtype hgen
  have hOL : pResidual 2 P ≤ L.subgroupOf P := sInf_le ⟨inferInstance, hp⟩
  have hRL : R ≤ L := by
    have hh := (embedded_pResidual_mono 2 (show M ≤ P from inf_le_left)).trans
      (map_mono (f := P.subtype) hOL)
    rwa [map_subgroupOf_eq_of_le hLP] at hh
  have hRX : R ≤ X := le_inf hRL ((map_subtype_le _).trans inf_le_right)
  apply le_antisymm
  · have hrp : IsPPerfect 2 (R.subgroupOf X) :=
      (isPPerfect_embedded_pResidual 2 M).of_surjective
        (subgroupOfEquivOfLe hRX).symm.toMonoidHom (subgroupOfEquivOfLe hRX).symm.surjective
    have hh := map_mono (f := X.subtype) (le_pResidual_of_isPPerfect (R.subgroupOf X) hrp)
    rwa [map_subgroupOf_eq_of_le hRX] at hh
  · exact embedded_pResidual_mono 2 (inf_le_inf hLP le_rfl)

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed.BarMarking

end
