module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCentral
public import Theory.SpecificGroups.Triality.BinaryCubicInversion

/-!
# Inverting the actual escaping cubic in the binary-triality branch

Keep the original cubic inside the left Cartan and containing C-component.
The same marking puts its image in the central parabolic of binary triality.
The literal map from the component to its image in Y/O₂(Y) has two-group
kernel; the original Sylow intersection maps onto the positive unipotent
subgroup. The central local-factor S₃ quotient therefore constructs an
inverter upstairs, inside that original Sylow intersection.

An inverter in L would belong to T∩L. Since the cubic normalizes T∩L,
its commutator with such an inverter would put the cubic in a two-group.
Thus the constructed inverter lies outside L. This does not exclude an
outer action on L, and does not identify the original left field degree
with the residual PSL₂(8) degree.

The universal reduction and Chapter12 application retain every preceding
exclusion, both Hall conditions, the original module and quotient maps.
Binary triality, paired J₁ and the remaining normal containing rows still
require the original ambient exclusion and classification arguments.
Source: Aschbacher--Smith 5.1.12--13, printed pp.635--638 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- A cubic in the left Borel cannot be inverted by an element of T∩L. -/
theorem CartanPair.cubic_inverter_not_mem_left
    {T : Sylow 2 G} {L H A B D : Subgroup G}
    (c : CartanPair T L H A B) (hDA : D ≤ A) (hD : Nat.card D = 3)
    {t : G} (ht : t ∈ (T : Subgroup G))
    (hinv : ∀ d ∈ D, t*d*t⁻¹=d⁻¹) : t ∉ L := by
  intro htL
  have hDT : D ≤ (T : Subgroup G) := by
    intro d hd
    have hdn : d ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
      (c.left_le (hDA hd)).2
    have hh := ((T : Subgroup G) ⊓ L).mul_mem (show t ∈ (T : Subgroup G) ⊓ L from ⟨ht,htL⟩)
      (mem_normalizer_iff.mp hdn t⁻¹ |>.mp
        (((T : Subgroup G) ⊓ L).inv_mem ⟨ht,htL⟩))
    have he : t*(d*t⁻¹*d⁻¹) = d⁻¹*d⁻¹ := by rw [←mul_assoc,←mul_assoc,hinv d hd]
    rw [he] at hh
    have hp : d^3=1 := by
      have hc := pow_card_eq_one' (x := (⟨d,hd⟩ : D))
      rw [hD] at hc
      exact congrArg Subtype.val hc
    have hd2 : d*d = d⁻¹ := eq_inv_iff_mul_eq_one.mpr (by simpa [pow_succ] using hp)
    have hi : d⁻¹*d⁻¹=d := by rw [←mul_inv_rev,hd2,inv_inv]
    rw [hi] at hh
    exact hh.1
  have hdvd := card_dvd_of_le hDT
  obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
  rw [hD,hk] at hdvd
  exact (by decide : (3:ℕ) ≠ 2)
    (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three Nat.prime_two hdvd)

namespace LocalSieve
/-- The already constructed original cubic is inverted by an element of
the original Sylow inside the same containing component. -/
theorem binaryTriality_cubic_inverted
    {T : Sylow 2 G} {L W H A B K Y D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C))
    (hDA : D ≤ A) (hDC : D ≤ C.map Y.subtype) (hD : Nat.card D = 3) :
    ∃ t ∈ (T : Subgroup G) ⊓ C.map Y.subtype, t ∉ L ∧
      ∀ d ∈ D, t*d*t⁻¹=d⁻¹ := by
  obtain ⟨_,hCn⟩ := binaryTriality_seed_eq_residual_and_normal h.qtke hKH hH.1.1.2
    hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨e,hmark,_,hcases⟩ := binaryTriality_escape_central_placement h hH hgen c
    hKH hK hKT horbit hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let J := (A.subgroupOf Y).map q ⊔ ((T : Subgroup G).subgroupOf Y).map q
  let f : C →* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one :=
    e.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := e.surjective.comp (q.subgroupMap_surjective C)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hTY := hH.1.1.2.trans hY.2
  let S0 := T.subtype hTY
  let := hCn
  obtain ⟨S,hS⟩ := S0.exists_subgroupOf_eq_of_normal C
  have hSle : (S : Subgroup C).map f ≤ Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) := by
    rw [←hmark]
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨q.subgroupMap C x,?_,rfl⟩
    exact mem_map_of_mem q (show x.val ∈ (T : Subgroup G).subgroupOf Y from by rw [hS] at hx; exact hx)
  have hSeq : (S : Subgroup C).map f = Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) :=
    ((S.mapSurjective hf).is_maximal'
      (Triality.Standard.Parabolics.unipotent_isPGroup_binary _ rfl) hSle).symm
  have hDY : D ≤ Y := hDC.trans (map_subtype_le C)
  have hDYC : D.subgroupOf Y ≤ C := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hDC hx
    exact (show y=x from Subtype.ext he) ▸ hy
  let DC := (D.subgroupOf Y).subgroupOf C
  have hDCc : Nat.card DC = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDYC).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDY).toEquiv,hD]
  have hDI : DC.map f ≤ (J.subgroupOf Cbar).map e.toMonoidHom := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨q.subgroupMap C x,?_,rfl⟩
    exact mem_sup_left (mem_map_of_mem q (hDA hx))
  have hIP : (J.subgroupOf Cbar).map e.toMonoidHom ≤
      Triality.Standard.Parabolics.parabolic
        (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .central := by
    rcases hcases with he | he
    · rw [he]
      exact Triality.Standard.Parabolics.localFactor_le_parabolic _ _
    · exact he.le
  obtain ⟨t,ht,hti⟩ := Triality.Standard.BinarySolvableEscape.cubic_inverted_of_two_kernel
    f hf hk S hSeq DC hDCc (hDI.trans hIP)
  have htT : (t.val : G) ∈ (T : Subgroup G) := by rw [hS] at ht; exact ht
  have hi : ∀ d ∈ D, (t.val:G)*d*(t.val:G)⁻¹=d⁻¹ := by
    intro d hd
    let y : Y := ⟨d,hDY hd⟩
    let x : C := ⟨y,hDYC hd⟩
    exact congrArg (fun z : C => (z.val:G)) (hti x hd)
  exact ⟨t.val,⟨htT,mem_map_of_mem Y.subtype t.property⟩,
    c.cubic_inverter_not_mem_left hDA hD htT hi,hi⟩
end LocalSieve
open Chapter1.Section02.LocalModels

/-- Retain every preceding exclusion and invert the actual escaping cubic
from the original Sylow inside its same binary-triality component. -/
theorem localCartan_escape_seed_binaryInverted_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          Even n ∧
          3 ∣ Nat.card ((A.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y))) ∧
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          BinaryArmsPlacement T H Y C ∧ BinaryArmsAction T H A B Y C ∧
          BinaryCentralPlacement T H A Y C ∧
          ∃ D : Subgroup G, D ≤ A ∧ D ≤ C.map Y.subtype ∧ Nat.card D = 3 ∧
            ¬ D ≤ normalizer (residual H : Set G) ∧
            ∃ t ∈ (T : Subgroup G) ⊓ C.map Y.subtype, t ∉ L ∧
              ∀ d ∈ D, t*d*t⁻¹=d⁻¹) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hpair⟩ :=
    localCartan_escape_seed_binaryCubic_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,?_,hprime,h25,hpair⟩
  intro hm
  obtain ⟨hEven,hdiv,hKR,hCn,ht,hsection,hplacement,haction,hcentral,D,hDA,hDC,hD,hDn⟩ := hrank hm
  exact ⟨hEven,hdiv,hKR,hCn,ht,hsection,hplacement,haction,hcentral,D,hDA,hDC,hD,hDn,
    LocalSieve.binaryTriality_cubic_inverted h hH hgen c hKH hKL hKT hR
      hY hescape C hC hKC ht hDA hDC hD⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
