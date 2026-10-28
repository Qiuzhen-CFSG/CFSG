module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality
/-!
# The external cubic character and the span centralizer

B need not lie in H. Its two-core lies in O₂(H) as soon as it lies in H,
and it centralizes the H-span of V by characteristic normalization.
The literal quotient character has kernel described by [h,B] ≤ O₂(B).
If q fixes F and its character is trivial, its action commutes with a cubic
b on V. It therefore fixes Fᵇ as well. A complementary pair F,Fᵇ proves
Q₁ ∩ ker χ = C_G(V). Normality then promotes the intersection with O₂(H)
to the actual centralizer of the entire conjugate span.

The local spanning premise is constructed in OrthogonalSplitting. These
lemmas preserve the earlier conditional SourceData API without requiring
its unavailable B ≤ H field. Source: the repaired argument for
Aschbacher–Smith 15.3.68(2), combined manuscript (1 March 2004), pp.1154–1155;
the local action input is 15.3.66(5).
-/

@[expose] public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G]

/-- The ambient image of the kernel of the literal B/O₂(B) action. -/
noncomputable abbrev characterKernel (H B : Subgroup G) (hHB : H ≤ normalizer (B : Set G)) : Subgroup G :=
  (quotientAction H B hHB).ker.map H.subtype

private theorem normalizes_centralizer {H D : Subgroup G}
    (h : H ≤ normalizer (D : Set G)) : H ≤ normalizer (centralizer (D : Set G) : Set G) :=
  h.trans ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (D : Set G))).mp
    inferInstance)

/-- Containment of the local core suffices; the external group B need not lie in H. -/
theorem external_twoCore_le_core (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (hB0H : ambientTwoCore B ≤ H) :
    ambientTwoCore B ≤ ambientTwoCore H :=
  le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 B) hB0H
    (hHB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))

/-- Characteristic normalization extends centralization from V to its actual H-span. -/
theorem external_twoCore_centralizes_span (H B V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hB0V : ambientTwoCore B ≤ centralizer (V : Set G)) :
    ambientTwoCore B ≤ centralizer (conjugateSpanBy V H : Set G) := by
  apply le_centralizer_iff.mp
  exact conjugateSpanBy_le (le_centralizer_iff.mp hB0V)
    (normalizes_centralizer
      (hHB.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))))

/-- The quotient character vanishes exactly when every commutator with B lies in B₀. -/
theorem mem_characterKernel_iff (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) (h : G) (hh : h ∈ H) :
    h ∈ characterKernel H B hHB ↔ ∀ b ∈ B, ⁅h,b⁆ ∈ ambientTwoCore B := by
  have hm : h ∈ characterKernel H B hHB ↔
      (⟨h,hh⟩ : H) ∈ (quotientAction H B hHB).ker := by
    constructor
    · rintro ⟨x,hx,he⟩
      exact (show x = ⟨h,hh⟩ from Subtype.ext he) ▸ hx
    · intro hx
      exact mem_map.mpr ⟨⟨h,hh⟩,hx,rfl⟩
  rw [hm, quotientAction_mem_ker_iff]
  constructor
  · intro hx b hb
    have he := QuotientGroup.eq_iff_div_mem.mp (hx ⟨b,hb⟩)
    simpa only [localTwoCore, mem_subgroupOf, Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk,
      commutatorElement_def] using he
  · intro hx b
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [localTwoCore, mem_subgroupOf, Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subtype.coe_mk,
      commutatorElement_def] using hx b b.property

/-- The ambient character kernel is normal relative to H. -/
theorem characterKernel_normalized (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    H ≤ normalizer (characterKernel H B hHB : Set G) := by
  intro h hh
  apply (quotientAction H B hHB).ker.le_normalizer_map H.subtype
  exact mem_map.mpr ⟨⟨h,hh⟩,by rw [normalizer_eq_top]; trivial,rfl⟩

private theorem fixes_conjugate {V F : Subgroup G} {q b : G}
    (hFV : F ≤ V) (hb : b ∈ normalizer (V : Set G))
    (hq : q ∈ centralizer (F : Set G))
    (hc : ⁅q,b⁆ ∈ centralizer (V : Set G)) :
    q ∈ centralizer (F.map (MulAut.conj b).toMonoidHom : Set G) := by
  apply mem_centralizer_iff.mpr
  rintro x ⟨f,hf,rfl⟩
  have hqf : MulAut.conj q f = f :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hq f hf).symm
  have hbf : MulAut.conj b f ∈ V := (mem_normalizer_iff.mp hb f).mp (hFV hf)
  have he : MulAut.conj q (MulAut.conj b f) = MulAut.conj b f := by
    calc
      MulAut.conj q (MulAut.conj b f) =
          MulAut.conj ⁅q,b⁆ (MulAut.conj b (MulAut.conj q f)) := by
        simp [MulAut.conj_apply, commutatorElement_def, mul_assoc]
      _ = MulAut.conj ⁅q,b⁆ (MulAut.conj b f) := by rw [hqf]
      _ = MulAut.conj b f :=
        mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hc _ hbf).symm
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem centralizer_le_characterKernel (H B V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hBV : B ≤ normalizer (V : Set G))
    (hB0 : ambientTwoCore B = B ⊓ centralizer (V : Set G)) :
    H ⊓ centralizer (V : Set G) ≤ characterKernel H B hHB := by
  rintro q ⟨hqH,hq⟩
  apply (mem_characterKernel_iff H B hHB q hqH).mpr
  intro b hb
  rw [hB0]
  constructor
  · exact B.mul_mem ((mem_normalizer_iff.mp (hHB hqH) b).mp hb) (B.inv_mem hb)
  · have hn := normalizes_centralizer hBV
    have hbq := (mem_normalizer_iff.mp (hn hb) q⁻¹).mp
      ((centralizer (V : Set G)).inv_mem hq)
    change q * b * q⁻¹ * b⁻¹ ∈ centralizer (V : Set G)
    simpa only [mul_assoc] using (centralizer (V : Set G)).mul_mem hq hbq

/-- A complementary pair of actual conjugate planes proves the local kernel identity. -/
theorem local_kernel_eq_centralizer (H B V F Q₁ : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hBV : B ≤ normalizer (V : Set G))
    (hB0 : ambientTwoCore B = B ⊓ centralizer (V : Set G))
    (hQH : Q₁ ≤ H) (hQF : Q₁ ≤ centralizer (F : Set G))
    (hRQ : centralizer (V : Set G) ≤ Q₁)
    (b : G) (hb : b ∈ B) (hspan : V = F ⊔ F.map (MulAut.conj b).toMonoidHom) :
    Q₁ ⊓ characterKernel H B hHB = centralizer (V : Set G) := by
  apply le_antisymm
  · rintro q ⟨hq,hker⟩
    have hc := (mem_characterKernel_iff H B hHB q (hQH hq)).mp hker b hb
    have hcV : ⁅q,b⁆ ∈ centralizer (V : Set G) := (hB0 ▸ hc).2
    have hFV : F ≤ V := hspan.ge.trans' le_sup_left
    have hqF := hQF hq
    have hqFb := fixes_conjugate hFV (hBV hb) hqF hcV
    have hz : F ⊔ F.map (MulAut.conj b).toMonoidHom ≤ centralizer ({q} : Set G) := by
      apply sup_le
      · intro f hf
        exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hqF f hf)
      · intro f hf
        exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hqFb f hf)
    apply mem_centralizer_iff.mpr
    intro v hv
    exact (mem_centralizer_singleton_iff.mp (hz (hspan ▸ hv)))
  · intro q hq
    exact ⟨hRQ hq,centralizer_le_characterKernel H B V hHB hBV hB0 ⟨hQH (hRQ hq),hq⟩⟩

/-- Normality extends the local identity to the centralizer of the entire H-span. -/
theorem kernel_inter_eq_span_centralizer (H B V Q₁ : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hBV : B ≤ normalizer (V : Set G))
    (hB0 : ambientTwoCore B = B ⊓ centralizer (V : Set G))
    (hlocal : Q₁ ⊓ characterKernel H B hHB = centralizer (V : Set G))
    (hQQ : ambientTwoCore H ≤ Q₁)
    (hCQ : H ⊓ centralizer (conjugateSpanBy V H : Set G) ≤ ambientTwoCore H) :
    ambientTwoCore H ⊓ characterKernel H B hHB =
      H ⊓ centralizer (conjugateSpanBy V H : Set G) := by
  let N := ambientTwoCore H ⊓ characterKernel H B hHB
  have hNV : N ≤ centralizer (V : Set G) := (inf_le_inf_right _ hQQ).trans hlocal.le
  have hHN : H ≤ normalizer (N : Set G) :=
    (le_inf (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
      (characterKernel_normalized H B hHB)).trans inf_normalizer_le_normalizer_inf
  have hNU : N ≤ centralizer (conjugateSpanBy V H : Set G) :=
    le_centralizer_iff.mp (conjugateSpanBy_le (le_centralizer_iff.mp hNV)
      (normalizes_centralizer hHN))
  apply le_antisymm (le_inf (inf_le_left.trans (pCoreIn_le 2 H)) hNU)
  intro x hx
  exact ⟨hCQ hx, centralizer_le_characterKernel H B V hHB hBV hB0
    ⟨hx.1, centralizer_le (le_conjugateSpanBy V H) hx.2⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
