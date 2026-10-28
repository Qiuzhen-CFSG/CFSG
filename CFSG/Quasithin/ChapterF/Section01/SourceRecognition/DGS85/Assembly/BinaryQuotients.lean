module
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.BinarySourceApplication

/-!
# Binary exclusions through the actual local-to-parabolic quotient map

The original F.1.9 core-intersection identity makes the inclusion-induced
map Lᵢ/O₂(Lᵢ) → Pᵢ/O₂(Pᵢ) injective. Its formula is retained on every original
representative. Consequently the local quotient order divides the full
quotient order, even when the full quotient is a proper extension.

This excludes full binary quotients at A₅ and nonbinary linear endpoints.
The same order obstruction is pulled back along the actual starred inclusion
in G₀ to exclude Chapter 13's binary marking. It does not identify any
binary Ree TYPE row with a concrete model or assert source exhaustiveness.
The separate quintic consumer handles the original D₁₀/Sz(2) quotients.

Source: Aschbacher--Smith F.1.9--12, pp.261--264; DGS, Groups and Graphs
(1985), (12.9) and (13.1), printed pp.186--191.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BinaryQuotients
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

def localToFull (L : Fin 2 → Subgroup G) (S : Subgroup G) (i : Fin 2) :
    L i →* (parabolic L S i ⧸ pCore 2 (parabolic L S i)) :=
  (QuotientGroup.mk' _).comp (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left))

theorem localToFull_ker (h : HypothesisF11 L S) (i : Fin 2) :
    (localToFull L S i).ker = pCore 2 (L i) := by
  have hc : (twoCore (parabolic L S i)).subgroupOf (L i) = pCore 2 (L i) := by
    apply map_injective (L i).subtype_injective
    rw [subgroupOf_map_subtype, inf_comm, h.local_inf_parabolic_core i]
    rfl
  rw [← hc]
  ext x
  change QuotientGroup.mk (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) x) =
    (1 : parabolic L S i ⧸ pCore 2 (parabolic L S i)) ↔
      (x : G) ∈ twoCore (parabolic L S i)
  rw [QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem (f := (parabolic L S i).subtype)
    (parabolic L S i).subtype_injective).symm

def localQuotientEmbedding (h : HypothesisF11 L S) (i : Fin 2) :
    (L i ⧸ pCore 2 (L i)) →*
      (parabolic L S i ⧸ pCore 2 (parabolic L S i)) :=
  (localToFull L S i).range.subtype.comp
    (((QuotientGroup.quotientMulEquivOfEq (localToFull_ker h i).symm).trans
      (QuotientGroup.quotientKerEquivRange (localToFull L S i))).toMonoidHom)

theorem localQuotientEmbedding_injective (h : HypothesisF11 L S) (i : Fin 2) :
    Function.Injective (localQuotientEmbedding h i) :=
  (localToFull L S i).range.subtype_injective.comp
    (((QuotientGroup.quotientMulEquivOfEq (localToFull_ker h i).symm).trans
      (QuotientGroup.quotientKerEquivRange (localToFull L S i))).injective)

@[simp] theorem localQuotientEmbedding_mk (h : HypothesisF11 L S) (i : Fin 2) (x : L i) :
    localQuotientEmbedding h i (QuotientGroup.mk x) =
      QuotientGroup.mk (inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left) x) := rfl

theorem local_quotient_card_dvd_full (h : HypothesisF11 L S) (i : Fin 2) :
    Nat.card (L i ⧸ pCore 2 (L i)) ∣
      Nat.card (parabolic L S i ⧸ pCore 2 (parabolic L S i)) :=
  card_dvd_of_injective (localQuotientEmbedding h i) (localQuotientEmbedding_injective h i)

theorem binary_quotient_card {X : Type*} [Group X]
    (he : ClassicalGroup.IsPSL X 2 2) : Nat.card X = 6 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hF)
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF] at hc
  exact (Nat.card_congr e.toEquiv).trans (by norm_num at hc ⊢; exact hc)

theorem no_binary_full_of_local_quotient_card (h : HypothesisF11 L S) (i : Fin 2)
    (hc : ¬ Nat.card (L i ⧸ pCore 2 (L i)) ∣ 6) :
    ¬ ClassicalGroup.IsPSL (parabolic L S i ⧸ pCore 2 (parabolic L S i)) 2 2 := by
  intro he
  exact hc (binary_quotient_card he ▸ local_quotient_card_dvd_full h i)

/-- The local binary marking has the same order-six obstruction. -/
theorem no_binary_local_of_card {X : Type*} [Group X]
    (hc : ¬ Nat.card X ∣ 6) (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  have hsix : Nat.card X = 6 := by
    rw [Nat.card_congr (e.trans SLTwoPermThree.sl2Two_equiv_perm_three.some).toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [hsix] at hc
  exact hc (dvd_refl 6)

/-- The original quotient is pulled back through its literal starred inclusion
in G₀; only the selected endpoint is needed for this exclusion. -/
theorem no_source_binary_of_local_card (h : HypothesisF11 L S) (i : Bool)
    (hc : ¬ Nat.card (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ∣ 6)
    (e : (CommutingThreeProfile.ReducedLayer.star L S i ⧸
      pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_binary_local_of_card hc ((CommutingThreeProfile.ReducedLayer.originalQuotient h i).trans e)

/-- Nonbinary characteristic-two linear quotients are too large to embed
in the order-six binary parabolic quotient. -/
theorem nonbinary_linear_card_not_dvd_six {X : Type*} [Group X] {n : ℕ}
    (hn : 1 < n) (he : ClassicalGroup.IsPSL X 2 (2^n)) : ¬ Nat.card X ∣ 6 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1), mul_one, hF, ← Nat.card_congr e.toEquiv] at hc
  have hq : 4 ≤ 2^n := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ n by omega)
  have hsq : 16 ≤ (2^n)^2 := by nlinarith only [hq]
  have hpred : 15 ≤ (2^n)^2 - 1 := by omega
  have hlarge := Nat.mul_le_mul hq hpred
  intro hd
  have hle := Nat.le_of_dvd (by decide : 0 < 6) hd
  omega

/-- Either A₅-marked endpoint excludes its binary full-parabolic row. -/
theorem no_binary_full_of_a5 (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    ¬ ClassicalGroup.IsPSL (parabolic L S i ⧸ pCore 2 (parabolic L S i)) 2 2 := by
  apply no_binary_full_of_local_quotient_card h i
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The nonbinary original marking excludes a full binary quotient at that
endpoint, without assuming that its full quotient equals its local quotient. -/
theorem no_binary_full_of_nonbinary_linear (h : HypothesisF11 L S) (i : Fin 2)
    {n : ℕ} (hn : 1 < n) (he : ClassicalGroup.IsPSL (L i ⧸ pCore 2 (L i)) 2 (2^n)) :
    ¬ ClassicalGroup.IsPSL (parabolic L S i ⧸ pCore 2 (parabolic L S i)) 2 2 :=
  no_binary_full_of_local_quotient_card h i (nonbinary_linear_card_not_dvd_six hn he)

/-- The A₅ quotient in either mixed or A₅/A₅ input rules out the Chapter 13
starred binary marking; no condition on the other endpoint is added. -/
theorem no_source_binary_of_a5 (h : HypothesisF11 L S) (i : Bool)
    (eA : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      alternatingGroup (Fin 5))
    (e : (CommutingThreeProfile.ReducedLayer.star L S i ⧸
      pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False := by
  apply no_source_binary_of_local_card h i _ e
  rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

/-- The original nonbinary linear marking rules out the literal Chapter 13
starred quotient. This covers both linear--Suzuki and eight-field inputs. -/
theorem no_source_binary_of_nonbinary_linear (h : HypothesisF11 L S) (i : Bool)
    {n : ℕ} (hn : 1 < n)
    (he : ClassicalGroup.IsPSL (L (if i then 1 else 0) ⧸
      pCore 2 (L (if i then 1 else 0))) 2 (2^n))
    (e : (CommutingThreeProfile.ReducedLayer.star L S i ⧸
      pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : False :=
  no_source_binary_of_local_card h i (nonbinary_linear_card_not_dvd_six hn he) e

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BinaryQuotients
