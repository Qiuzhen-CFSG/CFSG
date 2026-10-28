module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity.NaturalLayer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.CheckedPoint
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Checked
public import Theory.GroupAction.OddIndexInvolutionLayers
public import Theory.GroupTheory.PCoreImage
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Borel fixation forces fixation of the field-four block

The Sylow condition puts O₂(K) inside Tᵥ, so the involution a fixes it.
Faithfulness of the actual natural module gives C_K(O₂(K)) ≤ O₂(K).
The K-conjugates of a therefore generate an elementary abelian group W,
with [W,K] ≤ O₂(K) and [W ∩ O₂(K),K] ≤ U(K). A Borel diagonal has no
nonzero fixed vector on U(K)/C_U(K), and the Borel has odd index.
Two applications of averaging now show that a fixes all of K.

Only the genuine quotient/module coordinates of the source block are needed;
subnormality in the larger ambient group is not required. The final application
uses the actual marked a and the literal checked quotient. Its Borel-fixation
hypothesis is supplied separately by the Borel geometry argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the final
paragraph of the proof of 13.6.18, printed p.931 (PDF p.948).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity
open Subgroup ChapterC Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups commutatorElement

variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]

/-- The actual natural block model and Borel image force fixation. -/
theorem centralizes_of_borel_fixation (K T B : Subgroup G)
    (hTK : T ≤ normalizer (K : Set G))
    (hSylow : CFSG.Quasithin.Chapter1.IsSylowIn 2 T (K ⊔ T))
    (hTB : T ≤ B) (hBT : B ≤ K ⊔ T)
    (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (model : BlockModuleModel K ρ)
    (hρ : ∀ (g : SL(2,F)) (w : Multiplicative (Fin 2 → F)),
      Multiplicative.toAdd (ρ g w) = g.val *ᵥ Multiplicative.toAdd w)
    (hF : 2 < Nat.card F)
    (hB : (B.subgroupOf K).map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) = rankOneBorel F)
    (a : G) (ha2 : a ^ 2 = 1) (haT : a ∈ T)
    (haB : a ∈ centralizer (B : Set G)) : a ∈ centralizer (K : Set G) := by
  let Q := K.pCoreIn 2
  let U := (blockU K).map K.subtype
  have hHK : K ⊔ T ≤ normalizer (K : Set G) := sup_le K.le_normalizer hTK
  have hKQ : K ≤ normalizer (Q : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hQT : Q ≤ T := by
    obtain ⟨S, hS⟩ := hSylow
    rw [← hS]
    exact (pCoreIn_mono_of_normalizes le_sup_left hHK).trans (pCoreIn_le_sylow _ S)
  have hQB : pCore 2 K ≤ B.subgroupOf K := by
    intro x hx
    exact hTB (hQT (mem_map_of_mem K.subtype hx))
  have hself : K ⊓ centralizer (Q : Set G) ≤ Q := by
    intro x hx
    apply mem_map.mpr
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    apply centralizer_blockU_le_core ρ model hρ
    intro u hu
    apply Subtype.ext
    exact hx.2 u (mem_map_of_mem K.subtype (blockU_le_core hu))
  have hQU : ⁅K, Q⁆ ≤ U := by
    have ht : (⊤ : Subgroup K).map K.subtype = K := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    have he : ⁅K, Q⁆ = (⁅(⊤ : Subgroup K), pCore 2 K⁆).map K.subtype := by
      rw [map_commutator, ht]
      rfl
    rw [he, commutator_comm]
    exact le_rfl
  have hfixed : U ⊓ centralizer ((B.subgroupOf K).map K.subtype : Set G) ≤
      centralizer (K : Set G) := by
    rintro x ⟨⟨u, hu, rfl⟩, hx⟩ y hy
    have hc : u ∈ center K := borel_centralizer_blockU_le_center ρ model hρ
      (B.subgroupOf K) hB hF ⟨hu, ?_⟩
    · exact congrArg Subtype.val (mem_center_iff.mp hc ⟨y, hy⟩)
    · intro b hb
      apply Subtype.ext
      exact hx b (mem_map_of_mem K.subtype hb)
  exact OddIndexInvolutionLayers.involution_fixed_of_layers K Q U hKQ hself hQU
    (B.subgroupOf K) (borel_odd_index ρ model _ hQB hB) hfixed a ha2
    (hHK (hBT (hTB haT)))
    (centralizer_le (hQT.trans hTB) haB)
    (centralizer_le (by rw [subgroupOf_map_subtype]; exact inf_le_left) haB)

omit [CharP F 2] in
/-- The field-four case needed in 13.6.18, with characteristic supplied by its order. -/
theorem centralizes_of_four_borel_fixation (K T B : Subgroup G)
    (hTK : T ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 T (K ⊔ T))
    (hTB : T ≤ B) (hBT : B ≤ K ⊔ T)
    (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (model : BlockModuleModel K ρ)
    (hρ : ∀ (g : SL(2,F)) (w : Multiplicative (Fin 2 → F)),
      Multiplicative.toAdd (ρ g w) = g.val *ᵥ Multiplicative.toAdd w)
    (hF : Nat.card F = 4)
    (hB : (B.subgroupOf K).map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) = rankOneBorel F)
    (a : G) (ha2 : a ^ 2 = 1) (haT : a ∈ T)
    (haB : B ≤ centralizer ({a} : Set G)) : K ≤ centralizer ({a} : Set G) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  have ha := centralizes_of_borel_fixation K T B hTK hSylow hTB hBT ρ model hρ
    (by omega) hB a ha2 haT (fun b hb => mem_centralizer_singleton_iff.mp (haB hb))
  intro k hk
  exact mem_centralizer_singleton_iff.mpr (ha k hk)

open A5Module
omit [CharP F 2] in
/-- Apply the rigidity theorem to the actual marked a, and transport its conclusion
through C_G(v) → C_G(v)/⟨v⟩. Borel fixation is the independent geometry input. -/
theorem source_marked_centralizes {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (K B : Subgroup G)
    (hTK : Tv (T : Subgroup G) (markedV d.module) ≤ normalizer (K : Set G))
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.module))
      (K ⊔ Tv (T : Subgroup G) (markedV d.module)))
    (hTB : Tv (T : Subgroup G) (markedV d.module) ≤ B)
    (hBT : B ≤ K ⊔ Tv (T : Subgroup G) (markedV d.module))
    (ρ : SL(2,F) →* MulAut (Multiplicative (Fin 2 → F)))
    (model : BlockModuleModel K ρ)
    (hρ : ∀ (g : SL(2,F)) (w : Multiplicative (Fin 2 → F)),
      Multiplicative.toAdd (ρ g w) = g.val *ᵥ Multiplicative.toAdd w)
    (hF : Nat.card F = 4)
    (hB : (B.subgroupOf K).map
      (model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) = rankOneBorel F)
    (hfix : B ≤ centralizer ({markedA d.module} : Set G)) :
    K ≤ centralizer ({markedA d.module} : Set G) ∧
      checkedImage (markedV d.module) K ≤ centralizer
        ({checkedSylowMap (T : Subgroup G) (markedV d.module) d.checkedPoint} :
          Set (Gcheck (markedV d.module))) := by
  have ha2 : markedA d.module ^ 2 = 1 := by
    obtain ⟨c, _, hc⟩ := exists_a_conjugator d.module
    rw [← hc, ← map_pow, d.module.markedZ_pow_two, map_one]
  have hK := centralizes_of_four_borel_fixation K _ B hTK hSylow hTB hBT ρ model hρ
    hF hB (markedA d.module) ha2 d.checkedPoint.property hfix
  refine ⟨hK, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  let a : Gv (markedV d.module) := inclusion inf_le_right d.checkedPoint
  change checkedQuotientMap (markedV d.module) k * checkedQuotientMap (markedV d.module) a =
    checkedQuotientMap (markedV d.module) a * checkedQuotientMap (markedV d.module) k
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.mp (hK hk)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BlockRigidity
