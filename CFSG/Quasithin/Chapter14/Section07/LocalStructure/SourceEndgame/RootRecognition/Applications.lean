module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Algebra
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ElementaryQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.CanonicalCover

/-!
# Consumers of the original 14.7.73 root calculation

The source core and Frattini identities, marked Sylow image, and original
root generation supply the elementary P/U quotient and its commutator
generation. The proof constructs the actual Sylow witness and identifies
the two-root product with P=O₂(K), using the companion algebra module.

Once P/E is recognized and |E/U|=4 is proved, the original |U|=32 gives
|P|=2¹¹. After the later 14.7.74 equality O₂(H)=O₂(K), the same original
markings feed CanonicalCover and construct the six-dimensional RuTwo data.
Neither an action on P/U nor a projection nor indecomposability is assumed.

Natural P/E recognition, starred generation, the Sylow-image calculation,
and the fixed-kernel count remain explicit 14.7.73 obligations. These
conditional applications do not assert completion of the source theorem.
Source: Aschbacher–Smith 14.7.73–75, printed pp.1076–1078, manuscript of
1 March 2004.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition
open Chapter12.Section08 CriticalFusion.Source ChapterJ
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

omit [Finite G] in
private theorem product_core_intersections (k : K F)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹)) :
    P₀ L F k = (S L F ⊓ (K F).pCoreIn 2) ⊔
      ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) := by
  have hi (A : Subgroup G) (hA : A ≤ K F) :
      A ⊓ F.H.pCoreIn 2 = A ⊓ (K F).pCoreIn 2 := by
    rw [K_core_eq_intersection]
    exact le_antisymm (fun _ h => ⟨h.1, hA h.1, h.2⟩) (fun _ h => ⟨h.1, h.2.2⟩)
  exact congrArg₂ (· ⊔ ·) (hi _ (le_sup_left.trans hgen.ge))
    (hi _ (le_sup_right.trans hgen.ge))

/-- Apply the existing elementary-quotient and generation proofs to the
original two-core, retaining the natural-section recognition as an input. -/
theorem source_quotient_outputs (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d))) :
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2)) ∧
      ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 ∧
      (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
        ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      ∃ R' : Sylow 2 (K F),
        (R' : Subgroup (K F)).map (K F).subtype = S L F ⊔ (K F).pCoreIn 2 := by
  let := K_perfect d
  let : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
  let : (((K F).pCoreIn 2).subgroupOf (K F)).Normal :=
    normal_subgroupOf_of_le_normalizer ((K F).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ _))
  let : (F.U.subgroupOf (K F)).Normal := normal_subgroupOf_of_le_normalizer
    ((K_le_H F).trans d.conjugationSection.normalized)
  have hp : IsPGroup 2 (S L F) := hS.symm ▸ isPGroup_pCoreIn 2 L
  have hf : (frattini (S L F)).map (S L F).subtype ≤ F.U :=
    hPhi.le.trans (Data.V_le_U F)
  have hd : ⁅S L F, S L F⁆ ≤ F.U := derived_le_of_frattini_image_le hp hf
  have hSK : S L F ≤ K F := le_sup_left.trans hgen.ge
  have hP₀ := (source_product_eq_core d k hSK (QH_normalizes_S hS hTL)
    hgen hd (U_le_QH d) R hR).2
  have hPgen := hP₀.symm.trans (product_core_intersections k hgen)
  obtain ⟨_, helem⟩ := elementary_source_quotient (K F) ((K F).pCoreIn 2) (S L F)
    F.U k (qK d) (qK_surjective d) n hp hf
    ((K_le_H F).trans d.conjugationSection.normalized) hgen hPgen
  obtain ⟨R', hR'⟩ := source_sylow d hSK R hR
  exact ⟨helem, commutator_generation_of_source_sylow (K F) ((K F).pCoreIn 2)
    (S L F) F.U (pCoreIn_le 2 _) hSK ((U_le_E d k).trans n.kernel_le)
    (isPGroup_pCoreIn 2 _) R' hR' hd, hPgen, R', hR'⟩

/-- The recognized natural section and the fixed-kernel count give the
literal order of O₂(K), using the already proved |U|=32. -/
theorem core_card (k : K F) (hpoint : d.U₀ = F.Vi 1)
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hEU : F.U.relIndex (E L F k) = 4) : Nat.card ((K F).pCoreIn 2) = 2 ^ 11 := by
  have hcard := (F.U.subgroupOf (E L F k)).card_mul_index
  have hU : Nat.card (F.U.subgroupOf (E L F k)) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe (U_le_E d k)).toEquiv).trans (U_card d hpoint)
  change Nat.card (F.U.subgroupOf (E L F k)) * F.U.relIndex (E L F k) = _ at hcard
  rw [hU, hEU] at hcard
  rw [n.card_section, ← hcard,
    show Nat.card SL2FourNatural.V = 16 by
      rw [Nat.card_eq_fintype_card, SL2FourNatural.card_vector]]
  norm_num

private theorem ruTwo_adapter
    (V : Subgroup G) (T : Sylow 2 G) (H U Z K S : Subgroup G) [Group.IsPerfect K]
    (hH : H = ChapterJ.centralizerOfSylowCenter T)
    (hU : U = conjugateSpan H V) (hZ : Z = ChapterJ.sylowCenter T)
    (hKH : K ≤ H) (hSK : S ≤ K)
    (qH : H →* ChapterJ.S5) (hq : Function.Surjective qH)
    (hqker : qH.ker = (H.pCoreIn 2).subgroupOf H)
    (a : ChapterJ.L2FourAction)
    (dn : BinaryConjugationSection H U Z (a.action.comp qH))
    (k : K) (qK : K →* SL2FourNatural.SL) (hqK : Function.Surjective qK)
    (hmark : ∀ k : K, qH ⟨k, hKH k.property⟩ = alternatingActor a (qK k))
    (n : BinaryConjugationSection K (H.pCoreIn 2) (S ⊓ S.conjBy ((k : G)⁻¹))
      (SL2FourNatural.naturalRepresentation.comp qK))
    (hUE : U ≤ S ⊓ S.conjBy ((k : G)⁻¹))
    (hS : IsPGroup 2 S) (hPhi : (frattini S).map S.subtype ≤ U)
    (hKgen : K = S ⊔ S.conjBy ((k : G)⁻¹))
    (hPgen : H.pCoreIn 2 = (S ⊓ H.pCoreIn 2) ⊔
      (S.conjBy ((k : G)⁻¹) ⊓ H.pCoreIn 2))
    (hcard : U.relIndex (S ⊓ S.conjBy ((k : G)⁻¹)) = 4)
    (R : Sylow 2 K) (hR : (R : Subgroup K).map K.subtype = S ⊔ H.pCoreIn 2) :
    Nonempty (ChapterJ.RuTwo V T) := by
  subst H U Z
  exact exists_ruTwo_of_source_roots V T K S hKH hSK qH hq hqker a dn k qK hqK
    hmark n hUE hS hPhi hKgen hPgen hcard R hR

/-- The original root data feed the canonical six-dimensional cover after
the later 14.7.74 core equality. Natural recognition and |E/U|=4 are still
the two substantial 14.7.73 inputs; no indecomposability is assumed. -/
theorem source_ruTwo (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (hEU : F.U.relIndex (E L F k) = 4)
    (hpoint : d.U₀ = F.Vi 1)
    (hz : ChapterJ.sylowCenter T = F.Vi 1)
    (hcore : F.H.pCoreIn 2 = (K F).pCoreIn 2) : Nonempty (ChapterJ.RuTwo V T) := by
  let := K_perfect d
  obtain ⟨_, _, hPgen, R', hR'⟩ := source_quotient_outputs d k hS hPhi hTL hgen R hR n
  have nH : BinaryConjugationSection (K F) (F.H.pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)) := by
    rw [hcore]
    exact n
  refine ruTwo_adapter V T F.H F.U (F.Vi 1) (K F) (S L F)
    (source_H_eq_RuTwo_overgroup d hz) source_U_eq_RuTwo_span hz.symm
    (K_le_H F) (le_sup_left.trans hgen.ge) d.qH d.qH_surjective d.qH_ker
    d.naturalQuotient (source_natural_U_section d hpoint) k (qK d) (qK_surjective d)
    (qK_marking d) nH (U_le_E d k) (hS.symm ▸ isPGroup_pCoreIn 2 L)
    (hPhi.le.trans (Data.V_le_U F)) hgen ?_ hEU R' ?_
  · simpa only [hcore] using hPgen
  · simpa only [hcore] using hR'

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition
