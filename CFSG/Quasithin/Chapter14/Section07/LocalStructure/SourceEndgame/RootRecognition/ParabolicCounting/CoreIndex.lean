module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting.SteinbergGeneration
public import Theory.GroupTheory.PCoreImage

/-!
# The original parabolic two-core and index in 14.7.73

The original natural and Steinberg sections give S=[S,L₁], while the
natural P/E section gives P=[P,L₁](S∩P). Since T normalizes L₁ and both
S and P lie in T, these commutators put S and P in L₁. They are normal
two-subgroups of L₁. The genuine marked Sylow witness then identifies
SP=O₂(L₁)=T∩K, using only relative normality and the literal embeddings.

The same qL maps O₂(L₁) to the four-group core of the marked order-twelve
point residual. The original T∩L maps onto a Sylow two-subgroup of SL₃(2),
of order eight. Both quotient calculations use the original kernel
S=O₂(L), so their relative indices give |T∩L:T∩K|=2.

The final consumer combines this with the actual cubic fixed counts,
elementary P/U, commutator generation and |P|=2¹¹. It discharges all
parabolic counting obligations from the permitted earlier-source and
marked-geometry premises. Their producers remain with the local-structure
and root-geometry owners; the parent retains full 14.7.73 assembly.
No equality O₂(H)=P is used.

Source: Aschbacher–Smith, 14.7.73, printed pp.1076–1077
(PDF pp.1093–1094), combined manuscript of 1 March 2004.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

omit [Finite G] in
private theorem core_le_normalizing_sylow (A : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer A) : A.pCoreIn 2 ≤ (T : Subgroup G) := by
  have hn' : (T : Subgroup G) ≤ normalizer (A.pCoreIn 2) :=
    hn.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  exact sup_eq_right.mp (T.is_maximal'
    ((isPGroup_pCoreIn 2 A).to_sup_of_normal_left' T.isPGroup' hn') le_sup_right)

omit [Finite G] in
private theorem sylow_image_eq_intersection (A : Subgroup G)
    (hAT : A ≤ (T : Subgroup G))
    (R : Sylow 2 (K F)) (hR : (R : Subgroup (K F)).map (K F).subtype = A) :
    A = (T : Subgroup G) ⊓ K F := by
  have hRT : (R : Subgroup (K F)) ≤ (T : Subgroup G).subgroupOf (K F) := by
    intro x hx
    exact hAT (hR.le (mem_map_of_mem (K F).subtype hx))
  have he := R.is_maximal' T.isPGroup'.comap_subtype hRT
  have hm := congrArg (fun X : Subgroup (K F) => X.map (K F).subtype) he
  simpa only [hR, map_comap_eq, range_subtype, inf_comm] using hm.symm

omit [Finite G] in
private theorem core_subgroupOf (A : Subgroup G) (hA : A ≤ L) :
    (A.pCoreIn 2).subgroupOf L = (A.subgroupOf L).pCoreIn 2 := by
  apply (map_injective L.subtype_injective)
  rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 A).trans hA),
    map_pCoreIn_of_injective 2 _ _ L.subtype_injective, map_subgroupOf_eq_of_le hA]

/-- The original natural-section commutators place P=O₂(K) in L₁. -/
theorem source_core_le_parabolic (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    (K F).pCoreIn 2 ≤ F.Li L 1 := by
  have hPT := core_le_normalizing_sylow (K F)
    ((F.invariant 1).trans (H_normalizes_K F))
  have hS1 := SteinbergGeneration.S_le_L₁ d hS hTL s g hmark
  rw [source_core_parabolic_generation d k n (SteinbergGeneration.marked_image_card d g hmark)]
  exact sup_le (le_normalizer_iff_commutator_le_right.mp
    (hPT.trans (SteinbergGeneration.T_normalizes_L₁ hTL))) (inf_le_left.trans hS1)

/-- The source two-core equality, with the actual ambient Sylow intersection
and an intrinsically typed Sylow witness for K. -/
theorem source_parabolic_twoCore (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _))
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    S L F ⊔ (K F).pCoreIn 2 = (F.Li L 1).pCoreIn 2 ∧
      (F.Li L 1).pCoreIn 2 = (T : Subgroup G) ⊓ K F ∧
      ∃ R' : Sylow 2 (K F),
        (R' : Subgroup (K F)).map (K F).subtype = (F.Li L 1).pCoreIn 2 := by
  have hP1 := source_core_le_parabolic d k hS hTL s n g hmark
  have hPC : (K F).pCoreIn 2 ≤ (F.Li L 1).pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) hP1
      (parabolic_le_K.trans ((K F).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ _)))
  have hSC := SteinbergGeneration.S_le_parabolic_twoCore d hS hTL s g hmark
  obtain ⟨R', hR'⟩ := source_sylow d (le_sup_left.trans hgen.ge) R hR
  have hST := SteinbergGeneration.S_le_T hS hTL
  have hPT := core_le_normalizing_sylow (K F)
    ((F.invariant 1).trans (H_normalizes_K F))
  have hSP := sylow_image_eq_intersection _ (sup_le hST hPT) R' hR'
  have hCT := core_le_normalizing_sylow (F.Li L 1)
    (SteinbergGeneration.T_normalizes_L₁ hTL)
  have heq : S L F ⊔ (K F).pCoreIn 2 = (F.Li L 1).pCoreIn 2 :=
    le_antisymm (sup_le hSC hPC)
      ((le_inf hCT ((pCoreIn_le 2 _).trans parabolic_le_K)).trans hSP.ge)
  exact ⟨heq, heq.symm.trans hSP, R', hR'.trans heq⟩

private theorem source_relative_index (hS : S L F = L.pCoreIn 2)
    (A : Subgroup G) (hA : A ≤ L) :
    (S L F).relIndex A = Nat.card ((A.subgroupOf L).map d.qL) := by
  rw [← relIndex_ker, d.qL_ker, ← hS, relIndex_subgroupOf hA]

private theorem parabolic_core_image (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    (((F.Li L 1).pCoreIn 2).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointV.map (MulAut.conj g).toMonoidHom := by
  have hker : IsPGroup 2 d.qL.ker := by
    rw [d.qL_ker]
    exact (isPGroup_pCoreIn 2 L).comap_subtype
  rw [core_subgroupOf _ ((F.Li_le L 1).trans inf_le_left),
    map_pCoreIn_of_ker_isPGroup d.qL hker, hmark,
    ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective,
    Matrix.PSL3Two.MarkedAutomorphisms.point_core]

private theorem source_sylow_quotient_card (hTL : (T : Subgroup G) ≤ normalizer L) :
    Nat.card ((((T : Subgroup G) ⊓ L).subgroupOf L).map d.qL) = 8 := by
  obtain ⟨R, hR⟩ := d.source_sylow_image hTL
  have hm : (((T : Subgroup G) ⊓ L).subgroupOf L).map d.qL =
      (d.qL.comp (inclusion (inf_le_right : (T : Subgroup G) ⊓ L ≤ L))).range := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨inclusion inf_le_right l, l.property, rfl⟩
  rw [hm, hR, R.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
  decide +kernel

/-- The literal relative index in 14.7.73(2), computed through the original qL. -/
theorem source_parabolic_index (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _))
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom) :
    ((T : Subgroup G) ⊓ K F).relIndex ((T : Subgroup G) ⊓ L) = 2 := by
  obtain ⟨hSP, hC, _⟩ := source_parabolic_twoCore d k hS hTL hgen R hR s n g hmark
  have hCL : (F.Li L 1).pCoreIn 2 ≤ L :=
    (pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_left)
  have hsmall : (S L F).relIndex ((T : Subgroup G) ⊓ K F) = 4 := by
    rw [← hC, source_relative_index d hS _ hCL, parabolic_core_image d g hmark,
      card_map_of_injective (MulAut.conj g).injective,
      Matrix.PSL3Two.MarkedAutomorphisms.card_pointV]
  have hlarge : (S L F).relIndex ((T : Subgroup G) ⊓ L) = 8 := by
    rw [source_relative_index d hS _ inf_le_right, source_sylow_quotient_card d hTL]
  have hcontain : (T : Subgroup G) ⊓ K F ≤ (T : Subgroup G) ⊓ L :=
    le_inf inf_le_left (hC.ge.trans hCL)
  have hi := relIndex_mul_relIndex (S L F) ((T : Subgroup G) ⊓ K F)
    ((T : Subgroup G) ⊓ L) (le_sup_left.trans (hSP.trans hC).le) hcontain
  rw [hsmall, hlarge] at hi
  omega

/-- The complete parabolic counting branch of 14.7.73, on the original
markings and a specified Sylow three-subgroup of L₁. The source geometry
and 14.7.71–72 premises remain for the parent source-theorem assembly. -/
theorem source_parabolic_outputs (k : K F)
    (hS : S L F = L.pCoreIn 2)
    (hPhi : (frattini (S L F)).map (S L F).subtype = V)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hgen : K F = S L F ⊔ (S L F).conjBy ((k : G)⁻¹))
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _))
    (hpoint : d.U₀ = F.Vi 1)
    (s : BinaryConjugationSection L (S L F) V (BinaryLinearThree.S.comp d.qL))
    (n : BinaryConjugationSection (K F) ((K F).pCoreIn 2) (E L F k)
      (SL2FourNatural.naturalRepresentation.comp (qK d)))
    (g : BinaryLinearThree.Group)
    (hmark : ((F.Li L 1).subgroupOf L).map d.qL =
      Matrix.PSL3Two.MarkedAutomorphisms.pointA.map (MulAut.conj g).toMonoidHom)
    (B : Sylow 3 (F.Li L 1)) :
    letI : (F.U.subgroupOf ((K F).pCoreIn 2)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((pCoreIn_le 2 (K F)).trans ((K_le_H F).trans d.conjugationSection.normalized))
    S L F ⊔ (K F).pCoreIn 2 = (F.Li L 1).pCoreIn 2 ∧
      (F.Li L 1).pCoreIn 2 = (T : Subgroup G) ⊓ K F ∧
      (∃ R' : Sylow 2 (K F),
        (R' : Subgroup (K F)).map (K F).subtype = (F.Li L 1).pCoreIn 2) ∧
      ((T : Subgroup G) ⊓ K F).relIndex ((T : Subgroup G) ⊓ L) = 2 ∧
      IsElementaryAbelian 2 ((K F).pCoreIn 2 ⧸ F.U.subgroupOf ((K F).pCoreIn 2)) ∧
      ⁅(K F).pCoreIn 2, K F⁆ ⊔ F.U = (K F).pCoreIn 2 ∧
      (K F).pCoreIn 2 = (S L F ⊓ (K F).pCoreIn 2) ⊔
        ((S L F).conjBy ((k : G)⁻¹) ⊓ (K F).pCoreIn 2) ∧
      Nat.card (S L F ⊓ centralizer (cubic B : Set G) : Subgroup G) = 8 ∧
      Nat.card (F.U ⊓ centralizer (cubic B : Set G) : Subgroup G) = 2 ∧
      F.U.relIndex (E L F k) = 4 ∧ Nat.card ((K F).pCoreIn 2) = 2 ^ 11 := by
  have hpar := SteinbergGeneration.marked_image_card d g hmark
  obtain ⟨helem, hcomm, hprod, _, hindex, hcard⟩ :=
    source_counted_quotients d k hS hPhi hTL hgen R hR hpoint s n hpar
  obtain ⟨hSP, hTK, hSyl⟩ := source_parabolic_twoCore d k hS hTL hgen R hR s n g hmark
  obtain ⟨hCS, hCU⟩ := source_fixed_counts d hS
    ((U_le_E d k).trans (n.kernel_le.trans (pCoreIn_le 2 _))) hpoint s hpar B
  exact ⟨hSP, hTK, hSyl, source_parabolic_index d k hS hTL hgen R hR s n g hmark,
    helem, hcomm, hprod, hCS, hCU, hindex, hcard⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.ParabolicCounting
