module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.NormalizerGeneration.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricSix.SelectedGroup
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer

/-!
# The actual normalizer generates with the selected cubic residual

The original R is Sylow in the full preimage of its transposition image.
Relative Frattini therefore lifts the native transposition normalizer to
N_G(R), which normalizes Baum(R). The selected residual supplies the same
native cubic. Their images generate S₆. The original kernel Sylow and
perfect component quotient then remove the entire kernel, including its
possible central cubic part, giving generation in the original G.
Source: Aschbacher–Smith C.1.24(c), printed pp.130–131.
-/

public section
open Subgroup Theory.GroupTheory Equiv
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic
variable {G : Type*} [Group G] [Finite G]

/-- The literal residual of the selected cubic preimage generates G with
the original Baumann normalizer. No external conjugator is assumed. -/
theorem selected_normalizer_generate (L R T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym) (hq : Function.Surjective q)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 6))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R) (hRker : R ⊓ q.ker = pCore 2 G)
    (r c : Sym) (hR : R.map q = zpowers r)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M = 3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hMc : M.map (QuotientGroup.lift (pCore 2 G) q hQ) = zpowers c)
    (hnative : normalizer (zpowers r : Set Sym) ⊔ zpowers c = ⊤) :
    (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype ⊔
      normalizer (ChapterB.baumann R : Set G) = ⊤ := by
  let Y := (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype
  let K := Y ⊔ normalizer (ChapterB.baumann R : Set G)
  have hRN : normalizer (R : Set G) ≤ normalizer (ChapterB.baumann R : Set G) :=
    Stellmacher.normalizer_le_normalizer_baumann R
  have hQK : pCore 2 G ≤ K := hQR.trans (R.le_normalizer.trans (hRN.trans le_sup_right))
  have hN := normalizer_map_eq_of_kernel_intersection R hpR q hq P (hP.trans hRker.symm)
  rw [hR] at hN
  let π := QuotientGroup.mk' (pCore 2 G)
  let qb := QuotientGroup.lift (pCore 2 G) q hQ
  have he : qb.comp π = q := by ext x; rfl
  have hYq : Y.map q = zpowers c := by
    rw [←he,←map_map]
    rw [selected_residual_image R hpR M hM hn]
    exact hMc
  have hKq : K.map q = ⊤ := by
    apply top_unique
    rw [←hnative]
    apply sup_le
    · rw [←hN]
      exact map_mono (hRN.trans le_sup_right)
    · rw [←hYq]
      exact map_mono le_sup_left
  exact eq_top_of_full_symmetric_image L T q hQ hLq hT hgen P hP K hQK hKq

/-- Adding Baum(R) to the same residual does not change the generation
conclusion; this is the literal Hseed in C.1.24(c). -/
theorem selected_seed_normalizer_generate (L R T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym) (hq : Function.Surjective q)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 6))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R) (hRker : R ⊓ q.ker = pCore 2 G)
    (r c : Sym) (hR : R.map q = zpowers r)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M = 3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)))
    (hMc : M.map (QuotientGroup.lift (pCore 2 G) q hQ) = zpowers c)
    (hnative : normalizer (zpowers r : Set Sym) ⊔ zpowers c = ⊤) :
    ((pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype ⊔ ChapterB.baumann R) ⊔
      normalizer (ChapterB.baumann R : Set G) = ⊤ := by
  rw [sup_assoc,sup_of_le_right (ChapterB.baumann R).le_normalizer]
  exact selected_normalizer_generate L R T q hq hQ hLq hT hgen P hP hpR hQR hRker
    r c hR M hM hn hMc hnative

/-- The native cubic selection supplies the same actual M and all generation
inputs. Only the genuine earlier B.2.10 kernel Sylow and R-intersection
facts remain explicit for the original C.1.24 source assembly. -/
theorem exists_selected_normalizer_generate (L R T : Subgroup G) [L.Normal]
    [IsQuasisimple (L ⧸ pCore 2 L)] (q : G →* Sym) (hq : Function.Surjective q)
    (hQ : pCore 2 G ≤ q.ker) (hLq : L.map q = alternatingGroup (Fin 6))
    (hT : IsPGroup 2 T) (hgen : L ⊔ T = ⊤)
    (P : Sylow 2 q.ker) (hP : (P : Subgroup q.ker).map q.ker.subtype = pCore 2 G)
    (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R) (hRker : R ⊓ q.ker = pCore 2 G)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q = zpowers r) :
    ∃ (c : Sym) (M : Subgroup (G ⧸ pCore 2 G)),
      M ≤ L.map (QuotientGroup.mk' (pCore 2 G)) ∧ Nat.card M = 3 ∧
      R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G)) ∧
      M.map (QuotientGroup.lift (pCore 2 G) q hQ) = zpowers c ∧
      orderOf c = 3 ∧ c ∈ alternatingGroup (Fin 6) ∧ r*c*r⁻¹ = c⁻¹ ∧
      normalizer (zpowers r : Set Sym) ⊔ zpowers c = ⊤ ∧
      Nat.card (zpowers c ⊔ zpowers r : Subgroup Sym) = 6 ∧
      (¬Representation.BinaryOffender.fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers r) ≤
        Representation.BinaryOffender.fixedSpace (BinaryPermutation.naturalRepresentation (Fin 6)) (zpowers c)) ∧
      (pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype ⊔
        normalizer (ChapterB.baumann R : Set G) = ⊤ := by
  obtain ⟨c,M,hML,hM,hn,hMc,hc,hca,hinv,hgn,hcard,hmove⟩ :=
    exists_quotient_cubic L R q hQ hLq hpR r hr hR
  refine ⟨c,M,hML,hM,hn,hMc,hc,hca,hinv,hgn,hcard,hmove,?_⟩
  exact selected_normalizer_generate L R T q hq hQ hLq hT hgen P hP hpR hQR hRker
    r c hR M hM hn hMc hgn

end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
