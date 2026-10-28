module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.CoreConjugates
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryBaumann.SourceProduct

/-!
# The original unitary Baumann normalizer bound

Assume N_G(Baum(R₁)) escapes N_G(L). The preceding source construction then
gives Q = V × C_B(L), elementary Q, and its escaping conjugate. Root-eight
lifting bounds the normalizer orbit of Q by two. Since the original Sylow
subgroup fixes Q, the two-conjugate normalizer lemma forces the whole
Baumann normalizer to fix Q. Its previously proved core-normalizer bound
contradicts escape. This proves the unitary conclusion of 13.3.10(2)
before using any plane-centrality assumption from 13.3.14.

The proofs specialize and assemble the checked OriginalUnitaryNoncentrality
lemmas using normalizer escape directly. Source: Aschbacher--Smith
13.3.10(2), pp.887--888; C.1.37 and C.6.3.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
/-- Original13.3.10(2) for the literal unitary point radical R₁. -/
theorem unitary_original_baumann_bound
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hmax : D.L ∈ Chapter1.LStar G (D.T : Subgroup G))
    (eL : (D.L ⧸ pCore 2 D.L) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
 :
    normalizer (ChapterB.baumann ((D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2) : Set G) ≤
      normalizer (D.L : Set G) := by
  by_contra hout
  let R := (D.L₁ ⊔ (D.T : Subgroup G)).pCoreIn 2
  let S := ChapterB.baumann R
  let Y := D.L ⊔ S
  let Q := Y.pCoreIn 2
  let C := S ⊓ centralizer (D.L : Set G)
  obtain ⟨hprod,_,_,helem,x,hx,hext,hCA,hspan⟩ :=
    unitary_original_baumann_elementary_of_escape D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hout
  let : IsElementaryAbelian 2 Q := helem
  obtain ⟨rho,E,he,_,_,_,hVS,_,himage,_,_⟩ :=
    unitary_original_offender_images_of_escape D h chosen hmax eL structural
      e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hout
  obtain ⟨_,hcore⟩ := unitary_original_baumann_core_of_escape D h chosen hmax eL structural
    e E0 he0 hUV hZV hTZ hTU hZ hU B hBV hTB hB hout
  have hTN := (unitary_original_module_normalizers h hmax eL chosen structural).1
  let P := D.L₁ ⊔ (D.T : Subgroup G)
  have hRT : R ≤ (D.T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (D.T.subtype le_sup_right)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (D.T : Subgroup G) ≤ P from le_sup_right)] using hh
  have hTR : (D.T : Subgroup G) ≤ normalizer (R : Set G) :=
    le_sup_right.trans (P.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P)))
  have hTS : (D.T : Subgroup G) ≤ normalizer (S : Set G) :=
    hTR.trans (Stellmacher.normalizer_le_normalizer_baumann R)
  have hSN : S ≤ normalizer (D.V : Set G) := inf_le_left.trans (hRT.trans hTN)
  have hTQ : (D.T : Subgroup G) ≤ normalizer (Q : Set G) :=
    ((le_inf chosen.sylow_normalizes_component hTS).trans
      (normalizer_inf_normalizer_le_normalizer_sup D.L S)).trans
      (normalizer_le_normalizer_characteristic_image Y (pCore 2 Y))
  change Q = D.V ⊔ C at hprod
  change S = D.V.conjBy x⁻¹ ⊔ Q at hspan
  have hCQ : C ≤ Q := hprod ▸ le_sup_right
  have hCS : C ≤ centralizer (S : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hspan]
    exact sup_le (le_centralizer_iff.mp hCA)
      ((le_centralizer Q).trans (centralizer_le hCQ))
  have horbit := unitary_baumann_core_conjugates D.V S Q C rho E he hSN himage
    hcore hprod hCS x⁻¹ ((normalizer _).inv_mem hx) hext
  have hn := normalizer_le_of_sylow_two_conjugates D.T S Q hTS hTQ
    x⁻¹ ((normalizer _).inv_mem hx) horbit
  have hbound := hn.trans (unitary_baumann_core_normalizer h chosen hmax eL hTN R hRT hTR hVS)
  exact hout hbound

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
