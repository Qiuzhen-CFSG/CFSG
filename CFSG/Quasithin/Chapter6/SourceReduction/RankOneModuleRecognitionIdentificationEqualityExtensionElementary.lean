module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationEqualityExtensionSylow
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import Theory.Frattini.CentralElementarySupplement
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# Elementary cores in the equality extension

The proved formula Q = V C_H(K), with V central elementary in Q, identifies
the embedded Frattini groups of Q and C_H(K). This common subgroup is
normalized by LT and H. If nontrivial, uniqueness of the maximal two-local
over LT would put H in M, contradicting the canonical escaping pair.
Thus Q and C_H(K) are elementary. Since O₂(M) lies in Q and is
self-centralizing in M, Q = O₂(M), giving the relative normality needed
for the marked quotient.

This proves the elementary and kernel-normality portions of the block
calculation. The order bound, marked S₅ quotient, and four-group fusion
remain obligations of the equality-geometry owner.
Source: Aschbacher–Smith, proof of 6.2.13, printed pp.687–688; uniqueness
is Theorem 1.2.7, printed p.506.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The common Frattini subgroup is normalized by both H and LT, so uniqueness
of the maximal two-local over LT forces it to vanish. -/
theorem LocalAnalysis.equality_local_core_elementary
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    IsElementaryAbelian 2 ((L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let H := centralizer ({z} : Set G)
  let K := equalityLayerClosure L R z
  let D := equalityCentralizer L R z
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let F := (frattini Q).map Q.subtype
  have hp := A.equality_action_pair_data h611 hnatural hz horder hTH hbranch
  have hQ : Q = layer L R ⊔ D := by
    rw [show Q = (L ⊔ (T : Subgroup G)).pCoreIn 2 from rfl,
      ← equality_sylow_centralizer_eq_core h611 hnatural]
    exact A.equality_sylow_layer_centralizer h611 hnatural hz hTH hp.plusType
  have hF : F = (frattini D).map D.subtype :=
    frattini_map_eq_of_central_elementary_supplement Q D (layer L R)
      (isPGroup_pCoreIn 2 _) h611.layer_elementary
      (le_centralizer_iff.mp (local_core_centralizes_layer h611)) hQ
  have hHD : H ≤ normalizer (D : Set G) := by
    change H ≤ normalizer ((centralizer (K : Set H)).map H.subtype : Set G)
    have hh := (centralizer (K : Set H)).le_normalizer_map H.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hHF : H ≤ normalizer (F : Set G) := by
    rw [hF]
    exact hHD.trans (normalizer_le_normalizer_characteristic_image D (frattini D))
  have hJQ : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hJF : L ⊔ (T : Subgroup G) ≤ normalizer (F : Set G) :=
    hJQ.trans (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h611.local_mem.1.prop, ?_⟩
    intro J hJ hLJ
    exact le_antisymm (h611.local_mem.1.2 hJ hLJ) hLJ
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h611.simpleQTKE T hstar
  have hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro N hN hJN
    exact (hu.normalizer_unique N hN hJN).trans
      (hu.normalizer_unique M h611.maximal (sup_le h611.L_le h611.sylow_le)).symm
  have hzero : F = ⊥ := by
    by_contra hne
    have hNM : normalizer (F : Set G) ≤ M := normalizer_le_of_unique_maximalTwoLocal
      hunique ((isPGroup_pCoreIn 2 _).to_le (show F ≤ Q from map_subtype_le _)) hne hJF
    obtain ⟨g, hgH, hgM, _⟩ := hp.pair
    exact hgM (hNM (hHF hgH))
  let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 _⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (((frattini Q).map_eq_bot_iff_of_injective Q.subtype_injective).mp hzero)

/-- The elementary centralizer assertion in the block calculation, with its
extraspecial input discharged by the canonical equality pair. -/
theorem LocalAnalysis.equality_centralizer_elementary
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    IsElementaryAbelian 2 (equalityCentralizer L R z) := by
  let := A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  exact IsElementaryAbelian.of_injective
    (inclusion (A.equality_centralizer_le_local_core h611 hnatural hz hTH))
    (inclusion_injective _)

/-- Since Q is abelian and contains O₂(M), characteristic two in M identifies
the two cores. In particular the source quotient kernel is normal in M. -/
theorem LocalAnalysis.equality_local_core_eq_maximal_core
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 = M.pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hJM : L ⊔ (T : Subgroup G) ≤ M := sup_le h611.L_le h611.sylow_le
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow M (T.subtype h611.sylow_le)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le h611.sylow_le] at hh
  have hMQ : M.pCoreIn 2 ≤ Q := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 M) (hcoreT.trans le_sup_right)
    (hJM.trans (M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image M (pCore 2 M))))
  let : IsElementaryAbelian 2 Q :=
    A.equality_local_core_elementary h611 hnatural hz horder hTH hbranch
  have hchar : M ⊓ centralizer (M.pCoreIn 2 : Set G) ≤ M.pCoreIn 2 :=
    Chapter1.mem_He_iff.mpr
      (h611.simpleQTKE.evenCharacteristic T M h611.maximal h611.sylow_le)
  exact le_antisymm (le_trans (le_inf ((pCoreIn_le 2 _).trans hJM)
    ((le_centralizer Q).trans (centralizer_le hMQ))) hchar) hMQ

/-- Relative normality of the actual M-quotient kernel. -/
theorem LocalAnalysis.equality_local_core_normal
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hbranch : sourceClosure (T : Subgroup G) L R z ⊓ layer L R = ZS (T : Subgroup G) L R) :
    (((L ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf M).Normal := by
  rw [A.equality_local_core_eq_maximal_core h611 hnatural hz horder hTH hbranch]
  exact (normal_subgroupOf_iff_le_normalizer (pCoreIn_le 2 M)).mpr
    (M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
