module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ExternalAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.PairedExclusion
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.SourceAction

/-!
# Assembly of the ordinary A₆ external-component exclusion

The component list and the earlier source geometry force the actual full
Aut(L₃(2)) conjugation image when L₁ is outside K. Normal cubic generation,
the earlier Fitting alternatives and the solvable supplement give the paired
chief-factor hypotheses. The proved module exclusion then forces L₁ ≤ K.

All normality is relative to H or H/O₂(H). In particular no generalized
Fitting decomposition or paired-factor conclusion is assumed.
Source: Aschbacher–Smith 13.8.21(1), printed p.956.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ExternalComponentAction Geometry.CoveredProduct.ResidualPlacement
open ExternalModules

private theorem fitting_of_cubic_supplement {J : Type*} [Group J] [Finite J]
    (K X T : Subgroup J) [K.Normal] [X.Normal]
    (hK : IsQuasisimple K) (hX : Nat.card X = 3) (hT : IsPGroup 2 T)
    (hgen : K ⊔ X ⊔ T = ⊤) (hF : fittingSubgroup J ≤ X) :
    generalizedFitting J = K ⊔ X := by
  let : IsCyclic X := isCyclic_of_prime_card hX
  have hXF : X ≤ fittingSubgroup J := le_sSup ⟨inferInstance, inferInstance⟩
  have hFX : fittingSubgroup J = X := le_antisymm hF hXF
  let q := QuotientGroup.mk' K
  let : Group.IsSolvable (X.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective X)
  let : Group.IsNilpotent (T.map q) := (hT.map q).isNilpotent
  have hquot : Group.IsSolvable (J ⧸ K) := by
    apply Group.isSolvable_of_normal_sup_eq_top (X.map q) (T.map q)
    have hm := congrArg (Subgroup.map q) hgen
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective K)] using hm
  let := hquot
  have hE : componentLayer J = K := by
    apply le_antisymm
    · apply sSup_le
      intro D hD
      let := hD.2
      exact le_of_isPerfect_of_solvable_quotient D K
    · exact le_sSup ⟨(inferInstance : K.Normal).isSubnormal, hK⟩
  rw [generalizedFitting, hFX, hE, sup_comm]

variable {G : Type*} [Group G] [Finite G]
variable (κ : GroupClass) (H K L L₁ M G₁ V₁ V₃ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The ordinary-A₆ branch of 13.8.21(1). The earlier inputs are the literal
local residual, its cubic quotient, the seed commutator, 13.8.13, the ordinary
specialization of 13.8.14, quasisimplicity from 13.8.15, and the faithful source
centralizer identity. The component list is the independently supplied (2).
The B.4 single-factor bounds and q ≤ 2 remain precise earlier inputs. -/
theorem L₁_le_of_ordinary_source
    (hQTKE : IsSimpleQTKE κ G)
    (d : RankReduction.SourceSetup κ H K L₁ M G₁ T)
    (models : RankReduction.SmallQuotient (K ⧸ pCore 2 K))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hmarked : L₁ =
      (pResidual 2 ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G) : Subgroup G)).map
        ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G) : Subgroup G).subtype)
    (hflag : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (horder : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hfull : ⁅L₁, (T : Subgroup G)⁆ = L₁) (hseed : ⁅V₃, L₁⁆ = V₃)
    (hsolvable : ∀ J : Subgroup G, L₁ ⊔ (T : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (hfit : fittingPreimageResidual H = ⊥ ∨ fittingPreimageResidual H = L₁)
    (hqs : IsQuasisimple (Source.starImage H K))
    (act : SourceAction H V₃ V₁)
    (hcentralizer : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H)
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (hsmall : quadraticRatio act.representation ≤ 2) : L₁ ≤ K := by
  by_contra hout
  let : (K.subgroupOf H).Normal := d.normal
  let : (Source.starImage H K).Normal :=
    d.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨_, _, e, _, hc, hn, _, hgen, _, f, hf⟩ :=
    ordinary_source_geometry κ H K L L₁ M G₁ V₁ V₃ T hQTKE d hout models eL
      hmarked hflag (fun _ => horder) hfull hseed hsolvable act
  let : (Source.starImage H L₁).Normal := hn
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq d.generated
  have hLH : L₁ ≤ H := (le_sup_right.trans le_sup_left).trans_eq d.generated
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans_eq d.generated
  have hcard := normal_star_card_three H L₁ hLH hn horder
  have hcomm (k : Source.starImage H K) (x : Source.starImage H L₁) :
      Commute (k : Source.Hstar H) (x : Source.Hstar H) := hc x.property k k.property
  have hdis : Disjoint (Source.starImage H K) (Source.starImage H L₁) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxX
    have hz : (⟨x,hxK⟩ : Source.starImage H K) ∈ center (Source.starImage H K) := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (hcomm k ⟨x,hxX⟩).eq
    let eSL := e.trans Matrix.PSL3Two.equiv.symm
    have he := (centerCongr eSL ⟨⟨x,hxK⟩,hz⟩).property
    change eSL ⟨x,hxK⟩ ∈ center Matrix.PSL3Two.SL at he
    rw [Matrix.PSL3Two.center_eq_bot, mem_bot] at he
    exact congrArg Subtype.val (eSL.injective (he.trans (map_one eSL).symm))
  have hF : fittingSubgroup (Source.Hstar H) ≤ Source.starImage H L₁ := by
    rw [← fittingPreimageResidual_star H]
    rcases hfit with h | h
    · simp [h, Source.starImage]
    · exact (congrArg (Source.starImage H) h).le
  have hstar : Source.starImage H K ⊔ Source.starImage H L₁ ⊔
      Source.starImage H (T : Subgroup G) = ⊤ := by
    rw [← star_sup H K L₁ hKH hLH,
      ← star_sup H (K ⊔ L₁) (T : Subgroup G) (sup_le hKH hLH) hTH,
      d.generated]
    simp [Source.starImage, subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have htwo : IsPGroup 2 (Source.starImage H (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map _
  have hfit' := fitting_of_cubic_supplement _ _ _ hqs hcard htwo hstar hF
  have hsurj : Function.Surjective (sourceConjugation H K) := by
    intro a
    obtain ⟨z, hz⟩ := f.surjective (MulAut.congr e a)
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ z
    refine ⟨b, ?_⟩
    apply MulEquiv.ext
    intro k
    apply e.injective
    rw [← hf, hz]
    simp
  have hs : PairedStructure (Source.starImage H K) (Source.starImage H L₁) :=
    ⟨hcard, hcomm, hdis, hfit', hsurj⟩
  have hfaith := ParabolicMarking.faithful_of_source_centralizer act hcentralizer
  have hnoncentral : ∃ k : Source.starImage H K, ∃ v, act.representation k v ≠ v := by
    by_contra! hh
    have hall : ∀ k : Source.starImage H K, (k : Source.Hstar H) = 1 := by
      intro k
      apply hfaith
      ext v
      simpa using hh k v
    have hb : Source.starImage H K = ⊥ := bot_unique (fun k hk => hall ⟨k,hk⟩)
    let hnK : Nontrivial (Source.starImage H K) := e.surjective.nontrivial
    exact (nontrivial_iff_ne_bot _).mp hnK hb
  exact source_paired_configuration_exclusion H V₃ V₁ act K L₁
    (e.trans Matrix.PSL3Two.equiv.symm) hs hgen hnoncentral hS hND hsmall

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
