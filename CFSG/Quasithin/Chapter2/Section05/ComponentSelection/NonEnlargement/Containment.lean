module
public import CFSG.Quasithin.Chapter2.Section05.ComponentFusion
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.KnownSimple
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The containing component in the original 2.5.6 normalizer

For a nontrivial S-normal subgroup E of S∩C(K), the source normalizer theorem
puts J=N_G(E) in Γ₀ and keeps the original S Sylow in J. The ordinary
component K of H is consequently a local C-component for that full Sylow.
The completed A.3.12 containment assertion, applied to the actual two-core
quotient and lifted back, supplies a unique C-component of J containing K.

No universal A.3.12 premise or proper-embedding conclusion is assumed.
Promoting this C-component to an ordinary component and excluding strict
enlargement are the later source steps. Source: Aschbacher–Smith 2.5.6,
printed p.554, using 1.2.4, printed p.505.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {M H K S T E : Subgroup G} {z : G}

/-- The source local-family containment theorem now has all earlier inputs supplied. -/
theorem unique_containing_cComponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : SourceTuple M H S T z) (hK : IsComponentIn K H) (hgen : H = K ⊔ S)
    (hE : E ≠ ⊥) (hEC : E ≤ S ⊓ centralizer (K : Set G))
    (hSE : S ≤ normalizer (E : Set G)) :
    ∃! L : Subgroup G,
      L ∈ Chapter1.cComponentsIn (normalizer (E : Set G)) ∧ K ≤ L := by
  let J := normalizer (E : Set G)
  have hHJ : H ≤ J := normalizes_centralizer_subgroup hgen hEC hSE
  have hKJ : K ≤ J := hK.1.trans hHJ
  obtain ⟨hJ,⟨P,hP⟩,_⟩ := centralizer_subgroup_normalizer d hgen hE hEC hSE
  have hHgam : H ∈ gamma (Chapter1.He G) M :=
    d.gamma_zero.elim (fun h => h.1.1) (fun h => h.1)
  have hJgam : J ∈ gamma (Chapter1.He G) M :=
    hJ.elim (fun h => h.1.1) (fun h => h.1)
  obtain ⟨R,hR⟩ := d.sylow_intersection
  obtain ⟨Q,hQ⟩ := (intersection_sylow hHgam R).2
  have hQS : (Q : Subgroup H).map H.subtype = S := hQ.trans hR
  have hKL : K ∈ Chapter1.L G S :=
    Chapter1.mem_L_of_cComponent hHgam.1 ⟨Q,hQS⟩ hK.1 hK.2.isCComponent
  have hKLP : K.subgroupOf J ∈ Chapter1.L J (P : Subgroup J) := by
    apply (Chapter1.mem_L_map_iff J.subtype J.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hKJ,hP]
    exact hKL
  apply (Chapter1.existsUnique_cComponentsIn_iff hKJ).mp
  apply Chapter1.Section02.lemma_1_2_4_containment_of_A_3_12
    (fun X _ _ hX hO U B hB =>
      ChapterA.Section03.SourceComponents.containment_knownSimple hX hO U B hB)
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hJgam.1) P hKLP

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NonEnlargement
