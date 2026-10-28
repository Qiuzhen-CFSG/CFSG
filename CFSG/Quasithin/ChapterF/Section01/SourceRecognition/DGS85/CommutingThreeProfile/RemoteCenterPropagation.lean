module
public import Theory.SpecificGroups.Suzuki.DistinctOmegaGeneration
public import Theory.GroupTheory.CentralizerInjectiveImage
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CoreGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommonSylowIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommutatorGeometry
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Neighborhood

/-!
# Propagation from the prescribed remote Suzuki centers

The two remote centers on opposite sides of a Suzuki vertex have elementary
images of order q in the Sylows attached to its two distinct neighbors.
Their images are therefore the full Sylow omegas. Distinct-omega generation
shows that these actual centers generate the star modulo its two-core,
with the original completion inclusion preserved.

This generated subgroup is transitive on the middle neighborhood because
the two-core fixes it pointwise. A subgroup centralizing both remote centers
and lying in the two middle cores consequently centralizes every conjugate
of the adjacent center, hence the whole middle span. NinePathCentralizer
supplies the literal path application and derives the order-q indices from
critical-center saturation; they are genuine earlier premises here.

Source: DGS85, Groups and Graphs, (12.7), printed p.184, the paragraph
beginning “By (12.5) and (**)”. This is the positive Suzuki parameter case.
It does not yet eliminate the remaining centralizing path subgroup.
-/

public noncomputable section
open Subgroup
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The two actual remote centers generate the starred quotient at their middle vertex. -/
theorem source_suzuki_remote_center_pair
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    {a c z : Vertex (reducedFamily L S)}
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hne : z ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (haQ : Z (reducedFamily L S) a ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcQ : Z (reducedFamily L S) c ≤ Q (reducedFamily L S) z)
    (hia : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex (Z (reducedFamily L S) a) = 2^(2*n+1))
    (hic : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex (Z (reducedFamily L S) c) = 2^(2*n+1)) :
    let F := reducedFamily L S
    (Z F a ⊔ Z F c) ⊔ Q F (base F i) = star L S i ∧
    ((Z F a).map (G₀ L S).subtype ⊔ (Z F c).map (G₀ L S).subtype) ⊔
      (Q F (base F i)).map (G₀ L S).subtype = starredParabolic L S (if i then 1 else 0) := by
  let F := reducedFamily L S
  let A := star L S i
  let y := base F i
  let m := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (star_le_stabilizer i)) (inclusion_injective _)
  let f := ((originalQuotient h i).symm.trans e).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := ((originalQuotient h i).symm.trans e).surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 A := by
    ext t
    change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) t)) = 1 ↔ t ∈ pCore 2 A
    rw [map_eq_one_iff _ e.injective,map_eq_one_iff _ (originalQuotient h i).symm.injective]
    exact QuotientGroup.eq_one_iff t
  have hkQ : f.ker = (Q F y).subgroupOf A := by
    rw [hk,←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective _).symm
  have hmA : Q F m ≤ A := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hzA : Q F z ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hyA : Q F y ≤ A := (le_sup_right.trans hT.ge).trans (map_subtype_le _)
  have haA := haQ.trans hmA
  have hcA := hcQ.trans hzA
  obtain ⟨P,hP,_,_⟩ := source_common_sylow_core_index h i e T hT
  obtain ⟨U,hU,_,_⟩ := source_common_sylow_core_index h i e R hR
  have himage (v w : Vertex F) (hv : Z F v ≤ Q F w) (hw : Q F w ≤ A)
      (P : Sylow 2 (SuzukiMatrixGroup n))
      (hP : ((Q F w).subgroupOf A).map f = P)
      (hi : (Q F y).relIndex (Z F v) = 2^(2*n+1)) :
      ((Z F v).subgroupOf A).map f = omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup n)) := by
    let E := ((Z F v).subgroupOf A).map f
    let := Z_elementary F (fun t => (source_Z_Q_U (reduced_triple h) t).1) v
    let : IsElementaryAbelian 2 ((Z F v).subgroupOf A) := IsElementaryAbelian.subgroupOf (hv.trans hw)
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
    have hEP : E ≤ (P : Subgroup (SuzukiMatrixGroup n)) := hP ▸ map_mono (subgroupOf_mono A hv)
    have hEO : E ≤ omegaOneAmbient (P : Subgroup (SuzukiMatrixGroup n)) := by
      rw [←omegaOneAmbient_eq_self E]
      exact omegaOneAmbient_mono hEP
    have hcard : Nat.card E = 2^(2*n+1) := by
      rw [←relIndex_ker,hkQ,relIndex_subgroupOf (hv.trans hw)]
      exact hi
    exact eq_of_le_of_card_ge hEO (by rw [suzukiSylow_omega_card hn (MulEquiv.refl _) P,hcard])
  have hEa := himage a m haQ hmA P hP hia
  have hEc := himage c z hcQ hzA U hU hic
  have hgen := star_three_core_generation h i hz hne T R hT hR
  have hPU : (P : Subgroup (SuzukiMatrixGroup n)) ⊔ U = ⊤ := by
    have he : (Q F m).subgroupOf A ⊔ (Q F z).subgroupOf A ⊔ (Q F y).subgroupOf A = ⊤ := by
      apply map_injective A.subtype_injective
      rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le hmA,
        map_subgroupOf_eq_of_le hzA,map_subgroupOf_eq_of_le hyA,
        ←MonoidHom.range_eq_map,range_subtype]
      exact hgen.symm
    have hh := congrArg (Subgroup.map f) he
    rw [Subgroup.map_sup,Subgroup.map_sup,hP,hU,←hkQ,Subgroup.map_ker_self,sup_bot_eq,
      Subgroup.map_top_of_surjective _ hf] at hh
    exact hh
  have hnePU : P ≠ U := by
    intro he
    rw [he,sup_idem] at hPU
    exact (suzuki_rankOneSylowFacts n U).proper.not_ge (hPU ▸ U.toSubgroup.le_normalizer)
  have htop : (((Z F a).subgroupOf A) ⊔ (Z F c).subgroupOf A).map f = ⊤ := by
    rw [Subgroup.map_sup,hEa,hEc]
    exact suzukiSylow_distinct_omega_sup_eq_top hn P U hnePU
  have he := congrArg (Subgroup.comap f) htop
  rw [comap_map_eq,comap_top,hk] at he
  have hh := congrArg (Subgroup.map A.subtype) he
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le haA,map_subgroupOf_eq_of_le hcA,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  change (Z F a ⊔ Z F c) ⊔ A.pCoreIn 2 = A at hh
  rw [star_core h i] at hh
  refine ⟨hh,?_⟩
  have ho := congrArg (Subgroup.map (G₀ L S).subtype) hh
  rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le (star_le_completion _)] at ho
  exact ho

/-- Centralizing the two remote centers propagates to the whole middle span. -/
theorem source_suzuki_remote_center_propagation
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    {a c z : Vertex (reducedFamily L S)}
    (hz : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) z)
    (hne : z ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) z ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (haQ : Z (reducedFamily L S) a ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcQ : Z (reducedFamily L S) c ≤ Q (reducedFamily L S) z)
    (hia : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex (Z (reducedFamily L S) a) = 2^(2*n+1))
    (hic : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex (Z (reducedFamily L S) c) = 2^(2*n+1))
    (D : Subgroup (G₀ L S))
    (hDy : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hDm : D ≤ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hDa : Z (reducedFamily L S) a ≤ centralizer (D : Set (G₀ L S)))
    (hDc : Z (reducedFamily L S) c ≤ centralizer (D : Set (G₀ L S))) :
    let F := reducedFamily L S
    V F (base F i) 1 ≤ centralizer (D : Set (G₀ L S)) ∧
    (V F (base F i) 1).map (G₀ L S).subtype ≤ centralizer (D.map (G₀ L S).subtype : Set G) := by
  let F := reducedFamily L S
  let A := star L S i
  let y := base F i
  let m := base F (!i)
  let E := Z F a ⊔ Z F c
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hgen := (source_suzuki_remote_center_pair h i hn e hz hne T R hT hR haQ hcQ hia hic).1
  have hEA : E ≤ A := le_sup_left.trans hgen.le
  have hQA : Q F y ≤ A := le_sup_right.trans hgen.le
  have hEC : E ≤ centralizer (D : Set (G₀ L S)) := sup_le hDa hDc
  have hbase : (graph F).Adj y m :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have htrans : ∀ v, (graph F).Adj y v → ∃ g ∈ E, g • m = v := by
    intro v hv
    obtain ⟨g,hg,hgv⟩ := star_locally_transitive h i hbase hv
    have hs : E.subgroupOf A ⊔ (Q F y).subgroupOf A = ⊤ := by
      apply map_injective A.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEA,map_subgroupOf_eq_of_le hQA,
        ←MonoidHom.range_eq_map,range_subtype]
      exact hgen
    let : ((Q F y).subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer
      ((star_le_stabilizer i).trans (stabilizer_normalizes_Q F y))
    obtain ⟨u,hu,q,hq,he⟩ := mem_sup_of_normal_right.mp
      (show (⟨g,hg⟩ : A) ∈ E.subgroupOf A ⊔ (Q F y).subgroupOf A from hs ▸ mem_top _)
    have hqm : (q : G₀ L S) • m = m := (source_Z_Q_U (reduced_triple h) y).2 hq m
      ((mem_ball_one F y m).mpr (.inl hbase))
    refine ⟨u,hu,?_⟩
    have he' := congrArg Subtype.val he
    change (u : G₀ L S) * (q : G₀ L S) = g at he'
    rw [←he',mul_smul,hqm] at hgv
    exact hgv
  have hV : V F y 1 ≤ centralizer (D : Set (G₀ L S)) := by
    rw [V_eq_center_sup_neighbor_conjugates F E (hEA.trans (star_le_stabilizer i)) hbase htrans]
    refine sup_le ?_ ?_
    · exact (Z_centralizes_Q F y (source_Z_Q_U (reduced_triple h) y).1).trans (centralizer_le hDy)
    · apply conjugateSpanBy_le
      · exact (Z_centralizes_Q F m (source_Z_Q_U (reduced_triple h) m).1).trans (centralizer_le hDm)
      · exact hEC.trans (centralizer (D : Set (G₀ L S))).le_normalizer
  refine ⟨hV,?_⟩
  rw [←inf_eq_left] at hV ⊢
  rw [map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,hV]


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
