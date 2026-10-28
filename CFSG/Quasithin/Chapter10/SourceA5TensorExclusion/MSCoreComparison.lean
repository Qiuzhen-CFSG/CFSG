module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSBlockFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.NonFrattini

/-!
# Critical indices for the original non-Frattini tensor component

At distance two, an intrinsic core escaping the Frattini-central layer forces
both literal critical indices to be four. The original tensor setup supplies
the faithful simple component and the MS conditions; no failed-comparison,
inner-action or plane hypothesis remains. This supplies the numerical start
of the symplectic branch in MS93 (3.6), pp.870--871. The subsequent secondary
orbit argument is still required to identify the whole intrinsic core.
-/

public section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem source_tensor_sp4_nonfrattini_critical_indices
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g)
    (hlarge : ¬ (ChapterC.blockU K).map K.subtype ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {z : Vertex R}, CriticalPath R geometry (alpha R) z →
        (Q R z).relIndex (Z R (alpha R)) = 4 ∧
          (Q R (alpha R)).relIndex (Z R z) = 4 := by
  let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D hn H hRH hLH hout hs K hK hF eK hfit hprod
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  obtain ⟨_,hfaith,_⟩ :=
    source_tensor_sp4_msCentralOrbit D hn H hRH hLH hout hs K hK hF eK hfit hprod
  have hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := H))
  have hRne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hres : pResidual 2 H = K := component_eq_residual K R hK hodd.isPGroup hprod
  let : ((pResidual 2 H).map q).Normal := hres ▸ inferInstance
  let : IsSimpleGroup ((pResidual 2 H).map q) := hres ▸ inferInstance
  let : IsQuasisimple ((pResidual 2 H).map q) := hres ▸ inferInstance
  have hc' : Nat.card ((pResidual 2 H).map q) = 979200 := by rw [hres]; exact hc
  have hBC' : centralizer ((pResidual 2 H).map q : Set (H ⧸ pCore 2 H)) = ⊥ := by rw [hres]; exact hBC
  have hsq' : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q) := by rw [hres]; exact hsq
  have hgraph := ChapterC.RankTwo.Sp4Four.CoreReconstruction.graph_core_nonfrattini_of_intrinsic
    K R hodd.isPGroup hodd.twoCore_le hres hlarge
  dsimp only
  intro geometry hb z path
  exact ChapterC.RankTwo.Sp4Four.CoreReconstruction.original_critical_indices_eq_four_of_nonfrattini
    R hms hodd.isPGroup hRne hodd.twoCore_le hself hfaith q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hc' hBC' hsq' path hb hgraph

/-- The first source3.6 split either recognizes the whole original block or
forces the two critical indices4 for every chosen distance-two critical path. -/
theorem source_tensor_sp4_block_or_nonfrattini_indices
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k*r=g) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    ChapterC.IsSp4FourBlock K ∨
      (∀ (geometry : Geometry R), geometry.b R = 2 →
        ∀ {z : Vertex R}, CriticalPath R geometry (alpha R) z →
          (Q R z).relIndex (Z R (alpha R)) = 4 ∧
            (Q R (alpha R)).relIndex (Z R z) = 4) := by
  by_cases hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)
  · exact Or.inl (source_tensor_sp4_block_of_frattini_small D hn H hRH hLH hout hs
      K hK hF eK hfit hprod hsmall)
  · apply Or.inr
    apply source_tensor_sp4_nonfrattini_critical_indices D hn H hRH hLH hout hs
      K hK hF eK hfit hprod
    obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
    have hres := component_eq_residual K
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H) hK hodd.isPGroup hprod
    let : K.Normal := hres ▸ inferInstance
    have hperfect : IsPPerfect 2 K := hres ▸ isPPerfect_pResidual 2
    rw [commutatorCore_eq_intrinsic K hperfect] at hsmall
    exact hsmall

end CFSG.Quasithin.Chapter10
