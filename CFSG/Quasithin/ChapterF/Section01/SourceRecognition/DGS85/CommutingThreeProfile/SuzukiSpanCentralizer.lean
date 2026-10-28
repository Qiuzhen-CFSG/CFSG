module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices

/-!
# Centralizers in a neighboring Suzuki span

Let x and y be neighbors of a linear vertex m. Suppose M is normalized
by the full middle stabilizer and V_x intersect Q_y centralizes M.
The centralizer of M in V_x is either that intersection or all of V_x.

Choose the actual full-edge complement fixing x. It normalizes both the
centralizer and M. In the original Suzuki quotient at y, the image of
this centralizer is an elementary subgroup of a Sylow center invariant
under the full Borel. Suzuki torus transitivity makes a nonzero image the
whole Sylow center. Lifting through the literal core kernel proves the
dichotomy. No critical-pair or classification conclusion is assumed.

SuzukiSecondKernelCentralizer excludes the full-centralization branch for
the actual elementary second-kernel span. The implementation import reuses
the existing private full-edge complement construction without changing
its public boundary.
Source: DGS85, Groups and Graphs, (12.3)(a), (12.9), pp.179,188.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- A full-middle-invariant subgroup has only two possible centralizers in the neighboring span. -/
theorem source_suzuki_span_centralizer_dichotomy
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {x m : Vertex (reducedFamily L S)}
    (hxm : (graph (reducedFamily L S)).Adj x m)
    (hym : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) m)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SL(2,k))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) m ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (M : Subgroup (G₀ L S))
    (hM : stabilizer (reducedFamily L S) m ≤ normalizer (M : Set (G₀ L S)))
    (hC : V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) i) ≤
      centralizer (M : Set (G₀ L S))) :
    let F := reducedFamily L S
    V F x 1 ⊓ centralizer (M : Set (G₀ L S)) = V F x 1 ⊓ Q F (base F i) ∨
      V F x 1 ≤ centralizer (M : Set (G₀ L S)) := by
  let F := reducedFamily L S
  let A := star L S i
  let E := stabilizer F m ⊓ stabilizer F (base F i)
  let X := V F x 1
  let C := X ⊓ centralizer (M : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hXQ : X ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb hxm
  have hXA : X ≤ A := (hXQ.trans (le_sup_left.trans hR.ge)).trans (map_subtype_le _)
  let : IsElementaryAbelian 2 X := V_elementary F (reduced_triple h).generate hZ
    (reduced_kernel_sylow h) hb x
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ X from inf_le_left)
  let : IsElementaryAbelian 2 (C.subgroupOf A) :=
    IsElementaryAbelian.subgroupOf (inf_le_left.trans hXA : C ≤ A)
  let f := ((originalQuotient h i).symm.trans eSuz).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let D := (C.subgroupOf A).map f
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map f
  have hk : f.ker = (Q F (base F i)).subgroupOf A := by
    have hh : f.ker = pCore 2 A := by
      ext v
      change eSuz ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v)) = 1 ↔ _
      rw [map_eq_one_iff _ eSuz.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff v
    rw [hh, ←star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
  by_cases hzero : D = ⊥
  · left
    apply le_antisymm
    · have hh := (map_eq_bot_iff (C.subgroupOf A)).mp hzero
      rw [hk] at hh
      intro c hc
      exact ⟨hc.1,hh (show (⟨c,hXA hc.1⟩ : A) ∈ C.subgroupOf A from hc)⟩
    · exact le_inf inf_le_left hC
  · right
    have hne : base F i ≠ x := by
      intro he
      apply hzero
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [hk]
      exact comap_mono (inf_le_left.trans (he ▸ V_le_Q F (reduced_triple h).generate hZ
        (reduced_kernel_sylow h) hb x))
    obtain ⟨K,hK,hodd,hKx⟩ := source_middle_edge_complement h i eLin hxm hym hne
    obtain ⟨T,hTN,hsup⟩ := source_quotient_edge_complement_supplement h i hym eSuz K hK hodd
    have hDN : D ≤ normalizer (T : Set (SuzukiMatrixGroup n)) := by
      apply map_le_iff_le_comap.mpr
      rw [hTN]
      intro c hc
      exact Q_le_stabilizer F m (hXQ hc.1)
    have hDT : D ≤ T := by
      rw [←inf_eq_left.mpr hDN,(IsElementaryAbelian.isPGroup 2 D).inf_normalizer_sylow T]
      exact inf_le_right
    have hDZ : D ≤ (center T).map (T : Subgroup (SuzukiMatrixGroup n)).subtype := by
      rw [←suzukiSylow_omega_eq_center hn (MulEquiv.refl _) T,←omegaOneAmbient_eq_self D]
      exact omegaOneAmbient_mono hDT
    have hnD : normalizer (T : Set (SuzukiMatrixGroup n)) ≤ normalizer (D : Set _) := by
      rw [←hsup]
      apply sup_le
      · apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
        intro d hd t ht
        obtain ⟨d',hd',he⟩ := hDZ hd
        rw [←he]
        exact congrArg Subtype.val ((mem_center_iff.mp hd') ⟨t,ht⟩)
      · have hnC : (K.map E.subtype).subgroupOf A ≤ normalizer (C.subgroupOf A : Set A) := by
          intro c hc
          apply le_normalizer_comap A.subtype
          apply inf_normalizer_le_normalizer_inf
          exact ⟨stabilizer_normalizes_V F x 1 (hKx hc),
            normalizer_le_normalizer_centralizer M (hM (show (c : G₀ L S) ∈ stabilizer F m from
              (map_subtype_le K hc).1))⟩
        exact (map_mono hnC).trans ((C.subgroupOf A).le_normalizer_map f)
    have hD := suzuki_elementary_eq_center_of_borel_normalized hn (MulEquiv.refl _) T D hDT hzero hnD
    have hXN : (X.subgroupOf A).map f ≤ normalizer (T : Set (SuzukiMatrixGroup n)) := by
      apply map_le_iff_le_comap.mpr
      rw [hTN]
      intro c hc
      exact Q_le_stabilizer F m (hXQ hc)
    let : IsElementaryAbelian 2 (X.subgroupOf A) := IsElementaryAbelian.subgroupOf hXA
    let : IsElementaryAbelian 2 ((X.subgroupOf A).map f) := IsElementaryAbelian.map f
    have hXT : (X.subgroupOf A).map f ≤ T := by
      rw [←inf_eq_left.mpr hXN,
        (IsElementaryAbelian.isPGroup 2 ((X.subgroupOf A).map f)).inf_normalizer_sylow T]
      exact inf_le_right
    have hXD : (X.subgroupOf A).map f ≤ D := by
      rw [hD,←suzukiSylow_omega_eq_center hn (MulEquiv.refl _) T,
        ←omegaOneAmbient_eq_self ((X.subgroupOf A).map f)]
      exact omegaOneAmbient_mono hXT
    intro x hx
    obtain ⟨c,hc,hfx⟩ := hXD (mem_map_of_mem f (show (⟨x,hXA hx⟩ : A) ∈ X.subgroupOf A from hx))
    have hd : (⟨x,hXA hx⟩ : A) * c⁻¹ ∈ f.ker := by
      change f ((⟨x,hXA hx⟩ : A) * c⁻¹) = 1
      rw [map_mul,map_inv,hfx, mul_inv_cancel]
    have hdQ : x * (c : G₀ L S)⁻¹ ∈ Q F (base F i) := by
      rw [hk] at hd
      exact hd
    have hdX : x * (c : G₀ L S)⁻¹ ∈ X := X.mul_mem hx (X.inv_mem hc.1)
    have hh := (centralizer (M : Set (G₀ L S))).mul_mem (hC ⟨hdX,hdQ⟩) hc.2
    change x * (c : G₀ L S)⁻¹ * c ∈ centralizer (M : Set (G₀ L S)) at hh
    simpa only [inv_mul_cancel_right] using hh

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
