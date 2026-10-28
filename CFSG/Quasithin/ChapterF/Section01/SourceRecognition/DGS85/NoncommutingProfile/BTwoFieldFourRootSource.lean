module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourFactorsSource
public import Theory.SpecificGroups.MinusExtraspecial.AnisotropicIntersection
public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition

/-!
# Root recognition of the original field-four alpha core

The original alpha center contains the beta center and lies in the adjacent
core intersection. Involution-centralizer rigidity in the actual minus
extraspecial beta core proves that the intersection has precisely the alpha
center as its centralizer in the alpha core. The self-centralization premise
is used only inside the original beta parabolic.

Together with the marked anisotropic factors and the balanced square fibers
of the original alpha cubic, this identifies the actual alpha core with
UT₃(F₄). All center and core embeddings are the original subgroup maps.
This core isomorphism supplies the two elementary planes for the subsequent
Cartan-invariant complement construction; it is not parabolic recognition.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985), (10.9),
printed p.163. Intrinsic root recognition uses Aschbacher, Sporadic Groups
(1994), 8.15 and 46.14, pp.29--30 and 257--258.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true
local instance rootSourceAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

private theorem factor_centralizer_transport
    (Q R Z : Subgroup G) [Finite R] (e : R ≃* MinusExtraspecial.Model)
    (hZeq : (center Q).map Q.subtype = Z)
    (hZR : Z ≤ R) (hZe : IsElementaryAbelian 2 Z)
    (hZ : Nat.card (center Q) = 4)
    (hcenter : (center R).map R.subtype ≤ Z)
    (hA : Nat.card (R.subgroupOf Q) = 16)
    (hn : Q ≤ normalizer (R : Set G))
    (hself : Q ⊓ centralizer (R : Set G) ≤ R) :
    centralizer (R.subgroupOf Q : Set Q) = center Q := by
  have hZQ : Z ≤ Q := hZeq ▸ map_subtype_le _
  have hZC : Z ≤ centralizer (Q : Set G) := by
    intro x hx
    rw [←hZeq] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    intro q hq
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨q,hq⟩)
  have hZcard : Nat.card Z = 4 := by
    rw [←hZeq,card_map_of_injective Q.subtype_injective,hZ]
  let ei : R.subgroupOf Q ≃ Q.subgroupOf R := {
    toFun x := ⟨⟨x,x.property⟩,x.val.property⟩
    invFun x := ⟨⟨x,x.property⟩,x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hI : Nat.card (Q.subgroupOf R) = 16 := (Nat.card_congr ei).symm.trans hA
  have hc := MinusExtraspecial.intersection_centralizer_eq Q R Z e
    hZQ hZR hZC hZcard hZe hcenter hI hn hself
  apply le_antisymm
  · intro x hx
    have hxZ : (x : G) ∈ Z := hc ▸ (show (x : G) ∈ Q ⊓ centralizer
        ((Q ⊓ R : Subgroup G) : Set G) from ⟨x.property,by
      intro y hy
      exact congrArg Subtype.val (hx ⟨y,hy.1⟩ hy.2)⟩)
    rw [←hZeq] at hxZ
    obtain ⟨y,hy,he⟩ := hxZ
    exact Q.subtype_injective he ▸ hy
  · exact center_le_centralizer _

theorem original_bTwo_field_four_factor_centralizer
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let A := ((parabolic L S 1).pCoreIn 2).subgroupOf Q₀
    centralizer (A : Set Q₀) = center Q₀ := by
  let ι := (G₀ L S).subtype
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₀ := (Z F₀ α).map ι
  let P₁ := parabolic L S 1
  let : Finite P₁ := h.finite_parabolic 1
  let : Finite Q₁ := Finite.of_injective (inclusion (pCoreIn_le 2 P₁)) (inclusion_injective _)
  let : IsElementaryAbelian 2 (Z F₀ α) := graph_Z_elementary (reduced_triple h) α
  have hZE : IsElementaryAbelian 2 Z₀ := IsElementaryAbelian.map ι
  obtain ⟨hA,hZ,hclass,hZA,z,hz,hsq⟩ := original_bTwo_field_four_anisotropic_intersection
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨hQcard,hcenter,hder,hPhi,hs⟩ := original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  change (center Q₀).map Q₀.subtype = Z₀ at hcenter
  have hZQ₁ : Z₀ ≤ Q₁ := hD.symm.le.trans inf_le_left
  obtain ⟨hExtra,⟨emodel⟩⟩ := original_bTwo_field_four_beta_recognition h hb c hactor
    hcentral ht hne hcomm hnot e hD E hK
  let : IsExtraspecial 2 Q₁ := hExtra
  have hD' : D F₀ β t = Z F₀ α := by
    apply map_injective (G₀ L S).subtype_injective
    change (Q F₀ β ⊓ Q F₀ t).map ι = _
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,reduced_base_Q_map h true]
    exact hD
  have hcore : Q₁ = (V F₀ β 1).map ι := original_bTwo_exceptional_beta_core h hb c ht hne hD'
  have hmap₁ : (Q F₀ β).map ι = Q₁ := reduced_base_Q_map h true
  have hZb : (center Q₁).map Q₁.subtype = (Z F₀ β).map ι := by
    rw [←IsExtraspecial.commutator_eq_center (p := 2),map_subtype_commutator]
    calc
      ⁅Q₁,Q₁⁆ = (⁅V F₀ β 1,Q F₀ β⁆).map ι := by rw [map_commutator,hmap₁,←hcore]
      _ = _ := congrArg (map ι) hcomm
  have hZbZ : (center Q₁).map Q₁.subtype ≤ Z₀ := by
    rw [hZb]
    exact map_mono (center_le_of_central_neighbor (reduced_triple h)
      (reduced_borel_core_sylow h) (reduced_vertex_sylow h) c.middle hcentral)
  have hQ₀P : Q₀ ≤ P₁ := by
    have hh : Q₀ ≤ (commonBorel L S).pCoreIn 2 := by
      rw [original_bTwo_borel_core_eq_product h c]
      exact le_sup_left
    exact hh.trans ((pCoreIn_le 2 _).trans (commonBorel_le_parabolic 1))
  have hn : P₁ ≤ normalizer (Q₁ : Set G) := by
    change P₁ ≤ normalizer (((pCore 2 P₁).map P₁.subtype : Subgroup G) : Set G)
    have hh := (pCore 2 P₁).le_normalizer_map P₁.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hself : Q₀ ⊓ centralizer (Q₁ : Set G) ≤ Q₁ := by
    rintro x ⟨hxQ,hxc⟩
    let xP : P₁ := ⟨x,hQ₀P hxQ⟩
    have hxC : xP ∈ centralizer (pCore 2 P₁ : Set P₁) := by
      intro y hy
      exact Subtype.ext (hxc y (mem_map_of_mem P₁.subtype hy))
    exact mem_map_of_mem P₁.subtype
      (((ChapterA.generalizedFitting_eq_pCore_iff 2).mp (h.characteristic_two 1)) hxC)
  exact factor_centralizer_transport Q₀ Q₁ Z₀ emodel hcenter hZQ₁ hZE hZ hZbZ hA
    (hQ₀P.trans hn) hself

theorem original_bTwo_field_four_alpha_root
    (h : HypothesisF11 L S) (hb : b F₀ = 2) {u t : Vertex F₀}
    (c : BTwoCenterActionData F₀ α β u k W)
    (hactor : c.actor = graphLocalGroup F₀ α)
    (hcentral : Z F₀ β ≤ centerIn (graphLocalGroup F₀ β))
    (ht : (graph F₀).Adj α t) (hne : t ≠ β)
    (hcomm : ⁅V F₀ β 1,Q F₀ β⁆ = Z F₀ β)
    (hnot : ¬ stabilizer F₀ α ≤ normalizer
      ((Q F₀ β ⊓ Q F₀ α : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (e : (L 1 ⧸ pCore 2 (L 1)) ≃* PSL(2,K))
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hK : Nat.card K = 4) :
    Nonempty (((parabolic L S 0).pCoreIn 2) ≃* Matrix.PSL3Four.RootNormalizerModel.Root) := by
  let Q₀ := (parabolic L S 0).pCoreIn 2
  let Q₁ := (parabolic L S 1).pCoreIn 2
  let Z₀ := (Z F₀ α).map (G₀ L S).subtype
  let A := Q₁.subgroupOf Q₀
  let : Finite (parabolic L S 0) := h.finite_parabolic 0
  let : Finite Q₀ := Finite.of_injective (inclusion (pCoreIn_le 2 (parabolic L S 0)))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 Q₀) := ⟨isPGroup_pCoreIn 2 _⟩
  obtain ⟨hA,a,ha,φ,hφ,hφapply,hmark,z,z',hz,hz',hne',hs,hsB,hB,hI,hgen,hbal⟩ :=
    original_bTwo_field_four_anisotropic_pair h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  obtain ⟨hQa,hZa,hder,hPhi,hsq⟩ := original_bTwo_field_four_structure
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK
  change (center Q₀).map Q₀.subtype = Z₀ at hZa
  change (frattini Q₀).map Q₀.subtype = Z₀ at hPhi
  let : IsElementaryAbelian 2 (Z F₀ α) := graph_Z_elementary (reduced_triple h) α
  let : IsElementaryAbelian 2 Z₀ := IsElementaryAbelian.map (G₀ L S).subtype
  let eZ : center Q₀ ≃* Z₀ :=
    ((center Q₀).equivMapOfInjective Q₀.subtype Q₀.subtype_injective).trans
      (MulEquiv.subgroupCongr hZa)
  have hZE : IsElementaryAbelian 2 (center Q₀) :=
    IsElementaryAbelian.of_injective eZ.toMonoidHom eZ.injective
  have hZcard := (original_bTwo_field_four_anisotropic_intersection
    h hb c hactor hcentral ht hne hcomm hnot e hD E hK).2.1
  have hPhiZ : frattini Q₀ = center Q₀ :=
    map_injective Q₀.subtype_injective (hPhi.trans hZa.symm)
  let F : Theory.GroupTheory.AnisotropicFactors Q₀ := {
    card := hQa
    center_card := hZcard
    center_elementary := hZE
    square_central := fun x => hPhiZ ▸ pth_power_mem_frattini_of_isPGroup (p := 2) x
    A := A
    B := A.map φ.toMonoidHom
    A_card := hA
    B_card := hB
    inf_eq := hI
    sup_eq := hgen
    z := z
    u := z'
    z_ne_one := hz
    u_ne_one := hz'
    distinct := hne'
    A_square := hs
    B_square := hsB
    centralizer_A := original_bTwo_field_four_factor_centralizer
      h hb c hactor hcentral ht hne hcomm hnot e hD E hK }
  exact Theory.GroupTheory.AnisotropicRecognition.rootEquiv_of_balanced F hbal

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
