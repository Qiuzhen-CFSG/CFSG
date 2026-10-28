module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SmallSuzukiMinimalNinePath
public import Theory.SpecificGroups.Suzuki.SylowOmegaIndex
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullSecondKernel

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups Pointwise
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem model_elementary_index
    {M : Type*} [Group M] [Finite M]
    (A Q E : Subgroup G) [IsElementaryAbelian 2 E]
    (f : A →* M) (hQ : Q = f.ker.map A.subtype) (hEA : E ≤ A)
    {q : ℕ} (hbound : ∀ D : Subgroup M, IsElementaryAbelian 2 D → Nat.card D ≤ q) :
    Q.relIndex E ≤ q := by
  let D := E.subgroupOf A
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hEA).toMonoidHom (subgroupOfEquivOfLe hEA).injective
  have hkernel : Q.subgroupOf A = f.ker := by
    rw [hQ]
    exact comap_map_eq_self (by simp)
  rw [←relIndex_subgroupOf (H := Q) hEA,hkernel,relIndex_ker]
  exact hbound _ (IsElementaryAbelian.map f)

private theorem linear_elementary_card {k : Type*} [Field k] [Finite k] [CharP k 2]
    (D : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) [IsElementaryAbelian 2 D] :
    Nat.card D ≤ Nat.card k := by
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_le_sylow
  exact (Nat.card_le_card_of_injective (inclusion hT) (inclusion_injective _)).trans_eq
    ((Nat.card_congr (T.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow k 2)).toEquiv).trans
      (Matrix.SpecialLinearGroup.card_upperUnipotent k))

private theorem small_suzuki_base_elementary_index
    {M : Type*} [Group M] [Finite M]
    (h : HypothesisF11 L S) (i : Bool)
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* M)
    (he : graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) i) = star L S i)
    {q : ℕ} (hbound : ∀ D : Subgroup M, IsElementaryAbelian 2 D → Nat.card D ≤ q)
    (E : Subgroup (G₀ L S)) [IsElementaryAbelian 2 E]
    (hE : E ≤ stabilizer (reducedFamily L S) (base (reducedFamily L S) i)) :
    (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex E ≤ q := by
  let F := reducedFamily L S
  let A := star L S i
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let eA := (originalQuotient h i).symm.trans e
  let f := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hk : f.ker = pCore 2 A := by
    ext t
    change eA (QuotientGroup.mk' (pCore 2 A) t) = 1 ↔ _
    rw [map_eq_one_iff _ eA.injective]
    exact QuotientGroup.eq_one_iff t
  have hEA : E ≤ A := by
    change E ≤ star L S i
    rw [←he]
    exact pGroup_le_sylowGenerated _ E hE (IsElementaryAbelian.isPGroup 2 E)
  apply model_elementary_index A _ E f _ hEA hbound
  rw [hk]
  exact (star_core h i).symm

private theorem small_suzuki_elementary_card
    (D : Subgroup (SuzukiMatrixGroup 0)) [IsElementaryAbelian 2 D] :
    Nat.card D ≤ 2 := by
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_le_sylow
  have hD : D ≤ omegaOneAmbient (T : Subgroup _) := by
    rw [←omegaOneAmbient_eq_self D]
    exact omegaOneAmbient_mono hT
  let : IsCyclic T := by
    let P : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard
        (zpowers suzukiZeroRootGenerator) (by
      rw [Nat.card_zpowers, suzukiZeroRootGenerator_order, suzukiZero_card]
      decide +kernel)
    let : IsCyclic P := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
    exact (Sylow.equiv P T).isCyclic.mp inferInstance
  have hcent : (T : Subgroup (SuzukiMatrixGroup 0)) ≤
      centralizer ((T : Subgroup (SuzukiMatrixGroup 0)) : Set (SuzukiMatrixGroup 0)) := by
    intro x hx y hy
    have hz : (⟨x,hx⟩ : T) ∈ center T := by
      rw [center_eq_top]
      trivial
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)
  have hDcenter : D ≤ omegaCenterIn (T : Subgroup (SuzukiMatrixGroup 0)) := by
    intro x hx
    apply (mem_omegaCenterIn_iff (T : Subgroup (SuzukiMatrixGroup 0)) x).mpr
    refine ⟨hT hx, ?_, elemPow_eq_one_of_isElementaryAbelian x hx⟩
    exact hcent (hT hx)
  have hcard := (suzukiSylow_omegaCenter_card_index 0 T).1
  exact (Nat.card_le_card_of_injective (inclusion hDcenter) (inclusion_injective _)).trans_eq hcard

theorem source_small_suzuki_elementary_local_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) 
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (hq : Nat.card k = 2)
    (v : Vertex (reducedFamily L S)) (E : Subgroup (G₀ L S))
    [IsElementaryAbelian 2 E] (hE : E ≤ stabilizer (reducedFamily L S) v) :
    (Q (reducedFamily L S) v).relIndex E ≤ 2 := by
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let E₀ := E.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map _
  have hE₀ : E₀ ≤ stabilizer F (base F v.type) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hE
    rw [←stabilizer_translate,←hg,inv_smul_smul] at hh
    exact hh
  have hi : (Q F (base F v.type)).relIndex E₀ ≤ 2 := by
    by_cases hv : v.type = i
    · rw [hv] at hE₀ ⊢
      exact small_suzuki_base_elementary_index h i eLin (source_linear_graphLocalGroup_eq_star h i eLin)
        (fun D hD => by let := hD; exact (linear_elementary_card D).trans_eq hq) E₀ hE₀
    · have hv : v.type = !i := Bool.eq_not_iff.mpr hv
      rw [hv] at hE₀ ⊢
      exact small_suzuki_base_elementary_index h (!i) eSuz (source_suzuki_graphLocalGroup_eq_star h (!i) eSuz)
        (fun D hD => by let := hD; exact small_suzuki_elementary_card D) E₀ hE₀
  have hmap := relIndex_map_map_of_injective (Q F v) E (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective
  rw [←Q_translate,←hg,inv_smul_smul] at hmap
  rw [hg] at hmap
  exact hmap ▸ hi

private theorem elementary_path_card
    (F : Bool → Subgroup G) [∀ j, Finite (F j)] {q : ℕ}
    (hstep : ∀ v w : Vertex F, (graph F).Adj v w →
      ∀ (E : Subgroup G), IsElementaryAbelian 2 E → E ≤ stabilizer F v →
        (stabilizer F w).relIndex E ≤ q)
    {d : ℕ} {a : Vertex F} (p : BasedWalk (graph F) d a)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : E ≤ stabilizer F a) :
    Nat.card E ≤ q^d * Nat.card (E ⊓ pathStabilizer F p : Subgroup G) := by
  induction d generalizing a E with
  | zero =>
    have he : E ⊓ pathStabilizer F p = E := by
      apply inf_eq_left.mpr
      intro g hg z hz
      have hz : z = a := by simpa only [BasedWalk.vertices,List.mem_singleton] using hz
      subst z
      exact hE hg
    rw [he,pow_zero,one_mul]
  | succ d ih =>
    let D := E ⊓ stabilizer F (p.1 : Vertex F)
    let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
      (inclusion (show D ≤ E from inf_le_left)) (inclusion_injective _)
    let : Finite E := Finite.of_injective (inclusion hE) (inclusion_injective _)
    let : Finite D := Finite.of_injective (inclusion (show D ≤ E from inf_le_left)) (inclusion_injective _)
    have hi : D.relIndex E ≤ q := by
      rw [show D = E ⊓ stabilizer F (p.1 : Vertex F) from rfl,inf_relIndex_left]
      exact hstep a p.1 p.1.property E inferInstance hE
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) D E bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hh
    have he : D ⊓ pathStabilizer F p.2 = E ⊓ pathStabilizer F p := by
      ext g
      constructor
      · rintro ⟨⟨hg,_⟩,hp⟩
        refine ⟨hg,?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hE hg
        · exact hp z hz
      · rintro ⟨hg,hp⟩
        have ht : g ∈ pathStabilizer F p.2 := fun z hz => hp z (List.mem_cons_of_mem _ hz)
        exact ⟨⟨hg,pathStabilizer_le F p.2 ht⟩,ht⟩
    have htail := ih p.2 D (show D ≤ stabilizer F (p.1 : Vertex F) from inf_le_right)
    rw [he] at htail
    calc
      Nat.card E = Nat.card D * D.relIndex E := hh.symm
      _ ≤ (q^d * Nat.card (E ⊓ pathStabilizer F p : Subgroup G)) * q := Nat.mul_le_mul htail hi
      _ = q^(d+1) * Nat.card (E ⊓ pathStabilizer F p : Subgroup G) := by ring

/-- An elementary subgroup of the second kernel has order at most q^5,
using the five remaining actions along an actual nine-path. -/

theorem source_small_suzuki_elementary_second_kernel_card_on_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) 
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup 0)
    (hq : Nat.card k = 2)
    {a : Vertex (reducedFamily L S)} (p : BasedWalk (graph (reducedFamily L S)) 9 a)
    (ho : Odd (Nat.card (pathStabilizer (reducedFamily L S) p)))
    (E : Subgroup (G₀ L S)) [IsElementaryAbelian 2 E]
    (hE : E ≤ ballKernel (reducedFamily L S) (p.2.1 : Vertex (reducedFamily L S)) 2) :
    Nat.card E ≤ 2^5 := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let q := 2
  have hstep (v w : Vertex F) (hvw : (graph F).Adj v w)
      (D : Subgroup (G₀ L S)) (hD : IsElementaryAbelian 2 D)
      (hDv : D ≤ stabilizer F v) : (stabilizer F w).relIndex D ≤ q := by
    let := hD
    let : Finite D := Finite.of_injective (inclusion hDv) (inclusion_injective _)
    apply (relIndex_le_of_le_left
      ((source_Z_Q_U (reduced_triple h) v).2.trans ((ballKernel_one_le_edge F hvw).trans inf_le_right))
      (by exact index_ne_zero_of_finite)).trans
    exact source_small_suzuki_elementary_local_index h i eLin eSuz hq v D hDv
  have hE1 : E ≤ ballKernel F (p.1 : Vertex F) 1 :=
    hE.trans (ballKernel_succ_le F p.2.1.property.symm 1)
  have hE3 : E ≤ ballKernel F (p.2.2.1 : Vertex F) 1 :=
    hE.trans (ballKernel_succ_le F p.2.2.1.property 1)
  have hE0 : E ≤ stabilizer F a :=
    hE1.trans ((ballKernel_one_le_edge F p.1.property.symm).trans inf_le_right)
  have hE4 : E ≤ stabilizer F (p.2.2.2.1 : Vertex F) :=
    hE3.trans ((ballKernel_one_le_edge F p.2.2.2.1.property).trans inf_le_right)
  let : Finite E := Finite.of_injective (inclusion hE0) (inclusion_injective _)
  let : Finite (pathStabilizer F p) := Finite.of_injective
    (inclusion (pathStabilizer_le F p)) (inclusion_injective _)
  obtain ⟨r,hr⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hd : Disjoint E (pathStabilizer F p) := disjoint_of_coprime_natCard (by
    rw [hr]; exact ho.coprime_two_left.pow_left r)
  have hfix : E ⊓ pathStabilizer F p.2.2.2.2 = ⊥ := by
    apply bot_unique
    apply (show E ⊓ pathStabilizer F p.2.2.2.2 ≤ E ⊓ pathStabilizer F p from ?_).trans hd.eq_bot.le
    apply le_inf inf_le_left
    intro g hg z hz
    change z ∈ a :: (p.1 : Vertex F) :: (p.2.1 : Vertex F) ::
      (p.2.2.1 : Vertex F) :: p.2.2.2.2.vertices at hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | rfl | rfl | rfl | hz
    · exact hE0 hg.1
    · exact ballKernel_le_stabilizer F _ 1 (hE1 hg.1)
    · exact ballKernel_le_stabilizer F _ 2 (hE hg.1)
    · exact ballKernel_le_stabilizer F _ 1 (hE3 hg.1)
    · exact hg.2 z hz
  have hb := elementary_path_card F hstep p.2.2.2.2 E hE4
  simpa only [hfix,card_bot,mul_one] using hb


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
