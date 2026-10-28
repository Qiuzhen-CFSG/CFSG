module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSourceUpperBound
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFullSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiThirdLayer
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry

/-!
# Involutions in the full second and third kernels

An elementary subgroup of either marked local quotient has order at most q:
use an SL₂(q) root group on the linear side and the first omega of a Suzuki
Sylow subgroup on the other side. These are images of the actual local actor,
so each successive vertex stabilizer has index at most q in an elementary
path actor.

An elementary subgroup of the radius-two kernel fixes five consecutive
vertices of a nine-path centered at its third vertex. The remaining five
local actions, together with the already proved odd nine-path fixer, bound
its order by q⁵. The Suzuki span V_y has that order and is central in the
full second kernel. Adjoining any involution therefore gives another
elementary subgroup of the same size, proving Ω₁(G_y^(2)) = V_y.

The exact intersection with the third kernel at the adjacent linear vertex
then gives Ω₁(G_m^(3)) = V_x ∩ V_y, with the literal original inclusion maps.
This supplies the omega identity used on printed p.188 without an assumed
eight-path supplement. Equality of the entire third kernel with this
intersection is not asserted: elements of higher order still need exclusion.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.7)--(12.9), printed pp.184--188. All earlier source hypotheses and the
nonbinary Suzuki marking are retained from the full-third-kernel consumer.
-/

public noncomputable section
open Subgroup SimpleGraph
open scoped MatrixGroups IsMulCommutative
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

private theorem suzuki_elementary_card {n : ℕ} (hn : 0 < n)
    (D : Subgroup (SuzukiMatrixGroup n)) [IsElementaryAbelian 2 D] :
    Nat.card D ≤ 2^(2*n+1) := by
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_le_sylow
  have hD : D ≤ omegaOneAmbient (T : Subgroup _) := by
    rw [←omegaOneAmbient_eq_self D]
    exact omegaOneAmbient_mono hT
  exact (Nat.card_le_card_of_injective (inclusion hD) (inclusion_injective _)).trans_eq
    (suzukiSylow_omega_card hn (MulEquiv.refl _) T)

private theorem linear_elementary_card {k : Type*} [Field k] [Finite k] [CharP k 2]
    (D : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) [IsElementaryAbelian 2 D] :
    Nat.card D ≤ Nat.card k := by
  obtain ⟨T,hT⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_le_sylow
  exact (Nat.card_le_card_of_injective (inclusion hT) (inclusion_injective _)).trans_eq
    ((Nat.card_congr (T.equiv (Matrix.SpecialLinearGroup.upperUnipotentSylow k 2)).toEquiv).trans
      (Matrix.SpecialLinearGroup.card_upperUnipotent k))

private theorem base_elementary_index
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

/-- Every elementary local actor has at most q images in the literal core quotient. -/
theorem source_linear_suzuki_elementary_local_index
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hq : Nat.card k = 2^(2*n+1))
    (v : Vertex (reducedFamily L S)) (E : Subgroup (G₀ L S))
    [IsElementaryAbelian 2 E] (hE : E ≤ stabilizer (reducedFamily L S) v) :
    (Q (reducedFamily L S) v).relIndex E ≤ 2^(2*n+1) := by
  let F := reducedFamily L S
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  let E₀ := E.map (MulAut.conj g⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 E₀ := IsElementaryAbelian.map _
  have hE₀ : E₀ ≤ stabilizer F (base F v.type) := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hE
    rw [←stabilizer_translate,←hg,inv_smul_smul] at hh
    exact hh
  have hi : (Q F (base F v.type)).relIndex E₀ ≤ 2^(2*n+1) := by
    by_cases hv : v.type = i
    · rw [hv] at hE₀ ⊢
      exact base_elementary_index h i eLin (source_linear_graphLocalGroup_eq_star h i eLin)
        (fun D hD => by let := hD; exact (linear_elementary_card D).trans_eq hq) E₀ hE₀
    · have hv : v.type = !i := Bool.eq_not_iff.mpr hv
      rw [hv] at hE₀ ⊢
      exact base_elementary_index h (!i) eSuz (source_suzuki_graphLocalGroup_eq_star h (!i) eSuz)
        (fun D hD => by let := hD; exact suzuki_elementary_card hn D) E₀ hE₀
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
theorem source_linear_suzuki_elementary_second_kernel_card_on_path
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) {n : ℕ} (hn : 0 < n)
    (eLin : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SL(2,k))
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hq : Nat.card k = 2^(2*n+1))
    {a : Vertex (reducedFamily L S)} (p : BasedWalk (graph (reducedFamily L S)) 9 a)
    (ho : Odd (Nat.card (pathStabilizer (reducedFamily L S) p)))
    (E : Subgroup (G₀ L S)) [IsElementaryAbelian 2 E]
    (hE : E ≤ ballKernel (reducedFamily L S) (p.2.1 : Vertex (reducedFamily L S)) 2) :
    Nat.card E ≤ (2^(2*n+1))^5 := by
  let F := reducedFamily L S
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let q := 2^(2*n+1)
  have hstep (v w : Vertex F) (hvw : (graph F).Adj v w)
      (D : Subgroup (G₀ L S)) (hD : IsElementaryAbelian 2 D)
      (hDv : D ≤ stabilizer F v) : (stabilizer F w).relIndex D ≤ q := by
    let := hD
    let : Finite D := Finite.of_injective (inclusion hDv) (inclusion_injective _)
    apply (relIndex_le_of_le_left
      ((source_Z_Q_U (reduced_triple h) v).2.trans ((ballKernel_one_le_edge F hvw).trans inf_le_right))
      (by exact index_ne_zero_of_finite)).trans
    exact source_linear_suzuki_elementary_local_index h i hn eLin eSuz hq v D hDv
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

private theorem omega_eq_of_central_elementary_bound
    (K Y : Subgroup G) [Finite K] [IsElementaryAbelian 2 Y]
    (hYK : Y ≤ K) (hKY : K ≤ centralizer (Y : Set G))
    (hbound : ∀ E : Subgroup G, IsElementaryAbelian 2 E → E ≤ K → Nat.card E ≤ Nat.card Y) :
    omegaOneAmbient K = Y := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff K Y).mpr
    intro x hx hx2
    let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx2
    let : IsElementaryAbelian 2 (Y ⊔ zpowers x : Subgroup G) :=
      IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr (hKY hx))
    have hEK : Y ⊔ zpowers x ≤ K := sup_le hYK (zpowers_le.mpr hx)
    let : Finite (Y ⊔ zpowers x : Subgroup G) := Finite.of_injective (inclusion hEK) (inclusion_injective _)
    have he : Y = Y ⊔ zpowers x := eq_of_le_of_card_ge le_sup_left (hbound _ inferInstance hEK)
    rw [he]
    exact (show zpowers x ≤ Y ⊔ zpowers x from le_sup_right) (mem_zpowers x)
  · rw [←omegaOneAmbient_eq_self Y]
    exact omegaOneAmbient_mono hYK

/-- The full second kernel has no involutions outside its original span;
the full third kernel has precisely the geometric intersection as its first omega. -/
theorem source_suzuki_full_kernel_omegas
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb3 : b (reducedFamily L S) = 3)
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i))
    (hnat : Noncommuting.HasNaturalCenter (star L S i)
      (Z (reducedFamily L S) (base (reducedFamily L S) i))
      (Q (reducedFamily L S) (base (reducedFamily L S) i)))
    (hbranch : ⁅V (reducedFamily L S) x 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i)),
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1⁆ ≠ ⊥) :
    let F := reducedFamily L S
    let m := base F i
    let y := base F (!i)
    let H := V F x 1 ⊓ V F y 1
    omegaOneAmbient (ballKernel F y 2) = V F y 1 ∧
    omegaOneAmbient (ballKernel F m 3) = H ∧
    omegaOneAmbient ((ballKernel F y 2).map (G₀ L S).subtype) =
      (V F y 1).map (G₀ L S).subtype ∧
    omegaOneAmbient ((ballKernel F m 3).map (G₀ L S).subtype) =
      H.map (G₀ L S).subtype := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let Y := V F y 1
  let H := V F x 1 ⊓ Y
  let K := ballKernel F y 2
  let N := ballKernel F m 3
  let q := 2^(2*n+1)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hb : 2 < b F := by change 2 < b (reducedFamily L S); omega
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hYK : Y ≤ K := V_le_ballKernel F (reduced_triple h).generate y
    (by change 3 ≤ b (reducedFamily L S); omega)
  let : IsElementaryAbelian 2 Y := V_elementary F (reduced_triple h).generate
    (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_injective
    (inclusion (show H ≤ Y from inf_le_right)) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (ballKernel_le_stabilizer F y 2))
    (inclusion_injective _)
  have hYcard : Nat.card Y = q^5 :=
    (source_suzuki_center_layer_of_intersection h i hb hxadj hne T R hT hR e hz hcard hcardy
      hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat).2.1
  have hk : 4 ≤ Nat.card k := by
    rw [hfield]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ 2*n+1)
  have hQyA : Q F y ≤ star L S i := (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  have hcent : Q F y ⊓ centralizer (Y : Set (G₀ L S)) = K :=
    source_suzuki_second_kernel_centralizer h (!i) eSuz
      (by cases i <;> exact e) hk (by cases i <;> exact hQyA) (by cases i <;> exact hnat)
  have hbotodd : Odd (Nat.card (⊥ : Subgroup (G₀ L S))) := by simp
  obtain ⟨v₀,hv,hvn,_⟩ := source_mixed_odd_fixed_neighbor h i hn e eSuz Ry hRy hadj
    (⊥ : Subgroup (G₀ L S)) hbotodd bot_le
  obtain ⟨p,hpy,hp,_,_⟩ := source_mixed_odd_fixed_paths h i hn e eSuz Ry hRy
    (⊥ : Subgroup (G₀ L S)) hbotodd 7 hadj bot_le
  let t : BasedWalk (graph F) 9 v₀ := ⟨⟨m,hv.symm⟩,p⟩
  have ht : t.Nonbacktracking := by
    change (p.1 : Vertex F) ≠ v₀ ∧ p.Nonbacktracking
    exact ⟨hpy.symm ▸ hvn.symm,hp⟩
  have hot := (source_suzuki_every_nine_path_odd h i hb3 T hT e hz hcard hcardy
    hzy hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hmin hnat hxadj hne hbranch t ht).1
  have hOmega : omegaOneAmbient K = Y := by
    apply omega_eq_of_central_elementary_bound K Y hYK (hcent.ge.trans inf_le_right)
    intro E hE hEK
    let := hE
    rw [hYcard]
    apply source_linear_suzuki_elementary_second_kernel_card_on_path h i hn e eSuz hfield t hot E
    change E ≤ ballKernel F (p.1 : Vertex F) 2
    rw [hpy]
    exact hEK
  have hthird := source_suzuki_third_kernel_layer h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa hmin hnat
  have hHN : H ≤ N := hthird.2.2.1
  have hYN : Y ⊓ N = H := hthird.2.2.2.1
  have hN : omegaOneAmbient N = H := by
    apply le_antisymm
    · apply (le_inf (show omegaOneAmbient N ≤ Y from
          (omegaOneAmbient_mono (ballKernel_succ_le F hadj 2)).trans hOmega.le)
        (omegaOneAmbient_le N)).trans hYN.le
    · rw [←omegaOneAmbient_eq_self H]
      exact omegaOneAmbient_mono hHN
  refine ⟨hOmega,hN,?_,?_⟩
  · rw [←map_omegaOneAmbient_injective (G₀ L S).subtype (G₀ L S).subtype_injective,hOmega]
  · rw [←map_omegaOneAmbient_injective (G₀ L S).subtype (G₀ L S).subtype_injective,hN]

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
