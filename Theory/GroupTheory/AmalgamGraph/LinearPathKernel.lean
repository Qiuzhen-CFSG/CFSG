module
public import Theory.SpecificGroups.SL2.BorelSupplementAction
public import Theory.GroupTheory.AmalgamGraph.SylowGenerated
public import Theory.GroupTheory.AmalgamGraph.LocalAction
public import Theory.GroupTheory.PCoreImage

/-!
# Linear endpoint kernels of path supplements

A literal edge supplement restricts to a supplement in the Sylow-generated
local group. The matrix Borel argument then makes a nontrivial image of its
two-core transitive on the neighbors other than the marked one. If the
supplement is not transitive there, its core fixes every neighbor. The proof
uses the actual subgroup inclusions and the marked neighbor stabilizer; it
requires no finite completion and keeps the full local kernel distinct from
the vertex two-core.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 6.7--6.8(a), p.123.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups Pointwise
namespace Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- Every two-subgroup of a vertex lies in its Sylow-generated local group. -/
theorem pGroup_le_sylowGenerated (P A : Subgroup G) (hAP : A ≤ P)
    (hA : IsPGroup 2 A) : A ≤ sylowGenerated P := by
  have hp : IsPGroup 2 (A.subgroupOf P) := hA.comap_subtype
  obtain ⟨T,hT⟩ := hp.exists_le_sylow
  calc
    A = (A.subgroupOf P).map P.subtype := (map_subgroupOf_eq_of_le hAP).symm
    _ ≤ (T : Subgroup P).map P.subtype := map_mono hT
    _ ≤ sylowGenerated P := sylow_le_sylowGenerated P T

/-- Passing to the Sylow-generated local group preserves the vertex core. -/
theorem sylowGenerated_core (P : Subgroup G) [Finite P] :
    (sylowGenerated P).pCoreIn 2 = P.pCoreIn 2 := by
  apply le_antisymm (pCoreIn_mono_of_normalizes (sylowGenerated_le P)
    (sylowGenerated_normalized P))
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 P)
    (pGroup_le_sylowGenerated P _ (pCoreIn_le 2 P) (isPGroup_pCoreIn 2 P))
    ((sylowGenerated_le P).trans
      (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))))

private theorem restrict_product_supplement (E H S L : Subgroup G)
    (hHE : H ≤ E) (hSE : S ≤ E) (hSL : S ≤ L)
    (hprod : (E : Set G) = (H : Set G) * (S : Set G)) :
    H.subgroupOf L ⊔ S.subgroupOf L = E.subgroupOf L := by
  apply le_antisymm (sup_le (comap_mono hHE) (comap_mono hSE))
  intro x hx
  obtain ⟨a,ha,b,hb,hab⟩ := (show (x : G) ∈ (H : Set G) * (S : Set G) by
    rw [←hprod]; exact hx)
  have haL : a ∈ L := by
    have he : a = x * b⁻¹ := by rw [←hab, mul_inv_cancel_right]
    rw [he]
    exact L.mul_mem x.property (L.inv_mem (hSL hb))
  have hh : (⟨a,haL⟩ : L) * ⟨b,hSL hb⟩ = x := Subtype.ext hab
  rw [←hh]
  exact (H.subgroupOf L ⊔ S.subgroupOf L).mul_mem ((show H.subgroupOf L ≤ H.subgroupOf L ⊔ S.subgroupOf L from le_sup_left) ha)
    ((show S.subgroupOf L ≤ H.subgroupOf L ⊔ S.subgroupOf L from le_sup_right) hb)

variable (F : Bool → Subgroup G) {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The linear rank-one argument in DGS 6.8(a). A supplement which is not
transitive on the other neighbors has its two-core in the full local kernel.
The model input marks the actual neighbor stabilizer, not just a group tag. -/
theorem core_le_ballKernel_of_linear_supplement {v w : Vertex F}
    (H : Subgroup G)
    (hHE : H ≤ stabilizer F v ⊓ stabilizer F w)
    (q : sylowGenerated (stabilizer F v) →* Matrix.SpecialLinearGroup (Fin 2) K)
    (hq : Function.Surjective q)
    (hmark : (stabilizer F w).subgroupOf (sylowGenerated (stabilizer F v)) =
      (Matrix.SpecialLinearGroup.rankOneBorel K).comap q)
    (hprod : ((stabilizer F v ⊓ stabilizer F w : Subgroup G) : Set G) =
      (H : Set G) * ((stabilizer F v ⊓ stabilizer F w).pCoreIn 2 : Set G))
    (htrans : ∀ x : (graph F).neighborSet v,
      ∃ g ∈ sylowGenerated (stabilizer F v), g • w = x.val)
    (hnot : ¬ ∀ x y : (graph F).neighborSet v, x.val ≠ w → y.val ≠ w →
      ∃ g ∈ H, g • x.val = y.val) :
    H.pCoreIn 2 ≤ ballKernel F v 1 := by
  let E := stabilizer F v ⊓ stabilizer F w
  let L := sylowGenerated (stabilizer F v)
  let S := E.pCoreIn 2
  let N := H.pCoreIn 2
  have hSL : S ≤ L := pGroup_le_sylowGenerated _ _
    ((pCoreIn_le 2 E).trans inf_le_left) (isPGroup_pCoreIn 2 E)
  have hNL : N ≤ L := pGroup_le_sylowGenerated _ _
    ((pCoreIn_le 2 H).trans (hHE.trans inf_le_left)) (isPGroup_pCoreIn 2 H)
  have hgen : H.subgroupOf L ⊔ S.subgroupOf L =
      (Matrix.SpecialLinearGroup.rankOneBorel K).comap q := by
    have he : E.subgroupOf L = (stabilizer F w).subgroupOf L := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨sylowGenerated_le _ x.property,hx⟩⟩
    rw [restrict_product_supplement E H S L hHE (pCoreIn_le 2 E) hSL hprod, he]
    exact hmark
  have hn : H.subgroupOf L ≤ normalizer (N.subgroupOf L : Set L) := by
    apply le_normalizer_iff.mpr
    intro g hg a ha
    exact (mem_normalizer_iff.mp
      ((H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) hg)
        (a : G)).mp ha
  have hker : N.subgroupOf L ≤ q.ker := by
    by_contra hne
    have him := Matrix.SpecialLinearGroup.normal_two_image_of_borel_supplement q hq
      (H.subgroupOf L) (S.subgroupOf L) (N.subgroupOf L) hgen
      (isPGroup_pCoreIn 2 E).comap_subtype (isPGroup_pCoreIn 2 H).comap_subtype
      (comap_mono (pCoreIn_le 2 H)) hn hne
    apply hnot
    intro x y hx hy
    have hstab : MulAction.stabilizer L w = (Matrix.SpecialLinearGroup.rankOneBorel K).comap q := hmark
    have horbit (z : (graph F).neighborSet v) : ∃ g : L, g • w = z.val := by
      obtain ⟨g,hg,he⟩ := htrans z
      exact ⟨⟨g,hg⟩,he⟩
    obtain ⟨g,hg,he⟩ := Matrix.SpecialLinearGroup.moves_of_root_image q
      (N.subgroupOf L) him.ge w x.val y.val hstab hx hy (horbit x) (horbit y)
    exact ⟨g.val, pCoreIn_le 2 H hg, he⟩
  intro a ha x hx
  rcases (mem_ball_one F v x).mp hx with hx | rfl
  · obtain ⟨g,hg,hgx⟩ := htrans ⟨x,hx⟩
    let a' : L := ⟨a,hNL ha⟩
    let g' : L := ⟨g,hg⟩
    have hqa : q a' = 1 := hker ha
    have hf : (g'⁻¹ * a' * g' : L) ∈ (stabilizer F w).subgroupOf L := by
      rw [hmark]
      change q (g'⁻¹ * a' * g') ∈ Matrix.SpecialLinearGroup.rankOneBorel K
      simp only [map_mul, map_inv, hqa, mul_one, inv_mul_cancel]
      exact (Matrix.SpecialLinearGroup.rankOneBorel K).one_mem
    have hf' : (g⁻¹ * a * g) • w = w := hf
    have he := congrArg (fun z : Vertex F => g • z) hf'
    simpa only [mul_smul, smul_inv_smul, hgx] using he
  · exact (hHE (pCoreIn_le 2 H ha)).1
end Theory.GroupTheory.AmalgamGraph
