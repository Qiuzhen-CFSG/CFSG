module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionRoots
public import Theory.GroupTheory.SpecificGroups.SymmetricFourElementaryCentralizer

/-!
# Self-centralizers of the original exceptional endpoint cores

The graph involution f is central in each Eᵢ and has order two, hence
belongs to Aᵢ = O₂(Eᵢ). The common Sylow centralizer contains both Aᵢ,
so both lie in E₁. Since the root z also lies in each Aᵢ and C_G(z)=M₁,
every element of C_G(Aᵢ) lies in E₁=M₁∩C_G(f). The supplied original
fusion facts identify E₁ with E₄×S₄. The elementary order-sixteen
calculation in that product proves C_G(Aᵢ)=Aᵢ.

All groups and maps are the literal source groups. `FusionFacts` is the
only earlier source input; its independent producer is discharged by the
exceptional-branch assembly. No model recognition or self-centralizer
conclusion is assumed.

Source: Aschbacher–Smith F.5.4(1), printed p.301.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
local notation "C2" => Multiplicative (ZMod 2)
local notation "S4" => Equiv.Perm (Fin 4)

variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G)
  (h : FusionFacts c i z t)
include h

/-- The marked graph involution belongs to each actual endpoint two-core. -/
theorem graph_mem_A (b : Bool) : Source.graphElement c i ∈ A c i b := by
  have ho : orderOf (Source.graphElement c i) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp h.graph_fuses_t
    have he := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (Source.graphElement c i)
    change orderOf (g * Source.graphElement c i * g⁻¹) = _ at he
    rw [hg,h.t_order] at he
    exact he.symm
  have hp : IsPGroup 2 (zpowers (Source.graphElement c i)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ho]; rfl)
  have hnorm : E c i b ≤ normalizer (zpowers (Source.graphElement c i) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two _ ho]
    exact inf_le_right
  exact le_pCoreIn_of_normalizes hp (zpowers_le.mpr (graph_mem_E c i b)) hnorm (mem_zpowers _)

omit [Finite G] in
/-- Both endpoint two-cores lie in the literal common Sylow centralizer. -/
theorem A_le_TfImage (b : Bool) : A c i b ≤ TfImage c i := by
  obtain ⟨S,hS⟩ := h.tf_sylow b
  rw [←hS]
  exact pCoreIn_le_sylow _ S

/-- F.5.4(1): the actual ambient centralizer of each Aᵢ is Aᵢ itself. -/
theorem A_self_centralizer (b : Bool) : centralizer (A c i b : Set G) = A c i b := by
  let := h.A_elementary b
  have hAE : A c i b ≤ E c i false :=
    (A_le_TfImage c i z t h b).trans (TfImage_le_E c i false)
  let J := (A c i b).subgroupOf (E c i false)
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.subgroupOf hAE
  obtain ⟨e⟩ := h.E_iso false
  let K := J.map e.toMonoidHom
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.map _
  have hcard : Nat.card K = 16 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hAE).toEquiv).trans (h.A_card b)
  have hcentral : centralizer (K : Set ((C2 × C2) × S4)) = K :=
    SymmetricFourElementary.centralizer_eq_of_elementary_card_sixteen K hcard
  apply le_antisymm _ (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  intro x hx
  have hxE : x ∈ E c i false := by
    constructor
    · rw [←h.root_centralizer]
      exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx _ (h.root_mem_A b)).symm
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx _ (graph_mem_A c i z t h b)).symm
  let y : E c i false := ⟨x,hxE⟩
  have hy : e y ∈ centralizer (K : Set ((C2 × C2) × S4)) := by
    rintro _ ⟨a,ha,rfl⟩
    change e a * e y = e y * e a
    rw [←map_mul,←map_mul]
    apply congrArg e
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx a.val ha
  rw [hcentral] at hy
  obtain ⟨a,ha,he⟩ := hy
  have heq : a = y := e.injective he
  change y ∈ J
  exact heq ▸ ha

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
