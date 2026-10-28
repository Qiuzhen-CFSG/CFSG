module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryOffender.NormalOddSeed
public import Theory.GroupTheory.PResidual.TwiceOddPrime
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.ElementaryAbelian.Quotient

/-!
# The residual fixed denominator over the binary field

The core commutator bound constructs the literal SL₂(2) action on
V_beta/Z_beta. A neighboring center and its conjugates generate this
quotient, and the neighboring core supplies its Sylow-fixed generating
vectors. The two-residual of SL₂(2) has odd order three. The odd normal
fixed-space theorem therefore identifies its fixed space with the global
fixed space. The image of C_V_beta(O²(L_beta)) is consequently fixed by
L_beta, giving its commutator containment in Z_beta.

This supplies the field-two input to the proper-image argument of DGS,
*Groups and Graphs* (1985), 8.5, printed p.139. Every section map and actor
is the literal one; no splitting of V_beta is assumed.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem central_section_fixed_generation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta a : Vertex (family P)} (ha : (graph (family P)).Adj beta a)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (graphLocalGroup (family P) beta) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) beta) (V (family P) beta 1)
      (Z (family P) beta) ρ) :
    GeneratedByFixedSpace ρ ((Q (family P) a).subgroupOf (graphLocalGroup (family P) beta)) := by
  let := finite_endpoints h
  let Γ := family P
  let L := graphLocalGroup Γ beta
  let M := fixedGeneratedSubrepresentation ρ ((Q Γ a).subgroupOf L)
  have hspan := CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates Γ L (sylowGenerated_le _) ha
    (fun z hz => graphLocalGroup_transitive h hB hS beta ⟨a,ha⟩ ⟨z,hz⟩)
  have hseed : Z Γ a ≤ c.invariantPreimage M := by
    intro z hz
    have hzV := Z_neighbor_le_V Γ ha hz
    apply (c.mem_invariantPreimage M z).mpr
    refine ⟨hzV,?_⟩
    apply fixedSpace_le_fixedGenerated ρ ((Q Γ a).subgroupOf L)
    intro l
    change ρ l.val (c.coordinates ⟨z,hzV⟩).toAdd = (c.coordinates ⟨z,hzV⟩).toAdd
    rw [←c.equivariant]
    apply congrArg (fun x => (c.coordinates x).toAdd)
    apply Subtype.ext
    have hc := Z_centralizes_Q Γ a (source_Z_Q_U h a).1 hz
    change (l.val : G) * z * (l.val : G)⁻¹ = z
    rw [hc (l.val : G) l.property,mul_inv_cancel_right]
  have hV : V Γ beta 1 ≤ c.invariantPreimage M :=
    hspan.le.trans (sup_le (c.kernel_le_invariantPreimage M)
      (conjugateSpanBy_le hseed (c.invariantPreimage_normalized M)))
  have htop : M = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨v,hv⟩ := c.onto (Multiplicative.ofAdd w)
    have hm := (c.mem_invariantPreimage M v).mp (hV v.property) |>.choose_spec
    change w ∈ M.toSubmodule
    simpa only [hv,toAdd_ofAdd] using hm
  exact congrArg Subrepresentation.toSubmodule htop

private theorem odd_residual_fixed_eq_global
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) (T : Sylow 2 D)
    (hg : GeneratedByFixedSpace σ T) (ho : Odd (Nat.card (pResidual 2 D))) :
    fixedSpace σ (pResidual 2 D) = fixedSpace σ ⊤ := by
  apply NormalOddSeed.fixed_eq σ ⊤ (pResidual 2 D) T ho
    (by rw [top_inf_eq,pResidual_sup_sylow_eq_top T]) (fixedSpace σ T) le_rfl
  apply top_unique
  rw [←hg]
  apply iSup_le
  rintro g _ ⟨v,hv,rfl⟩
  exact Submodule.subset_span ⟨g,v,hv,rfl⟩

/-- The binary quotient fixes its residual denominator modulo the beta center. -/
theorem source_binary_residual_fixed_commutator
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {beta a : Vertex (family P)} (ha : (graph (family P)).Adj beta a)
    (hesc : ¬ Q (family P) a ≤ Q (family P) beta)
    (hb : 2 < b (family P))
    (hcore : ⁅Q (family P) beta,V (family P) beta 1⁆ ≤ Z (family P) beta)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2)
    (e : (graphLocalGroup (family P) beta ⧸ pCore 2 (graphLocalGroup (family P) beta)) ≃* SL(2,F)) :
    let L := graphLocalGroup (family P) beta
    let E := (pResidual 2 L).map L.subtype
    ⁅V (family P) beta 1 ⊓ centralizer (E : Set G),L⁆ ≤ Z (family P) beta := by
  let := finite_endpoints h
  let Γ := family P
  let L := graphLocalGroup Γ beta
  change 2 < b Γ at hb
  let V₀ := V Γ beta 1
  let Z₀ := Z Γ beta
  let E := (pResidual 2 L).map L.subtype
  let C := V₀ ⊓ centralizer (E : Set G)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let hSyl := source_kernel_sylow h hB hS
  let hZ := fun v => (source_Z_Q_U h v).1
  let := V_elementary Γ h.generate hZ hSyl beta (r := 1) (by simpa using hb)
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hVL : V₀ ≤ L := (V_le_Q Γ h.generate hZ hSyl beta (by omega)).trans (core_le_graphLocalGroup h beta)
  have hZV : Z₀ ≤ V₀ := Z_le_V Γ beta 1
  have hNV : L ≤ normalizer (V₀ : Set G) :=
    (sylowGenerated_le _).trans (stabilizer_normalizes_V Γ beta 1)
  have hNZ : L ≤ normalizer (Z₀ : Set G) :=
    (sylowGenerated_le _).trans (stabilizer_normalizes_Z Γ beta)
  let : (Z₀.subgroupOf V₀).Normal := normal_subgroupOf_of_le_normalizer (hVL.trans hNZ)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨σ,c,hc⟩ := BinaryConjugationSection.exists_descended_actor L V₀ Z₀ hVL hZV hNV hNZ q hq (by
    intro l hl v hv
    have hlQ : (l : G) ∈ Q Γ beta := (graphLocalGroup_core h beta) ▸
      mem_map_of_mem L.subtype (show l ∈ pCore 2 L from hk ▸ hl)
    exact hcore (commutator_mem_commutator hlQ hv))
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS ha hesc e
  have hg : GeneratedByFixedSpace σ T := by
    have hg₀ := central_section_fixed_generation h hB hS ha (σ.comp q) c
    have hh := generatedByFixedSpace_of_equivariant_surjection (σ.comp q) σ q
      (LinearMap.id : Additive (V₀ ⧸ Z₀.subgroupOf V₀) →ₗ[ZMod 2] Additive (V₀ ⧸ Z₀.subgroupOf V₀))
      Function.surjective_id (fun _ _ => rfl) _ hg₀
    exact hT ▸ hh
  have ho : Odd (Nat.card (pResidual 2 SL(2,F))) := by
    have hoD : Nat.card SL(2,F) = 2*3 := by
      rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
      norm_num
    rw [card_twoResidual_of_card_twice_odd_prime (by decide : Odd 3) hoD]
    decide
  have hfixed := odd_residual_fixed_eq_global σ T hg ho
  have hmap : (pResidual 2 L).map q = pResidual 2 SL(2,F) := map_pResidual_of_surjective 2 q hq
  have hEC : ⁅E,C⁆ ≤ Z₀ := by
    rw [commutator_comm]
    exact (commutator_eq_bot_iff_le_centralizer.mpr (show C ≤ centralizer (E : Set G) from inf_le_right)).le.trans bot_le
  have hCf : c.imageSpace C ≤ fixedSpace σ (pResidual 2 SL(2,F)) := by
    intro w hw r
    obtain ⟨l,hl,he⟩ := show r.val ∈ (pResidual 2 L).map q from hmap.symm ▸ r.property
    change σ r.val w = w
    rw [←he]
    exact c.fixed_on_imageSpace_of_commutator_le E C hEC l (mem_map_of_mem L.subtype hl) w hw
  change ⁅C,L⁆ ≤ Z₀
  rw [commutator_comm]
  apply c.commutator_le_of_imageSpace_fixed L C le_rfl inf_le_left
  intro w hw l
  exact (hfixed ▸ hCf hw) ⟨q l.val,mem_top _⟩
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
