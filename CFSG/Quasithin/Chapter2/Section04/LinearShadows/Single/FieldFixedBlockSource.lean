module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionCoreSource
public import Theory.GroupAction.ElementaryFixedQuotient
public import Theory.GroupTheory.PCoreSurjective
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The original fixed block quotient and two-core

The square-root fixed-core count kills the elementary lifting obstruction,
so the original fixed block maps onto the fixed PSL₂ quotient. Its kernel
is exactly the original fixed two-core. The smaller PSL₂ has trivial
two-core, including PSL₂(2), so this kernel is O₂ of the fixed block.
All fixed subgroups and quotient maps use the original ambient embeddings.

The final theorem identifies this two-core with the fixed source module,
discharging the core equality in original 2.4.23(3) independently of the
subsequent fixed-module recognition.
Source: Aschbacher–Smith, 2.4.12(2), 2.4.23(1,3), pp.532 and537.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_field_fixed_block_quotient
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let Ls := (d.block.map d.H.subtype) ⊓ centralizer ({s} : Set G)
    ∃ m : ℕ, 0 < m ∧ n = 2*m ∧
      pCore 2 Ls = (twoCore d.H).subgroupOf Ls ∧
      Nonempty ((Ls ⧸ pCore 2 Ls) ≃* Theory.PSL2.BinaryGroup m) := by
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let L := d.block.map d.H.subtype
  let f : ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G) : Subgroup G) := ⟨s,hs⟩
  let fH : d.H := inclusion (inf_le_left.trans (map_subtype_le _)) f
  let a := MulAut.conjNormal (H := d.block) fH
  let eL : d.block ≃* L := equivMapOfInjective d.block d.H.subtype d.H.subtype_injective
  let b := MulAut.congr eL a
  let eK : (d.block ⧸ pCore 2 d.block) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ eL (pCore_map_iso 2 eL)
  have hs1 : s^2=1 := by simpa only [hs2] using pow_orderOf_eq_one s
  have ha : a^2=1 := by
    change MulAut.conjNormal fH ^ 2 = 1
    rw [←map_pow]
    have hfH : fH^2=1 := Subtype.ext hs1
    rw [hfH,map_one]
  have hb : b^2=1 := by dsimp only [b]; rw [←map_pow,ha,map_one]
  have hquot : quotientAut (pCore 2 L) b =
      MulAut.congr eK (normalQuotientAction d.block (pCore 2 d.block) fH) := by
    apply MulEquiv.ext
    intro z
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
    obtain ⟨k,rfl⟩ := eL.surjective l
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (pCore 2 L) (eL (a (eL.symm (eL k)))) =
      eK (normalQuotientAction d.block (pCore 2 d.block) fH
        (eK.symm (eK (QuotientGroup.mk' (pCore 2 d.block) k))))
    rw [eL.symm_apply_apply,eK.symm_apply_apply,normalQuotientAction_apply_mk]
    rfl
  have ho : ¬ ∃ g, quotientAut (pCore 2 L) b = MulAut.conj g := by
    rw [hquot,MulAut.congr_inner_iff]
    intro ⟨g,hg⟩
    exact source_field_actor_not_inner d hG T hST hsingle hL hM hTM hunique c f
      (fun hf => by have he : s=1 := congrArg Subtype.val hf; simp [he] at hs2)
      (hg ▸ ⟨g,rfl⟩)
  have hK := hL.of_mulEquiv eL
  have hc : Nat.card (((MulAut.characteristic (pCore 2 L) b).toMonoidHom).eqLocus
      (MonoidHom.id (pCore 2 L))) ^ 2 = Nat.card (pCore 2 L) := by
    obtain ⟨_,D,_,_,_,x,_,_,_,hZ⟩ := source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
    rcases hZ with hz | ⟨hz,_,_⟩
    · exact hK.centerless_core_fixed_card (source_block_core_eq_module d hG T hST hsingle) hz b hb ho
    · exact hK.full_cover_core_fixed_card (source_block_core_eq_module d hG T hST hsingle) hz b hb ho
  let Ls := L ⊓ centralizer ({s} : Set G)
  have hbval (l : L) : (b l:G)=s*(l:G)*s⁻¹ := by
    obtain ⟨k,rfl⟩ := eL.surjective l
    change (eL (a (eL.symm (eL k))):G)=_
    rw [eL.symm_apply_apply]
    rfl
  let ef : b.fixedSubgroup ≃* Ls := {
    toFun x := ⟨x.val.val,x.val.property,mem_centralizer_singleton_iff.mpr (by
      have hx := congrArg (fun y : L => (y:G)) ((MulAut.mem_fixedSubgroup b x.val).mp x.property)
      rw [hbval] at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm)⟩
    invFun x := ⟨⟨x.val,x.property.1⟩,(MulAut.mem_fixedSubgroup b _).mpr (by
      apply Subtype.ext
      rw [hbval]
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp x.property.2).symm)⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hco : pCore 2 L = ChapterC.blockU L := source_block_core_eq_module d hG T hST hsingle
  let : IsElementaryAbelian 2 (pCore 2 L) := hco ▸ hK.2.1.elementary
  have hc' : Nat.card (MulAut.characteristic (pCore 2 L) b).fixedSubgroup ^ 2 = Nat.card (pCore 2 L) := by
    have he : (MulAut.characteristic (pCore 2 L) b).fixedSubgroup =
        (MulAut.characteristic (pCore 2 L) b).toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext x
      rw [MulAut.mem_fixedSubgroup]
      rfl
    rwa [he]
  have hf2 : orderOf f=2 :=
    (orderOf_injective (((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))).subtype
      Subtype.val_injective f).symm.trans hs2
  obtain ⟨m,hm,hn,⟨eq⟩⟩ := source_field_involution_quotient_fixed_model
    d hG T hST hsingle hL hM hTM hunique c f hf2
  let eb : (quotientAut (pCore 2 L) b).fixedSubgroup ≃* Theory.PSL2.BinaryGroup m :=
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hquot)).trans
      ((MulAut.fixedSubgroupCongr eK _).symm.trans eq)
  let π : Ls →* Theory.PSL2.BinaryGroup m := eb.toMonoidHom.comp
    ((MulAut.fixedQuotientProjection (pCore 2 L) b).comp ef.symm.toMonoidHom)
  have hπ : Function.Surjective π := eb.surjective.comp
    ((MulAut.fixedQuotientProjection_surjective (pCore 2 L) b hb hc').comp ef.symm.surjective)
  have hcore : (pCore 2 L).map L.subtype = twoCore d.H :=
    (source_core_absorption d hG T hST hsingle hL hM hTM hunique).2
  have hker : π.ker=(twoCore d.H).subgroupOf Ls := by
    ext x
    change eb (MulAut.fixedQuotientProjection (pCore 2 L) b (ef.symm x))=1 ↔ _
    rw [eb.map_eq_one_iff, ← MonoidHom.mem_ker, MulAut.fixedQuotientProjection_kernel]
    change (⟨x.val,x.property.1⟩ : L) ∈ pCore 2 L ↔ x.val ∈ twoCore d.H
    rw [←hcore]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hp : IsPGroup 2 π.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 d.H).comap_of_injective Ls.subtype Ls.subtype_injective
  have he := π.comap_pCore_of_ker_isPGroup hπ hp
  rw [Atlas.RankOneFieldAutomorphisms.psl_twoCore_eq_bot] at he
  change π.ker = pCore 2 Ls at he
  change ∃ m : ℕ, 0<m ∧ n=2*m ∧ pCore 2 Ls=(twoCore d.H).subgroupOf Ls ∧ _
  refine ⟨m,hm,hn,he.symm.trans hker,⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq he.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective π hπ)

/-- Original 2.4.23(3): the fixed source module is the ambient two-core
of the actual fixed block. -/
theorem source_field_fixed_block_core
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    twoCore ((d.block.map d.H.subtype) ⊓ centralizer ({s} : Set G)) =
      ChapterC.Section05.ConjugateSource.sourceModule (d.block.map d.H.subtype) ⊓
        centralizer ({s} : Set G) := by
  let L := d.block.map d.H.subtype
  let Ls := L ⊓ centralizer ({s}:Set G)
  obtain ⟨m,hm,hn,hcore,_⟩ := source_field_fixed_block_quotient
    d hG T hST hsingle hL hM hTM hunique c s hs hs2
  have hQL : twoCore d.H ≤ L := by
    rw [←(source_core_absorption d hG T hST hsingle hL hM hTM hunique).2]
    exact map_subtype_le _
  change (pCore 2 Ls).map Ls.subtype = _
  rw [hcore,subgroupOf_map_subtype]
  rw [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2]
  change twoCore d.H ⊓ (L ⊓ centralizer ({s}:Set G)) = _
  rw [←inf_assoc,inf_eq_left.mpr hQL]

end CFSG.Quasithin.Chapter2.LinearShadows.Single
