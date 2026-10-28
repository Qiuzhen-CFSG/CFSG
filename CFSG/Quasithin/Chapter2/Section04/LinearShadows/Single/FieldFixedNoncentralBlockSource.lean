module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldFixedBlockSource
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.FixedOrthogonalBlock
public import Theory.GroupTheory.CentralizerResidualProducts
/-!
# The original noncentral field-fixed block

The coherent orthogonal coordinates recognize the literal group L∩C_G(s)
as a rank-one block at half the original degree. Its center is precisely
the original block center intersected with this fixed subgroup.
Source: Aschbacher--Smith, 2.4.12(2), 2.4.23(1), printed pp.532,537.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_fixed_noncentral_block
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) (hz : center (d.block.map d.H.subtype) ≠ ⊥) (hn : 4≤n) :
    let L := d.block.map d.H.subtype
    let Ls := L ⊓ centralizer ({s}:Set G)
    ChapterC.IsL2EvenBlock Ls (n/2) ∧
      center Ls = ((center L).map L.subtype).subgroupOf Ls ∧ center Ls ≠ ⊥ := by
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
  have hzcard : Nat.card (center L)=2^n := by
    obtain ⟨_,D,_,_,_,x,_,_,_,hZ⟩ := source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
    exact hZ.resolve_left hz |>.1
  obtain ⟨coords⟩ := hK.fixed_orthogonal_coordinates hco hzcard b hb ho
  let : IsElementaryAbelian 2 (pCore 2 L) := hco ▸ hK.2.1.elementary
  let j : (pCore 2 L).subgroupOf b.fixedSubgroup →* pCore 2 L := {
    toFun u := ⟨u.val.val,u.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf b.fixedSubgroup) :=
    IsElementaryAbelian.of_injective j (by
      intro u v h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w:pCore 2 L => w.val) h)
  obtain ⟨m,hm,hnm,hblock,hcore,hcenter,hne⟩ := coords.fixed_block hQ hn
  have hmhalf : m=n/2 := by omega
  have hcen : center Ls = ((center L).map L.subtype).subgroupOf Ls := by
    ext z
    have hziff : z∈center Ls ↔ ef.symm z∈center b.fixedSubgroup :=
      (MulEquivClass.apply_mem_center_iff ef.symm).symm
    rw [hziff,hcenter]
    change (⟨z.val,z.property.1⟩:L)∈center L ↔ z.val∈(center L).map L.subtype
    exact (mem_map_iff_mem L.subtype_injective).symm
  refine ⟨hmhalf ▸ hblock.of_mulEquiv ef,hcen,?_⟩
  intro hz0
  apply hne
  have hh := Theory.GroupTheory.map_center_equiv ef
  rw [hz0] at hh
  exact (map_eq_bot_iff_of_injective (center b.fixedSubgroup) ef.injective).mp hh
end CFSG.Quasithin.Chapter2.LinearShadows.Single
