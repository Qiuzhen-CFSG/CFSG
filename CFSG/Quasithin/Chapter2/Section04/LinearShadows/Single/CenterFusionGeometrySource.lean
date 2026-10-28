module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModuleFusionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedGeometrySource
public import Stellmacher.ElementaryAbelianMaxGlobal
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Elementary geometry for the central involution fusion argument

The original natural module has maximum elementary order in the ambient
group, and every elementary subgroup of that order is its conjugate.
In the centerless branch, each involution of the original R lies in a
whole conjugate of the distinguished Z contained in R. This uses the
literal natural-module action of L and the original elementary pair.

Source: Aschbacher–Smith, 2.4.21, printed p.536.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_module_maximum_elementary
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    sourceModule (d.block.map d.H.subtype) ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G) := by
  let U := sourceModule (d.block.map d.H.subtype)
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hf := ((source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS).2.2
  have hU : U ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    rw [hf]
    exact Set.mem_insert _ _
  refine ⟨le_top,hU.2.1,?_⟩
  intro E _ hE
  obtain ⟨P,hEP⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P T
  have hET : E.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
    rw [←hg]
    exact map_mono hEP
  have hc := hU.2.2 _ hET (hE.map (MulAut.conj g).toMonoidHom)
  rwa [card_map_of_injective (MulAut.conj g).injective] at hc

/-- Every elementary group of the original module's order is a conjugate
of that same module. -/
theorem source_maximum_elementary_conjugate
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E)
    (hc : Nat.card E = Nat.card (sourceModule (d.block.map d.H.subtype))) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom = sourceModule (d.block.map d.H.subtype) := by
  let U := sourceModule (d.block.map d.H.subtype)
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hf := ((source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS).2.2
  have hU := source_module_maximum_elementary d hG T hST hsingle hL hM hTM hunique
  obtain ⟨P,hEP⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P T
  have hET : E.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) := by
    rw [←hg]
    exact map_mono hEP
  have hEg : E.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    refine ⟨hET,hE.map _,?_⟩
    intro W _ hW
    rw [card_map_of_injective (MulAut.conj g).injective,hc]
    exact hU.2.2 W le_top hW
  rw [hf,Set.mem_insert_iff,Set.mem_singleton_iff] at hEg
  rcases hEg with he | he
  · exact ⟨g,he⟩
  · refine ⟨x*g,?_⟩
    change E.conjBy (x*g)=_
    rw [conjBy_mul]
    change (E.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom = _
    rw [he,map_map]
    have hid : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id G := by
      ext a
      simp only [MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
      group
    rw [hid,map_id]

/-- Every involution of R belongs to a whole conjugate of the original Z inside R. -/
theorem source_centerless_involution_conjugate_cover
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    ∀ r ∈ R, r^2=1 → r≠1 → ∃ g : G,
      (distinguishedZ d).map (MulAut.conj g).toMonoidHom ≤ R ∧
      r ∈ (distinguishedZ d).map (MulAut.conj g).toMonoidHom := by
  let L := d.block.map d.H.subtype
  let U := sourceModule L
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Z := distinguishedZ d
  obtain ⟨x,hxT,hxS⟩ := SetLike.exists_of_lt hST
  have hf := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
  have hUR : U ≤ R := le_sup_left.trans_eq hf.1.symm
  have hUxR : U.map (MulAut.conj x⁻¹).toMonoidHom ≤ R := le_sup_right.trans_eq hf.1.symm
  have hZU : Z ≤ U := by
    rw [show Z=distinguishedZ d from rfl,distinguishedZ_of_centerless d hz]
    exact (source_absorbed_center_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).ge.trans inf_le_left
  have hLN : L ≤ normalizer (U : Set G) :=
    L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (ChapterC.blockU L))
  change ∀ r ∈ R, r^2=1 → r≠1 → ∃ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ R ∧ r ∈ Z.map (MulAut.conj g).toMonoidHom
  intro r hr hr2 hr1
  obtain ⟨z,hzZ,hz1,_⟩ := source_involution_fused_into_distinguished_of_centerless d hG T hST hsingle hL hM hTM hunique hz r hr hr2 hr1
  have hcov (u : G) (hu : u∈U) (hu1 : u≠1) :
      ∃ l : G, Z.map (MulAut.conj l).toMonoidHom ≤ U ∧ u∈Z.map (MulAut.conj l).toMonoidHom := by
    obtain ⟨l,hl,he⟩ := source_centerless_module_transitive d hL hz z (hZU hzZ) hz1 u hu hu1
    refine ⟨l,?_,⟨z,hzZ,he⟩⟩
    exact (map_mono hZU).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hLN hl))
  rcases (source_elementary_subgroup_pair d hG T hST hsingle hL hM hTM hunique x hxT hxS).1 r hr hr2 with hu | hu
  · obtain ⟨l,hle,hlr⟩ := hcov r hu hr1
    exact ⟨l,hle.trans hUR,hlr⟩
  · obtain ⟨u,hu,he⟩ := hu
    have hu1 : u≠1 := by
      intro h
      apply hr1
      rw [←he,h,map_one]
    obtain ⟨l,hle,hlu⟩ := hcov u hu hu1
    refine ⟨x⁻¹*l,?_,?_⟩
    · change Z.conjBy (x⁻¹*l) ≤ _
      rw [conjBy_mul]
      exact (map_mono hle).trans hUxR
    · change r ∈ Z.conjBy (x⁻¹*l)
      rw [conjBy_mul]
      change r∈(Z.map (MulAut.conj l).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom
      rw [←he]
      exact mem_map_of_mem _ hlu
end CFSG.Quasithin.Chapter2.LinearShadows.Single
