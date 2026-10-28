module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.QuotientNormalizerTransfer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
/-!
# Invariant escaping overgroups in the literal component quotient

An invariant characteristic-two overgroup of the faithful quotient block
pulls back through the component two-core. The original stabilizer acts on
that quotient and preserves the actual block layer, hence normalizes this
pullback. Full-Sylow local C-components descend through the two-group kernel,
contradicting the original persistence statement.

Source: Aschbacher–Smith 2.4.25, printed p.543.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
variable {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]
theorem quotient_overgroup_obstruction (q : E →* D) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A : Subgroup E) (N' : Subgroup D)
    (hAN' : A.map q ≤ N') (hN : N' ∈ Chapter1.He D)
    (hbad : ∀ Q : Sylow 2 N', (A.map q).subgroupOf N' ∉
        ChapterA.Section03.localCComponents Q) :
    let N := N'.comap q
    N ∈ Chapter1.He E ∧ A ≤ N ∧ ∀ Q : Sylow 2 N,
      A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  let N := N'.comap q
  let f : N →* N' :=
    { toFun := fun x => ⟨q x,x.property⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul x y) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    exact ⟨⟨x,show q x ∈ N' from hx ▸ y.property⟩,Subtype.ext hx⟩
  have hker : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.subgroupOf N := by
      ext x
      change (⟨q x,x.property⟩ : N') = 1 ↔ q x = 1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  have hAN : A ≤ N := by
    intro a ha
    exact hAN' (mem_map_of_mem q ha)
  refine ⟨Chapter1.mem_He_iff.mpr (f.centralizer_pCore_le_of_surjective_pKernel hf hker
    (Chapter1.mem_He_iff.mp hN)),hAN,?_⟩
  intro Q hlocal
  let := hker.isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f
  have he : (A.subgroupOf N).map f = (A.map q).subgroupOf N' := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map_of_mem q ha
    · rintro ⟨a,ha,he⟩
      exact ⟨⟨a,hAN ha⟩,ha,Subtype.ext he⟩
  apply hbad (Q.mapSurjective hf)
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2.AlternatingTerminal
namespace CFSG.Quasithin.Chapter2
open ChapterC
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_no_component_invariant_quotient_obstruction
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    {R K : Subgroup G}
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hi : R.relIndex ((d.S : Subgroup d.H).map d.H.subtype) = 2)
    (hR : R ∈ beta M)
    (hL : d.block.map d.H.subtype ∈ Chapter1.L G R)
    (hLK : d.block.map d.H.subtype ≤ K)
    (hRK : R ≤ normalizer (K : Set G))
    (hRL : R ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    let A := (d.block.map d.H.subtype).subgroupOf K
    let U := (blockU A).map A.subtype
    let q := QuotientGroup.mk' (pCore 2 K)
    ∀ N : Subgroup (K ⧸ pCore 2 K), N ∈ Chapter1.He (K ⧸ pCore 2 K) → A.map q ≤ N →
    (∀ a : MulAut (K ⧸ pCore 2 K), (U.map q).map a.toMonoidHom = U.map q →
      N.map a.toMonoidHom = N) →
    (∀ Q : Sylow 2 N, (A.map q).subgroupOf N ∉ ChapterA.Section03.localCComponents Q) →
    False := by
  intro A U q N hN hAN hInv hbad
  let W := N.comap q
  let V := W.map K.subtype
  have hker : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 K)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨hW,hAW,hbadW⟩ := AlternatingTerminal.quotient_overgroup_obstruction
    q (QuotientGroup.mk'_surjective _) hker A N hAN hN hbad
  have hUa : U.map K.subtype =
      (blockU (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv (subgroupOfEquivOfLe hLK),map_map,map_map]
    rfl
  have hRU : R ≤ normalizer (U.map K.subtype : Set G) := by
    rw [hUa]
    exact hRL.trans (normalizer_le_normalizer_characteristic_image _ _)
  have hRV : R ≤ normalizer (V : Set G) := by
    intro r hr
    let a := K.normalizerMonoidHom ⟨r,hRK hr⟩
    let b := quotientAut (pCore 2 K) a
    have hUa' : U.map a.toMonoidHom = U := by
      apply map_injective K.subtype_injective
      rw [map_map]
      change U.map ((MulAut.conj r).toMonoidHom.comp K.subtype) = _
      rw [←map_map]
      exact mem_normalizer_iff_map_conj_eq.mp (hRU hr)
    have hcomm : b.toMonoidHom.comp q = q.comp a.toMonoidHom := by
      ext x
      exact quotientAut_apply_mk _ _ _
    have hUb : (U.map q).map b.toMonoidHom = U.map q := by
      rw [map_map,hcomm,←map_map,hUa']
    have hNb := hInv b hUb
    have hWa : W.map a.toMonoidHom = W := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        change q (a y) ∈ N
        rw [←quotientAut_apply_mk (pCore 2 K) a y]
        exact hNb ▸ mem_map_of_mem b.toMonoidHom hy
      · intro hx
        have hh : b.symm (q x) ∈ N := by
          obtain ⟨y,hy,he⟩ := show q x ∈ N.map b.toMonoidHom from hNb.symm ▸ hx
          have he' : b y = q x := he
          rw [←he',b.symm_apply_apply]
          exact hy
        refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
        change q (a.symm x) ∈ N
        have he : q (a.symm x) = b.symm (q x) := by
          apply b.injective
          rw [b.apply_symm_apply]
          change quotientAut (pCore 2 K) a (q (a.symm x)) = q x
          rw [quotientAut_apply_mk,a.apply_symm_apply]
        exact he ▸ hh
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (W.map K.subtype).map (MulAut.conj r).toMonoidHom = W.map K.subtype
    rw [map_map]
    change W.map (K.subtype.comp a.toMonoidHom) = _
    rw [←map_map,hWa]
  have hLV : d.block.map d.H.subtype ≤ V := by
    intro l hl
    exact ⟨⟨l,hLK hl⟩,hAW hl,rfl⟩
  let e : W ≃* V := W.equivMapOfInjective K.subtype K.subtype_injective
  have hV : V ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp (Chapter1.mem_He_iff.mp hW))
  apply d.alternating_no_normalized_local_obstruction hG T hTM hu hRS hi hR hL hV hLV hRV
  intro Q hlocal
  have hes : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  let : Group.IsSolvable e.symm.toMonoidHom.ker := by
    rw [e.symm.toMonoidHom.ker_eq_bot e.symm.injective]; infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal e.symm.toMonoidHom
  have he : ((d.block.map d.H.subtype).subgroupOf V).map e.symm.toMonoidHom =
      A.subgroupOf W := by
    ext a
    constructor
    · rintro ⟨n,hn,rfl⟩
      have hn' := congrArg (fun n : V => n.val) (e.apply_symm_apply n)
      change (e.symm n).val.val ∈ d.block.map d.H.subtype
      exact hn' ▸ hn
    · intro ha
      exact ⟨e a,ha,e.symm_apply_apply a⟩
  apply hbadW (Q.mapSurjective hes)
  change A.subgroupOf W ∈ ChapterA.Section03.localCComponents
    (Q.mapSurjective hes : Subgroup W)
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2
