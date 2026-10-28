module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.NormalizerTransfer
public import Theory.GroupTheory.PCorePreimageCentralizer
/-!
# Escaping local overgroups through the literal component quotient

Pull back a characteristic-two model normalizer through its actual 2-core
quotient. Local C-components descend at full Sylow subgroups through the
2-group kernel. The original stabilizer normalizes the pullback because
its ambient defining subgroup is the join of the block layer and the
characteristic 2-core of the containing component.

Source: Aschbacher–Smith 2.4.25, printed p.543. All model obstruction
premises are discharged by the connected family producers.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
/-- An intrinsic subgroup whose ambient image is preserved by the actual actor
supplies a literal normalized escaping overgroup. -/
theorem MinimalBlockSetup.alternating_no_component_subgroup_obstruction
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
    (W : Subgroup K)
    (hAW : (d.block.map d.H.subtype).subgroupOf K ≤ normalizer (W : Set K))
    (hRW : R ≤ normalizer (W.map K.subtype : Set G))
    (hN : normalizer (W : Set K) ∈ Chapter1.He K)
    (hbad : ∀ Q : Sylow 2 (normalizer (W : Set K)),
      ((d.block.map d.H.subtype).subgroupOf K).subgroupOf (normalizer (W : Set K)) ∉
        ChapterA.Section03.localCComponents Q) : False := by
  let L := d.block.map d.H.subtype
  let A := L.subgroupOf K
  let U := W.map K.subtype
  let N₀ := normalizer (W : Set K)
  let N := N₀.map K.subtype
  have hUK : U ≤ K := map_subtype_le _
  have hU : W = U.subgroupOf K := by
    exact (comap_map_eq_self_of_injective K.subtype_injective W).symm
  have hAN : A ≤ N₀ := hAW
  have hLN : L ≤ N := by
    intro l hl
    exact ⟨⟨l,hLK hl⟩,hAN hl,rfl⟩
  have hNN : N = K ⊓ normalizer (U : Set G) := by
    change (normalizer (W : Set K)).map K.subtype = _
    rw [hU,←subgroupOf_normalizer_eq hUK]
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩; exact ⟨k.property,hk⟩
    · intro hx; exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  have hRN : R ≤ normalizer (N : Set G) := by
    rw [hNN]
    exact (le_inf hRK (hRW.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let e : N₀ ≃* N := N₀.equivMapOfInjective K.subtype K.subtype_injective
  have hNe : N ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp (Chapter1.mem_He_iff.mp hN))
  apply d.alternating_no_normalized_local_obstruction hG T hTM hu hRS hi hR hL hNe hLN hRN
  intro Q hlocal
  have hes : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  let : Group.IsSolvable e.symm.toMonoidHom.ker := by
    rw [e.symm.toMonoidHom.ker_eq_bot e.symm.injective]; infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal e.symm.toMonoidHom
  have he : (L.subgroupOf N).map e.symm.toMonoidHom = A.subgroupOf N₀ := by
    ext a
    constructor
    · rintro ⟨n,hn,rfl⟩
      have hn' := congrArg (fun n : N => n.val) (e.apply_symm_apply n)
      change (e.symm n).val.val ∈ L
      exact hn' ▸ hn
    · intro ha
      exact ⟨e a,ha,e.symm_apply_apply a⟩
  apply hbad (Q.mapSurjective hes)
  change A.subgroupOf N₀ ∈ ChapterA.Section03.localCComponents
    (Q.mapSurjective hes : Subgroup N₀)
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
variable {E D : Type*} [Group E] [Group D] [Finite E] [Finite D]

/-- Pull back the actual full-Sylow obstruction through its 2-group kernel. -/
theorem quotient_normalizer_obstruction (q : E →* D) (hq : Function.Surjective q)
    (hk : IsPGroup 2 q.ker) (A U : Subgroup E)
    (hAU : A ≤ normalizer (U : Set E))
    (hN : normalizer (U.map q : Set D) ∈ Chapter1.He D)
    (hbad : ∀ Q : Sylow 2 (normalizer (U.map q : Set D)),
      (A.map q).subgroupOf (normalizer (U.map q : Set D)) ∉
        ChapterA.Section03.localCComponents Q) :
    let N := (normalizer (U.map q : Set D)).comap q
    N ∈ Chapter1.He E ∧ A ≤ N ∧ ∀ Q : Sylow 2 N,
      A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  let V := U.map q
  let N' := normalizer (V : Set D)
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
    exact (U.le_normalizer_map q) (mem_map_of_mem q (hAU ha))
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
  change (A.map q).subgroupOf N' ∈ ChapterA.Section03.localCComponents
    (Q.mapSurjective hf : Subgroup N')
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2.AlternatingTerminal

namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- Lift a model normalizer obstruction through the literal component
2-core quotient, preserving the original stabilizer action. -/
theorem MinimalBlockSetup.alternating_no_component_quotient_normalizer_obstruction
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
    let U := (ChapterC.blockU A).map A.subtype
    let q := QuotientGroup.mk' (pCore 2 K)
    let N := normalizer (U.map q : Set (K ⧸ pCore 2 K))
    N ∈ Chapter1.He (K ⧸ pCore 2 K) →
    (∀ Q : Sylow 2 N, (A.map q).subgroupOf N ∉ ChapterA.Section03.localCComponents Q) →
    False := by
  intro A U q N hN hbad
  let W := pCore 2 K ⊔ U
  have hAU : A ≤ normalizer (U : Set K) := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  have hker : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 K)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨hN₀,hAN₀,hbad₀⟩ := AlternatingTerminal.quotient_normalizer_obstruction
    q (QuotientGroup.mk'_surjective _) hker A U hAU hN hbad
  have he : N.comap q = normalizer (W : Set K) := by
    change (normalizer (U.map q : Set (K ⧸ pCore 2 K))).comap q = _
    rw [comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
    change normalizer ((U.map (QuotientGroup.mk' (pCore 2 K))).comap
      (QuotientGroup.mk' (pCore 2 K)) : Set K) = _
    rw [QuotientGroup.comap_map_mk']
  have hUa : U.map K.subtype =
      (ChapterC.blockU (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype := by
    rw [←ChapterC.RankOne.Solvable.blockU_map_equiv (subgroupOfEquivOfLe hLK),map_map,map_map]
    rfl
  have hRW : R ≤ normalizer (W.map K.subtype : Set G) := by
    change R ≤ normalizer ((pCore 2 K ⊔ U).map K.subtype : Set G)
    rw [Subgroup.map_sup,hUa]
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup]
    rw [mem_normalizer_iff_map_conj_eq.mp
      (hRK.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)) hr),
      mem_normalizer_iff_map_conj_eq.mp
      (hRL.trans (normalizer_le_normalizer_characteristic_image
        (d.block.map d.H.subtype) (ChapterC.blockU (d.block.map d.H.subtype))) hr)]
  apply d.alternating_no_component_subgroup_obstruction hG T hTM hu hRS hi hR hL hLK hRK
    W (he ▸ hAN₀) hRW (he ▸ hN₀)
  exact he ▸ hbad₀
end CFSG.Quasithin.Chapter2
