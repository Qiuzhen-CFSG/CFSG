module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.NormalizedObstruction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# The literal component-normalizer transport

Ambient isomorphisms preserve the normalizer of the original block layer
and its full-Sylow local obstruction. Inside the original group the image
of that intrinsic normalizer is K ∩ N_G(U). Hence an actor normalizing K
and the original block normalizes this actual overgroup. No actor lift
or independent Sylow enlargement is assumed.

Source: Aschbacher–Smith 2.4.25, printed p.543. The model-specific inputs
are discharged by the connected model-row consumers.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.AlternatingTerminal
variable {G D : Type*} [Group G] [Group D] [Finite G] [Finite D]

omit [Finite G] [Finite D] in
private theorem blockU_image (A : Subgroup G) (f : G →* D) (hf : Function.Injective f) :
    (ChapterC.blockU (A.map f)).map (A.map f).subtype =
      ((ChapterC.blockU A).map A.subtype).map f := by
  let e := A.equivMapOfInjective f hf
  rw [← ChapterC.RankOne.Solvable.blockU_map_equiv e,map_map,map_map]
  rfl

omit [Finite D] in
/-- The normalizer and all full-Sylow local conditions transport through
the same ambient isomorphism and the same block layer. -/
theorem normalizer_obstruction_of_equiv (e : G ≃* D) (A : Subgroup G)
    (hN : normalizer (((ChapterC.blockU (A.map e.toMonoidHom)).map
      (A.map e.toMonoidHom).subtype) : Set D) ∈ Chapter1.He D)
    (hbad : ∀ Q : Sylow 2 (normalizer (((ChapterC.blockU (A.map e.toMonoidHom)).map
      (A.map e.toMonoidHom).subtype) : Set D)),
      (A.map e.toMonoidHom).subgroupOf (normalizer (((ChapterC.blockU (A.map e.toMonoidHom)).map
        (A.map e.toMonoidHom).subtype) : Set D)) ∉ ChapterA.Section03.localCComponents Q) :
    let N := normalizer ((ChapterC.blockU A).map A.subtype : Set G)
    N ∈ Chapter1.He G ∧ ∀ Q : Sylow 2 N,
      A.subgroupOf N ∉ ChapterA.Section03.localCComponents Q := by
  let U := (ChapterC.blockU A).map A.subtype
  let N := normalizer (U : Set G)
  let B := A.map e.toMonoidHom
  let N' := normalizer ((ChapterC.blockU B).map B.subtype : Set D)
  have hAN : A ≤ N := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  have hNN : N.map e.toMonoidHom = N' := by
    change (normalizer (U : Set G)).map e.toMonoidHom =
      normalizer ((ChapterC.blockU (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype : Set D)
    rw [blockU_image _ _ e.injective,map_equiv_normalizer_eq]
  let f := (N.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hNN)
  refine ⟨Chapter1.mem_He_iff.mpr ((Theory.Quasithin.centralizer_pCore_le_iff 2 f).mpr
    (Chapter1.mem_He_iff.mp hN)),?_⟩
  intro Q hlocal
  have hf : Function.Surjective f.toMonoidHom := f.surjective
  let : Group.IsSolvable f.toMonoidHom.ker := by rw [f.toMonoidHom.ker_eq_bot f.injective]; infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal f.toMonoidHom
  have he : (A.subgroupOf N).map f.toMonoidHom = B.subgroupOf N' := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map_of_mem e.toMonoidHom ha
    · intro hb
      rcases hb with ⟨a,ha,he⟩
      exact ⟨⟨a,hAN ha⟩,ha,Subtype.ext he⟩
  apply hbad (Q.mapSurjective hf)
  change B.subgroupOf N' ∈ ChapterA.Section03.localCComponents
    (Q.mapSurjective hf : Subgroup N')
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2.AlternatingTerminal

namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The actual actor only needs to normalize the containing component and
original block; the canonical normalizer inherits both actions. -/
theorem MinimalBlockSetup.alternating_no_component_normalizer_obstruction
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
    (hRL : R ≤ normalizer (d.block.map d.H.subtype : Set G))
    (hN : normalizer ((ChapterC.blockU ((d.block.map d.H.subtype).subgroupOf K)).map
      ((d.block.map d.H.subtype).subgroupOf K).subtype : Set K) ∈ Chapter1.He K)
    (hbad : ∀ Q : Sylow 2 (normalizer ((ChapterC.blockU
      ((d.block.map d.H.subtype).subgroupOf K)).map
      ((d.block.map d.H.subtype).subgroupOf K).subtype : Set K)),
      ((d.block.map d.H.subtype).subgroupOf K).subgroupOf (normalizer ((ChapterC.blockU
        ((d.block.map d.H.subtype).subgroupOf K)).map
        ((d.block.map d.H.subtype).subgroupOf K).subtype : Set K)) ∉
        ChapterA.Section03.localCComponents Q) : False := by
  let L := d.block.map d.H.subtype
  let A := L.subgroupOf K
  let U := (ChapterC.blockU L).map L.subtype
  let U₀ := (ChapterC.blockU A).map A.subtype
  let N₀ := normalizer (U₀ : Set K)
  let N := N₀.map K.subtype
  have hUK : U ≤ K := (map_subtype_le _).trans hLK
  have hU : U₀ = U.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le hUK]
    change ((ChapterC.blockU (L.subgroupOf K)).map (L.subgroupOf K).subtype).map K.subtype =
      (ChapterC.blockU L).map L.subtype
    rw [←ChapterC.RankOne.Solvable.blockU_map_equiv
      (subgroupOfEquivOfLe (show L ≤ K from hLK)),map_map,map_map]
    rfl
  have hAN : A ≤ N₀ := A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (ChapterC.blockU A))
  have hLN : L ≤ N := by
    intro l hl
    exact ⟨⟨l,hLK hl⟩,hAN hl,rfl⟩
  have hNN : N = K ⊓ normalizer (U : Set G) := by
    change (normalizer (U₀ : Set K)).map K.subtype = _
    rw [hU,←subgroupOf_normalizer_eq hUK]
    ext x
    constructor
    · rintro ⟨k,hk,rfl⟩; exact ⟨k.property,hk⟩
    · intro hx; exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  have hRN : R ≤ normalizer (N : Set G) := by
    rw [hNN]
    exact (le_inf hRK ((hRL.trans (normalizer_le_normalizer_characteristic_image
      L (ChapterC.blockU L))).trans (normalizer (U : Set G)).le_normalizer)).trans
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
