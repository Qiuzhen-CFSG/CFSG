module
public import Theory.GroupTheory.InnerActorSylowNormalizer
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.NormalizedObstruction
/-!
# The original actor in an intrinsic inner-action escape

A model escape containing a Sylow subgroup of the original block normalizer
is preserved by the actual half-Sylow actor when the containing group is
centerless with only inner automorphisms. The selected intrinsic overgroup
then contradicts the proved original-source persistence statement. The native
model escape remains an explicit input; no full ambient Sylow bound is used.

Source: Aschbacher--Smith 2.4.25, printed p.543.
-/
public section
namespace CFSG.Quasithin.Chapter2
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.alternating_no_inner_escape
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
    (hc : center K = ⊥)
    (hin : Function.Surjective (MulAut.conj : K →* MulAut K))
    (hrow : ∀ P : Sylow 2 (normalizer ((d.block.map d.H.subtype).subgroupOf K : Set K)),
      ∃ N : Subgroup K,
        (d.block.map d.H.subtype).subgroupOf K ≤ N ∧
        (P : Subgroup (normalizer ((d.block.map d.H.subtype).subgroupOf K : Set K))).map
          (normalizer ((d.block.map d.H.subtype).subgroupOf K : Set K)).subtype ≤ N ∧
        N ∈ Chapter1.He K ∧ ∀ Q : Sylow 2 N,
          ((d.block.map d.H.subtype).subgroupOf K).subgroupOf N ∉
            ChapterA.Section03.localCComponents Q) : False := by
  let L := d.block.map d.H.subtype
  obtain ⟨P,hP⟩ := exists_inner_normalizer_sylow K L R hRK hRL
    ((d.S.isPGroup'.map d.H.subtype).to_le hRS) hc hin
  obtain ⟨N,hLN,hPN,hN,hbad⟩ := hrow P
  let NA := N.map K.subtype
  let e : N ≃* NA := N.equivMapOfInjective K.subtype K.subtype_injective
  have hLNA : L ≤ NA := by
    intro l hl
    exact ⟨⟨l,hLK hl⟩,hLN hl,rfl⟩
  have hNA : NA ∈ Chapter1.He G := Chapter1.mem_He_iff.mpr
    ((Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp (Chapter1.mem_He_iff.mp hN))
  apply d.alternating_no_normalized_local_obstruction hG T hTM hu hRS hi hR hL hNA hLNA
    (hP N hPN)
  intro Q hlocal
  let : Group.IsSolvable e.symm.toMonoidHom.ker := by
    rw [e.symm.toMonoidHom.ker_eq_bot e.symm.injective]
    infer_instance
  have hm := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal e.symm.toMonoidHom
  have he : (L.subgroupOf NA).map e.symm.toMonoidHom = (L.subgroupOf K).subgroupOf N := by
    ext a
    constructor
    · rintro ⟨n,hn,rfl⟩
      have hn' := congrArg (fun n : NA => n.val) (e.apply_symm_apply n)
      change (e.symm n).val.val ∈ L
      exact hn' ▸ hn
    · intro ha
      exact ⟨e a,ha,e.symm_apply_apply a⟩
  have hes : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
  apply hbad (Q.mapSurjective hes)
  change (L.subgroupOf K).subgroupOf N ∈ ChapterA.Section03.localCComponents
    (Q.mapSurjective hes : Subgroup N)
  rw [Sylow.coe_mapSurjective]
  exact he ▸ hm
end CFSG.Quasithin.Chapter2
