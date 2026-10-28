module
public import Theory.GroupTheory.SylowPreimageNormalizer
public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Radicality of Sylow preimages of action cores

Let q be an onto homomorphism and R a Sylow subgroup of the full preimage
of its p-core, mapping onto that core. Frattini lifting makes N(R) map
onto the entire target. Its p-core therefore lies in the same full
preimage, where Sylow maximality identifies it with R. In particular the
intersection of a prescribed Sylow subgroup with the preimage of the
image p-core is radical. Odd factors in the action kernel are retained.

The literal first-flag application is FirstFlagMSPair in Chapter 13:
this supplies the local subgroup required by C.1.37, pp.142--143, without
identifying the source R₁ with the two-core of L₁T.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H] {p : ℕ} [Fact p.Prime]

/-- A Sylow preimage of the image p-core is the p-core of its normalizer. -/
theorem pCoreIn_normalizer_of_sylow_preimage
    (R : Subgroup G) (hpR : IsPGroup p R) (q : G →* H)
    (hq : Function.Surjective q) (himage : R.map q = pCore p H)
    (P : Sylow p ((R.map q).comap q))
    (hP : (P : Subgroup ((R.map q).comap q)) = R.subgroupOf ((R.map q).comap q)) :
    (normalizer (R : Set G)).pCoreIn p = R := by
  let N := normalizer (R : Set G)
  let U := (R.map q).comap q
  have hN : N.map q = ⊤ := by
    rw [normalizer_map_eq_of_sylow_preimage R q hq P hP, himage, normalizer_eq_top]
  let f := q.comp N.subtype
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨x,hx,hxh⟩ := hN.symm ▸ mem_top h
    exact ⟨⟨x,hx⟩,hxh⟩
  have hc : (pCore p N).map f ≤ pCore p H :=
    le_sSup ⟨(inferInstance : (pCore p N).Normal).map f hf,pCore_isPGroup.map f⟩
  have hCU : N.pCoreIn p ≤ U := by
    rintro _ ⟨x,hx,rfl⟩
    change q x.val ∈ R.map q
    rw [himage]
    exact hc (mem_map_of_mem f hx)
  have hRC : R ≤ N.pCoreIn p := le_map_pCore_normalizer hpR
  have he : (N.pCoreIn p).subgroupOf U = (P : Subgroup U) :=
    P.is_maximal' (isPGroup_pCoreIn p N).comap_subtype (by
      rw [hP]
      exact comap_mono hRC)
  have hm := congrArg (map U.subtype) he
  rw [hP,map_subgroupOf_eq_of_le hCU,
    map_subgroupOf_eq_of_le (le_comap_map q R)] at hm
  exact hm

/-- The inverse image of the image p-core inside a prescribed Sylow is
radical in the original group. The full kernel need not be a p-group. -/
theorem sylow_inf_corePreimage_normalizer_core
    (q : G →* H) (hq : Function.Surjective q) (S : Sylow p G) :
    let R := (S : Subgroup G) ⊓ (pCore p H).comap q
    (normalizer (R : Set G)).pCoreIn p = R := by
  let U := (pCore p H).comap q
  let R := (S : Subgroup G) ⊓ U
  have him : R.map q = pCore p H := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx.2
    · intro h hh
      obtain ⟨x,hx,hxh⟩ := (pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hq)) hh
      exact ⟨x,⟨hx,show q x ∈ pCore p H from hxh.symm ▸ hh⟩,hxh⟩
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal U
  have he : (P : Subgroup U) = R.subgroupOf U := by
    rw [hP]
    ext x
    exact ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
  have hpre : (R.map q).comap q = U := congrArg (comap q) him
  let e := MulEquiv.subgroupCongr hpre.symm
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQ : (Q : Subgroup ((R.map q).comap q)) =
      R.subgroupOf ((R.map q).comap q) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change y ∈ R.subgroupOf U
      rwa [←he]
    · intro hx
      refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
      rw [he]
      exact hx
  exact pCoreIn_normalizer_of_sylow_preimage R (S.isPGroup'.to_le inf_le_left)
    q hq him Q hQ
end Subgroup
