module

public import CFSG.Quasithin.ChapterC.Section06.General
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Local finiteness for C.6.3

The finite ambient proof of C.6.3 is localized to `L ⊔ R`.  If `R`
normalizes `L`, this join is finite when `L` and `R` are finite, so the
finite core and residual calculations can be performed in its subtype and
transported back to the original ambient group.
-/

open Subgroup
open Stellmacher
open BenderSuzuki.External
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC
noncomputable section
variable {G : Type*} [Group G]

private theorem finiteSup (L R : Subgroup G) [Finite L] [Finite R]
    (hRL : R ≤ normalizer (L : Set G)) : Finite (↥(L ⊔ R)) := by
  apply Finite.of_surjective (fun p : L × R =>
    (⟨(p.1 : G) * (p.2 : G), (by
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left L R hRL]
      exact ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩)⟩ : ↥(L ⊔ R)))
  intro x
  have hx : (x : G) ∈ (L : Set G) * (R : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L R hRL]
    exact x.property
  rcases hx with ⟨l, hl, r, hr, hrl⟩
  refine ⟨(⟨l, hl⟩, ⟨r, hr⟩), ?_⟩
  apply Subtype.ext
  exact hrl

private lemma norm_subgroupOf {L R : Subgroup G} (hRL : R ≤ normalizer (L : Set G)) :
    R.subgroupOf (L ⊔ R) ≤ normalizer (L.subgroupOf (L ⊔ R) : Set (↥(L ⊔ R))) := by
  rw [Subgroup.le_normalizer_iff]
  intro r hr l hl
  exact (Subgroup.le_normalizer_iff.mp hRL) r.val hr l.val hl

private lemma htop_of_hres {L : Subgroup G} [Finite L]
    (hres : twoResidualAmbient L = L) :
    twoResidualAmbient (⊤ : Subgroup L) = (⊤ : Subgroup L) := by
  have hsub : twoResidualSubgroup L = (⊤ : Subgroup L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hres
  apply top_unique
  intro x hx
  rw [twoResidualAmbient, Subgroup.mem_map]
  let f : (⊤ : Subgroup L) →* L := (⊤ : Subgroup L).subtype
  have hf : Function.Surjective f := by
    intro y
    exact ⟨⟨y, trivial⟩, rfl⟩
  have hxsub : (x : L) ∈ twoResidualSubgroup L := by
    rw [hsub]
    trivial
  have hx' : (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈
      twoResidualSubgroup (⊤ : Subgroup L) := by
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let N' : Subgroup L := N.map f
    have hNnormal : N'.Normal := hN.1.map f hf
    have hNindex : N'.index = N.index := by
      have hcomap : N'.comap f = N := by
        apply Subgroup.comap_map_eq_self
        rw [MonoidHom.ker_eq_bot f (Subgroup.subtype_injective (⊤ : Subgroup L))]
        exact bot_le
      rw [← hcomap, Subgroup.index_comap_of_surjective N' hf]
    have hNpow : ∃ n : ℕ, N'.index = 2 ^ n := by
      rcases hN.2 with ⟨n, hn⟩
      exact ⟨n, hNindex.trans hn⟩
    have hxN' : (x : L) ∈ N' := by
      apply (Subgroup.mem_sInf.mp hxsub) N'
      exact ⟨hNnormal, hNpow⟩
    rcases (Subgroup.mem_map.mp hxN') with ⟨y, hy, hfy⟩
    change (⟨x, trivial⟩ : (⊤ : Subgroup L)) ∈ N
    have heq : y = (⟨x, trivial⟩ : (⊤ : Subgroup L)) := by
      apply Subtype.ext
      exact hfy
    simpa [heq] using hy
  exact ⟨⟨x, trivial⟩, hx', rfl⟩

private lemma local_residual_eq {L R : Subgroup G} [Finite L] [Finite R]
    (hRL : R ≤ normalizer (L : Set G))
    (hres : twoResidualAmbient L = L) :
    let S : Subgroup G := L ⊔ R
    let LS : Subgroup (↥S) := L.subgroupOf S
    twoResidualAmbient LS = LS := by
  let S : Subgroup G := L ⊔ R
  let LS : Subgroup (↥S) := L.subgroupOf S
  let _ : Finite (↥S) := finiteSup L R hRL
  have htopL := htop_of_hres hres
  let e : (↥LS) ≃* (↥L) := Subgroup.subgroupOfEquivOfLe le_sup_left
  have htopLS : twoResidualAmbient (⊤ : Subgroup LS) = (⊤ : Subgroup LS) := by
    have h := map_twoResidualAmbient_of_subgroup_image
      (⊤ : Subgroup L) e.symm.toMonoidHom (⊤ : Subgroup LS)
      (Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective)
    rw [htopL, Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] at h
    exact h.symm
  have h := map_twoResidualAmbient_of_subgroup_image
      (⊤ : Subgroup LS) LS.subtype LS
      (by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
  rw [htopLS, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h.symm

private lemma transport (L R : Subgroup G) :
    let S : Subgroup G := L ⊔ R
    let LS : Subgroup (↥S) := L.subgroupOf S
    let RS : Subgroup (↥S) := R.subgroupOf S
    LS ⊔ RS = (⊤ : Subgroup (↥S)) ∧
    LS.map S.subtype = L ∧ RS.map S.subtype = R ∧
    ((pCore 2 (↥(LS ⊔ RS))).map (LS ⊔ RS).subtype).map S.subtype =
      (pCore 2 (↥S)).map S.subtype ∧
    ((pCore 2 LS).map LS.subtype).map S.subtype =
      (pCore 2 L).map L.subtype := by
  let S : Subgroup G := L ⊔ R
  let LS : Subgroup (↥S) := L.subgroupOf S
  let RS : Subgroup (↥S) := R.subgroupOf S
  have hsup : LS ⊔ RS = (⊤ : Subgroup (↥S)) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    ext x
    constructor
    · intro _
      trivial
    · intro _
      exact x.property
  have hmapL : LS.map S.subtype = L := by
    exact Subgroup.map_subgroupOf_eq_of_le le_sup_left
  have hmapR : RS.map S.subtype = R := by
    exact Subgroup.map_subgroupOf_eq_of_le le_sup_right
  have hpc :
      (pCore 2 (⊤ : Subgroup (↥S))).map (⊤ : Subgroup (↥S)).subtype = pCore 2 (↥S) := by
    have h := pCore_map_iso 2
      (Subgroup.topEquiv : (⊤ : Subgroup (↥S)) ≃* (↥S))
    exact h
  have hqmap :
      ((pCore 2 (↥(LS ⊔ RS))).map (LS ⊔ RS).subtype).map S.subtype =
        (pCore 2 (↥S)).map S.subtype := by
    rw [hsup, Subgroup.map_map, ← Subgroup.map_map, hpc]
  have hmmap :
      ((pCore 2 LS).map LS.subtype).map S.subtype =
        (pCore 2 L).map L.subtype := by
    let e : (↥LS) ≃* (↥L) := Subgroup.subgroupOfEquivOfLe le_sup_left
    have he := pCore_map_iso 2 e
    rw [Subgroup.map_map]
    have hcomp : S.subtype.comp LS.subtype = L.subtype.comp e.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, he]
  exact ⟨hsup, hmapL, hmapR, hqmap, hmmap⟩

public theorem c6_3_commutator_core_bound_local {L R : Subgroup G} [Finite L] [Finite R]
    (hRL : R ≤ normalizer (L : Set G))
    (hres : twoResidualAmbient L = L) :
    ⁅L, (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype⁆ ≤
      ⁅(pCore 2 L).map L.subtype, L⁆ ∧
    (pCore 2 L).map L.subtype ≤ (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype := by
  let S : Subgroup G := L ⊔ R
  let LS : Subgroup (↥S) := L.subgroupOf S
  let RS : Subgroup (↥S) := R.subgroupOf S
  let _ : Finite (↥S) := finiteSup L R hRL
  have hresS : twoResidualAmbient LS = LS := local_residual_eq hRL hres
  have hb := c6_3_commutator_core_bound LS RS (norm_subgroupOf hRL) hresS
  have ht := transport L R
  have hm := Subgroup.map_mono (f := S.subtype) hb.1
  have hm2 := Subgroup.map_mono (f := S.subtype) hb.2
  rw [Subgroup.map_commutator, Subgroup.map_commutator] at hm
  have hL : LS.map S.subtype = L := by simp [S, LS, ht.2.1]
  have hq :
      ((pCore 2 (↥(LS ⊔ RS))).map (LS ⊔ RS).subtype).map S.subtype =
        (pCore 2 (↥S)).map S.subtype := by
    simpa [S, LS, RS] using ht.2.2.2.1
  have hM : ((pCore 2 LS).map LS.subtype).map S.subtype =
      (pCore 2 L).map L.subtype := by
    simpa [S, LS, RS] using ht.2.2.2.2
  rw [hL, hq, hM] at hm
  rw [hM, hq] at hm2
  exact ⟨hm, hm2⟩

public theorem c6_3_exists_escaping_conjugate_local
    (L R T Λ : Subgroup G)
    [Finite L] [Finite R] [Finite T] [Finite Λ]
    (hRL : R ≤ normalizer (L : Set G))
    (hres : twoResidualAmbient L = L)
    (hQR : (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype ≤ R)
    (hU : ⁅(pCore 2 L).map L.subtype, L⁆ ≠ ⊥)
    (hRT : R ≤ T)
    (hTR : (R.subgroupOf T).Normal)
    (hno : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R →
      (W.subgroupOf (L ⊔ T)).Normal →
      ¬ Λ ⊓ normalizer (R : Set G) ≤ Λ ⊓ normalizer (W : Set G)) :
    let U := ⁅(pCore 2 L).map L.subtype, L⁆
    let Q := (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype
    ∃ x ∈ (Λ ⊓ normalizer (R : Set G)) ⊔ T,
      ¬ U.map (MulAut.conj x⁻¹) ≤ Q := by
  let M := (pCore 2 L).map L.subtype
  let U := ⁅M, L⁆
  let Q := (pCore 2 (↥(L ⊔ R))).map (L ⊔ R).subtype
  have hb := c6_3_commutator_core_bound_local hRL hres
  have hMU : L ≤ normalizer (M : Set G) := by
    have hh := (pCore 2 L).le_normalizer_map L.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      using hh
  have hUM : U ≤ M := le_normalizer_iff_commutator_le_left.mp hMU
  have hMQ : M ≤ Q := hb.2
  have hUQ : U ≤ Q := hUM.trans hMQ
  have hUR : U ≤ R := hUQ.trans hQR
  have hTR' : T ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hRT).mp hTR
  exact exists_conjugate_escape_of_commutator_le L R T Λ U Q
    hU hUR hRT hTR' hb.1 hno
end
end ChapterC
