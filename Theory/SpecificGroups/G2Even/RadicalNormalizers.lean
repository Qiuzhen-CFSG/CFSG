module
public import Theory.SpecificGroups.SL2.RadicalSubgroups
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.SpecificGroups.SL2.TwoCore

/-!
# Exact two-radical normalizers in even G₂

The root geometry places a nontrivial two-radical normalizer inside a
conjugate root parabolic. The parabolic's normal rank-one subgroup contains
a full Sylow two-subgroup, hence contains the radical. Radicality descends
to its literal SL₂ quotient. The radical is therefore either the parabolic
core or an ambient Sylow subgroup, giving the exact normalizer alternatives.

Each alternative contains a full Sylow normalizer. Conjugacy inside a
specified overgroup then preserves the original supplied Sylow marking.
This is the normalizer input used on the original NI in 15.2.23.

Source: Aschbacher (1981), 8.2(7), used in Aschbacher--Smith C.2.7,
pp.146--147 and original 15.2.23, p.1116; refs/quasithin.pdf.
The root model and parabolic facts retain their ATLAS attribution through
the imported modules; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup
open scoped MatrixGroups Pointwise

private theorem twoGroup_le_normal_sylow_overgroup
    {G : Type*} [Group G] [Finite G]
    (R P L : Subgroup G) (hR : IsPGroup 2 R)
    (hRP : R ≤ P) (hLP : L ≤ P) (hn : P ≤ normalizer (L : Set G))
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ L) : R ≤ L := by
  let : (L.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hn
  have hSL : (T.subtype (hTL.trans hLP) : Subgroup P) ≤ L.subgroupOf P := fun x hx => hTL hx
  have hi : ¬ 2 ∣ (L.subgroupOf P).index := fun hd =>
    (T.subtype (hTL.trans hLP)).not_dvd_index (hd.trans (index_dvd_of_le hSL))
  have hp : IsPGroup 2 (R.subgroupOf P) := hR.comap_subtype
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hle : R.subgroupOf P ≤ L.subgroupOf P := by
    rw [← relIndex_eq_one]
    apply Nat.eq_one_of_dvd_coprimes
      (show (L.subgroupOf P).index.Coprime (Nat.card (R.subgroupOf P)) from by
        rw [hk]
        exact (Nat.prime_two.coprime_iff_not_dvd.mpr hi).symm.pow_right k)
      ((L.subgroupOf P).relIndex_dvd_index_of_normal (R.subgroupOf P))
      (relIndex_dvd_card _ _)
  intro x hx
  exact hle (show (⟨x,hRP hx⟩ : P) ∈ R.subgroupOf P from hx)

private theorem normalizer_le_of_common_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S Q : Sylow p G) (P : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hQP : (Q : Subgroup G) ≤ P)
    (hN : normalizer (S : Set G) ≤ P) : normalizer (Q : Set G) ≤ P := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P (S.subtype hSP) (Q.subtype hQP)
  have he : (g : G) • S = Q :=
    Sylow.subtype_injective ((S.smul_subtype hSP g).symm.trans hg)
  have hm : (S : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom = Q :=
    congrArg Sylow.toSubgroup he
  have hn : (normalizer (S : Set G)).map (MulAut.conj (g : G)).toMonoidHom =
      normalizer (Q : Set G) := by
    change (normalizer ((S : Subgroup G) : Set G)).map _ = _
    rw [map_equiv_normalizer_eq,hm]
    rfl
  rw [←hn]
  rintro x ⟨y,hy,rfl⟩
  exact P.mul_mem (P.mul_mem g.property (hN hy)) (P.inv_mem g.property)

namespace Atlas.G2
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem normalizer_eq_parabolic_or_sylow
    (R P L : Subgroup (Model F)) (hR : R.IsPRadical 2)
    (hLP : L ≤ P) (hNP : normalizer (R : Set (Model F)) ≤ P)
    (hPL : P ≤ normalizer (L : Set (Model F)))
    (q : L →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hTL : (sylow (F := F) : Subgroup (Model F)) ≤ L) :
    normalizer (R : Set (Model F)) = P ∨
      ∃ S : Sylow 2 (Model F), (S : Subgroup (Model F)) = R := by
  have hRL := twoGroup_le_normal_sylow_overgroup R P L hR.isPGroup
    (R.le_normalizer.trans hNP) hLP hPL sylow hTL
  rcases Matrix.SpecialLinearGroup.radical_local_eq_kernel_or_sylow
    R L hR hRL (hNP.trans hPL) q hq hk sylow hTL with he | hs
  · left
    have hc : q.ker = pCore 2 L := by
      have hh := q.comap_pCore_of_ker_isPGroup hq hk (p := 2)
      rwa [Matrix.SL2.twoCore_eq_bot F,MonoidHom.comap_bot] at hh
    apply le_antisymm hNP
    rw [he,hc]
    exact hPL.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  · exact Or.inr hs

/-- A two-radical normalizer is a full root parabolic, unless the radical is Sylow. -/
theorem radical_normalizer_parabolic_or_sylow
    (R : Subgroup (Model F)) (hR : R.IsPRadical 2) :
    (∃ g : Model F,
      (normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom = parabolic₁ ∨
      (normalizer (R : Set (Model F))).map (MulAut.conj g).toMonoidHom = parabolic₂) ∨
      ∃ S : Sylow 2 (Model F), (S : Subgroup (Model F)) = R := by
  obtain ⟨g,hg⟩ := EvenLocal.NormalizerCover.normalizer_conjugate_le_parabolic R hR.1 hR.isPGroup
  let e := MulAut.conj g
  let U := R.map e.toMonoidHom
  have hu : U.IsPRadical 2 := hR.map_equiv e
  have hmap : (normalizer (R : Set (Model F))).map e.toMonoidHom =
      normalizer (U : Set (Model F)) := map_equiv_normalizer_eq R e
  rw [hmap] at hg
  have hsyl (S : Sylow 2 (Model F)) (hS : (S : Subgroup (Model F)) = U) :
      ∃ S : Sylow 2 (Model F), (S : Subgroup (Model F)) = R := by
    refine ⟨S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,?_⟩
    change (S : Subgroup (Model F)).map e.symm.toMonoidHom = R
    rw [hS]
    ext x
    constructor
    · rintro ⟨y,⟨r,hr,rfl⟩,rfl⟩
      simpa using hr
    · intro hx
      exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
  rcases hg with hp | hp
  · have hk : IsPGroup 2 (shortSLHom (F := F)).ker := by
      rw [shortSLHom_ker]
      exact (unipotent_isTwoGroup.to_le (fiveRootSubgroup_le_unipotent 5 (Or.inr rfl))).comap_subtype
    rcases normalizer_eq_parabolic_or_sylow U parabolic₁ local₁ hu
      (by rw [←local₁_sup_borel]; exact le_sup_left) hp parabolic₁_normalizes_local₁
      shortSLHom shortSLHom_surjective hk unipotent_le_local₁ with he | ⟨S,hS⟩
    · exact Or.inl ⟨g,Or.inl (hmap.trans he)⟩
    · exact Or.inr (hsyl S hS)
  · have hk : IsPGroup 2 (longSLHom (F := F)).ker := by
      rw [longSLHom_ker]
      exact radical₂_isTwoGroup.comap_subtype
    rcases normalizer_eq_parabolic_or_sylow U parabolic₂ local₂ hu local₂_le_parabolic₂
      hp parabolic₂_le_normalizer_local₂ longSLHom longSLHom_surjective hk
      unipotent_le_local₂ with he | ⟨S,hS⟩
    · exact Or.inl ⟨g,Or.inr (hmap.trans he)⟩
    · exact Or.inr (hsyl S hS)

/-- A radical normalizer contains a full Sylow normalizer. -/
theorem exists_sylow_normalizer_le_radical_normalizer
    (R : Subgroup (Model F)) (hR : R.IsPRadical 2) :
    ∃ S : Sylow 2 (Model F), normalizer (S : Set (Model F)) ≤ normalizer (R : Set (Model F)) := by
  rcases radical_normalizer_parabolic_or_sylow R hR with ⟨g,hg⟩ | ⟨S,hS⟩
  · let a := MulAut.conj g
    let S := (sylow (F := F)).mapSurjective (f := a.symm.toMonoidHom) a.symm.surjective
    refine ⟨S,?_⟩
    have he : ((S : Subgroup (Model F))).map a.toMonoidHom = unipotent := by
      change (((sylow (F := F)) : Subgroup (Model F)).map a.symm.toMonoidHom).map a.toMonoidHom = _
      have hc : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id (Model F) := by
        apply MonoidHom.ext
        intro x
        exact a.apply_symm_apply x
      rw [map_map,hc,map_id]
      rfl
    apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
    change (normalizer ((S : Subgroup (Model F)) : Set (Model F))).map a.toMonoidHom ≤ _
    rw [map_equiv_normalizer_eq (S : Subgroup (Model F)) a,he,
      SylowNormalizer.normalizer_unipotent]
    rcases hg with hg | hg
    · rw [hg]; exact borel_le_parabolic₁
    · rw [hg]; exact borel_le_parabolic₂
  · exact ⟨S, hS ▸ le_rfl⟩

/-- Every marked Sylow overgroup containing a radical normalizer contains
its full ambient Sylow normalizer. -/
theorem sylow_normalizer_le_of_radical_normalizer_le
    (R : Subgroup (Model F)) (hR : R.IsPRadical 2)
    (Q : Sylow 2 (Model F)) (M : Subgroup (Model F))
    (hQM : (Q : Subgroup (Model F)) ≤ M)
    (hRM : normalizer (R : Set (Model F)) ≤ M) :
    normalizer (Q : Set (Model F)) ≤ M := by
  obtain ⟨S,hS⟩ := exists_sylow_normalizer_le_radical_normalizer R hR
  exact normalizer_le_of_common_sylow S Q M
    (S.toSubgroup.le_normalizer.trans (hS.trans hRM)) hQM (hS.trans hRM)

end Atlas.G2
