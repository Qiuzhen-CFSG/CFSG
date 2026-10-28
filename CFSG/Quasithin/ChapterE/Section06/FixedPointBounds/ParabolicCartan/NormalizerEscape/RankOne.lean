module

public import Theory.GroupTheory.CyclicHallNormalizerEscape
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.Reflections.RankOne

/-!
# Full rank-one Borel normalizer escape

The binary PSL₂ and Suzuki Borel has a normal two-group supplemented by its
full cyclic torus. Sylow conjugacy moves any prescribed odd-primary subgroup
into that torus. The actual Weyl element normalizes every subgroup of the
torus and lies outside the Borel, giving escape for the original subgroup.

Source: Aschbacher–Smith 4.4.13(1), printed pp.623–624, rank-one rows.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels BenderSuzuki.Converse BenderSuzuki.MatrixGroups

private theorem escape_of_root_torus {G : Type*} [Group G] [Finite G]
    (U C B : Subgroup G) [IsCyclic C] (hU : IsPGroup 2 U)
    (hgen : U ⊔ C = B) (hnorm : (U.subgroupOf B).Normal)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsPGroup p A) (hAB : A ≤ B)
    (w : G) (hw : w ∈ normalizer (C : Set G)) (hout : w ∉ B) :
    ¬ normalizer (A : Set G) ≤ B := by
  have hUB : U ≤ B := hgen ▸ le_sup_left
  have hCB : C ≤ B := hgen ▸ le_sup_right
  let := hnorm
  have hs : U.subgroupOf B ⊔ C.subgroupOf B = ⊤ := by
    rw [← subgroupOf_sup hUB hCB,hgen,subgroupOf_self]
  have hd := index_dvd_of_normal_supplement (U.subgroupOf B) (C.subgroupOf B) hs
  have hindex : ¬ p ∣ (C.subgroupOf B).index := by
    have hUBp : IsPGroup 2 (U.subgroupOf B) := hU.comap_subtype
    obtain ⟨n,hn⟩ := hUBp.exists_card_eq
    have hc : Nat.Coprime p (Nat.card (U.subgroupOf B)) := by
      rw [hn]
      exact hp.coprime_two_right.pow_right n
    exact fun hh => (Fact.out : p.Prime).ne_one
      (Nat.eq_one_of_dvd_coprimes hc (dvd_refl p) (hh.trans hd))
  exact normalizer_not_le_of_cyclic_torus B C A hCB hindex hA hAB w hw hout

/-- Every odd-primary subgroup of the full binary PSL₂ Borel has an
escaping normalizer; the original subgroup need not lie in the chosen torus. -/
theorem psl2_full_borel_escape {F : Type*} [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2^f) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (PSL2 F)) (hA : IsPGroup p A) (hAB : A ≤ PBorel F) :
    ¬ normalizer (A : Set _) ≤ PBorel F := by
  let : IsCyclic (PTorus F) := by
    change IsCyclic ((Torus F).map (pi F))
    rw [Torus_eq_range,MonoidHom.map_range]
    exact isCyclic_of_surjective _ ((pi F).comp (torHom F)).rangeRestrict_surjective
  obtain ⟨w,hw,hinv⟩ := Tori.exists_psl2Torus_reflection (F := F)
  apply escape_of_root_torus (PUnip F) (PTorus F) (PBorel F)
    (IsPGroup.of_card (by rw [PUnip_card,hF]))
    PUnip_sup_PTorus PUnip_normal_in_PBorel hp A hA hAB w ?_ hw
  apply mem_normalizer_fintype
  intro x hx
  change x ∈ (Torus F).map (pi F) at hx
  rw [Torus_eq_range,MonoidHom.map_range] at hx
  obtain ⟨a,rfl⟩ := hx
  rw [show w * ((pi F).comp (torHom F)) a * w⁻¹ =
    (((pi F).comp (torHom F)) a)⁻¹ from hinv a]
  apply (PTorus F).inv_mem
  exact mem_map_of_mem _ (Torus_eq_range (F := F) ▸ ⟨a,rfl⟩)

/-- Every odd-primary subgroup of the full Suzuki Borel has an escaping
normalizer, on the literal matrix Suzuki carrier. -/
theorem suzuki_full_borel_escape (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (SuzukiMatrixGroup m)) (hA : IsPGroup p A)
    (hAB : A ≤ SuzukiBorelSubgroup m) :
    ¬ normalizer (A : Set _) ≤ SuzukiBorelSubgroup m := by
  let := suzukiSplitTorus_isCyclic m hm
  obtain ⟨w,hw,hinv⟩ := Tori.exists_suzukiTorus_reflection m hm
  apply escape_of_root_torus (SuzukiRootSubgroup m) (SuzukiSplitTorus m)
    (SuzukiBorelSubgroup m) (suzukiRootSubgroup_isPGroup m hm)
    (suzukiBorelSubgroup_eq_sup m).symm (suzukiRootSubgroup_normal_in_borel m)
    hp A hA hAB w ?_ hw
  apply mem_normalizer_fintype
  intro x hx
  obtain ⟨a,ha⟩ := (suzukiSplitTorus_equiv_units m hm).some.surjective ⟨x,hx⟩
  have he : (Tori.suzukiTorus m hm a : SuzukiMatrixGroup m) = x := congrArg Subtype.val ha
  rw [← he,hinv]
  exact (SuzukiSplitTorus m).inv_mem ((suzukiSplitTorus_equiv_units m hm).some a).property

/-- Transport of the two full rank-one model results through the actual
source component and its marked overlap. -/
theorem rank_one_sourceImage_escape {X : Type*} [Group X]
    {M K : Subgroup X} {f : ℕ} (hm : ExchangedModel M K f)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (sourceImage M K)) (hA : IsPGroup p A)
    (hAB : A ≤ componentOverlap M K) :
    ¬ normalizer (A : Set _) ≤ componentOverlap M K := by
  rcases hm with ⟨F,hfield,hfin,hchar,_,hF,e,he⟩ | ⟨m,hm,_,e,he⟩
  · let := hfield
    let := hfin
    let := hchar
    have hout := psl2_full_borel_escape hF hp (A.map e.toMonoidHom)
      (hA.map _) ((map_mono hAB).trans_eq he)
    intro hn
    apply hout
    rw [← map_equiv_normalizer_eq]
    exact (map_mono hn).trans_eq he
  · have hout := suzuki_full_borel_escape m (by omega) hp (A.map e.toMonoidHom)
      (hA.map _) ((map_mono hAB).trans_eq he)
    intro hn
    apply hout
    rw [← map_equiv_normalizer_eq]
    exact (map_mono hn).trans_eq he

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
