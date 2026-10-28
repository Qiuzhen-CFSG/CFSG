module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.Elementary
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles

/-!
# The uniform characteristic pair for an abelian base

For an abelian marked Sylow subgroup of a characteristic-two local group,
self-centralization of the two-core forces the Sylow image to equal that
core. Thus the whole base is normal in every possible marked overgroup.
Choosing it as the second member of a characteristic pair proves the full
universal alternative in the abelian case: the pair precedes all groups and
all embeddings. The final theorem applies the literal center restriction of
C.1.19, retaining both marked subgroup maps.

Source: Aschbacher–Smith C.1.17–19, printed pp.126–127. This closes the
abelian-base branch of C.1.18; no general uniform pushing-up theorem is
asserted for nonabelian bases.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
universe u v
variable {B : Type u} [Group B] [IsMulCommutative B]

/-- In the characteristic-two local class, an abelian Sylow subgroup is
necessarily the actual two-core. -/
theorem InLocalClass.range_eq_core_of_abelian
    {H : Type v} [Group H] [Finite H] {e : B →* H} (h : InLocalClass e) :
    e.range = pCore 2 H := by
  obtain ⟨T,he,_⟩ := h.sylow
  have hQ : pCore 2 H ≤ e.range := by
    rw [he]
    exact pCore_isPGroup.le_sylow_of_normal T
  apply le_antisymm ?_ hQ
  apply le_trans ?_ h.core_selfCentralizing
  rintro _ ⟨b,rfl⟩ q hq
  obtain ⟨c,rfl⟩ := hQ hq
  exact (map_mul e c b).symm.trans ((congrArg e (mul_comm' c b)).trans (map_mul e b c))

/-- Every marked local overgroup normalizes the same whole base subgroup. -/
theorem InLocalClass.range_normal_of_abelian
    {H : Type v} [Group H] [Finite H] {e : B →* H} (h : InLocalClass e) :
    e.range.Normal := by
  rw [h.range_eq_core_of_abelian]
  infer_instance

/-- The abelian case of C.1.18 has one pair before all local groups and all
markings. Its second member is the whole base, independent of the overgroup. -/
theorem exists_universal_of_abelian [Finite B] [Nontrivial B] (hB : IsPGroup 2 B) :
    ∃ D : CharacteristicPair B, D.second = ⊤ ∧ D.Universal.{u,v} := by
  obtain ⟨D⟩ := nonempty_characteristicPair hB
  let E : CharacteristicPair B :=
    { D with
      second := ⊤
      second_characteristic := by infer_instance
      second_ne_bot := top_ne_bot }
  refine ⟨E,rfl,?_⟩
  intro H _ _ e he
  right; left
  change ((⊤ : Subgroup B).map e).Normal
  have ht : (⊤ : Subgroup B).map e = e.range := by
    ext x
    simp
  rw [ht]
  exact he.range_normal_of_abelian

/-- The actual C.1.19 reduction for an abelian characteristic base. The pair
is chosen once, and the literal restricted first subgroup and embedded second
subgroup satisfy C.1.18 in every marked local overgroup of the base. -/
theorem exists_reducedPair_of_abelian_base
    {S : Type u} [Group S] [Finite S] (hS : IsPGroup 2 S)
    (B : Subgroup S) [B.Characteristic] [Nontrivial B] [IsMulCommutative B] :
    ∃ C : RankOneCharacteristicPair B,
      ∀ (H : Type v) [Group H] [Finite H] (e : B →* H),
        InLocalClass e → Alternatives (C.first.subgroupOf B) C.second e := by
  obtain ⟨D,_,hD⟩ := exists_universal_of_abelian.{u,v} (hS.to_subgroup B)
  let : D.first.Characteristic := D.first_characteristic
  let : D.second.Characteristic := D.second_characteristic
  let C := glaubermanNiles_reducePair hS B D.first D.second D.first_ne_bot
    D.second_ne_bot D.first_le_omegaCenter
  refine ⟨C,?_⟩
  intro H _ _ e he
  have h := glaubermanNiles_reduction_alternatives B D.first D.second e
    (BlockAlternative H) (hD H e he)
  change Alternatives ((centerRestriction B D.first).subgroupOf B) D.second e
  simpa only [Alternatives, image_subgroupOf_subtype] using h

end CFSG.Quasithin.ChapterC.GlaubermanNiles
