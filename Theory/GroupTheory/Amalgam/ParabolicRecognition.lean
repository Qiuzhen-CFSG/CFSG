module
public import Theory.GroupTheory.Amalgam.SylowRigidity
public import Theory.PGroupCore

/-!
# Recognition of an embedded parabolic amalgam

Independent isomorphisms of the three groups preserve the order of the overlap
and both endpoints. If the model overlap is Sylow and the input maps are
injective, the input ranges have the full Sylow order as well. No compatibility
of these initial isomorphisms is required.

For an inclusion amalgam with a p-group overlap, a subgroup normal in both
endpoints is normal in their join. A trivial p-core of that join therefore
implies intrinsic amalgam faithfulness, even in a larger ambient group.

These two bridges discharge the input premises of Sylow normalization in
`CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalRigidity`, using the
literal source Borel and F.1.1(e). Source: Aschbacher--Smith, F.1.1 and
F.1.11--12, printed pp.259 and 262--263.
-/
@[expose] public section
noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam
variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']
private theorem sylow_of_equiv {p : ℕ} [Fact p.Prime] [Finite L']
    (i : B →* L) (j : B' →* L')
    (hi : Function.Injective i) (hj : Function.Injective j)
    (P : Sylow p L') (hP : (P : Subgroup L') = j.range)
    (eL : L ≃* L') (eB : B ≃* B') :
    ∃ Q : Sylow p L, (Q : Subgroup L) = i.range := by
  let : Finite L := Finite.of_injective eL eL.injective
  have hcard : Nat.card i.range = p ^ (Nat.card L).factorization p := by
    calc
      Nat.card i.range = Nat.card B := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
      _ = Nat.card B' := Nat.card_congr eB.toEquiv
      _ = Nat.card j.range := Nat.card_congr (MonoidHom.ofInjective hj).toEquiv
      _ = Nat.card P := Nat.card_congr (MulEquiv.subgroupCongr hP.symm).toEquiv
      _ = p ^ (Nat.card L').factorization p := P.card_eq_multiplicity
      _ = p ^ (Nat.card L).factorization p := by rw [Nat.card_congr eL.toEquiv]
  exact ⟨Sylow.ofCard i.range hcard, Sylow.coe_ofCard _ _⟩

/-- Injective input maps and the three group isomorphisms force Sylow ranges. -/
theorem SylowEmbedded.of_parabolicEquiv {p : ℕ} [Fact p.Prime]
    [Finite L'] [Finite R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (hβ : SylowEmbedded p β) (e : ParabolicEquiv α β)
    (hleft : Function.Injective α.left) (hright : Function.Injective α.right) :
    SylowEmbedded p α := by
  obtain ⟨P, hP⟩ := hβ.left_sylow
  obtain ⟨Q, hQ⟩ := hβ.right_sylow
  exact ⟨hleft, hright,
    sylow_of_equiv α.left β.left hleft hβ.left_injective P hP e.left e.middle,
    sylow_of_equiv α.right β.right hright hβ.right_injective Q hQ e.right e.middle⟩

/-- The middle group is a p-group because its left image is Sylow. -/
theorem SylowEmbedded.isPGroup {p : ℕ} {α : RankTwoAmalgam L B R}
    (h : SylowEmbedded p α) : IsPGroup p B := by
  obtain ⟨P, hP⟩ := h.left_sylow
  have hp : IsPGroup p α.left.range := hP ▸ P.isPGroup'
  exact hp.of_injective (MonoidHom.ofInjective h.left_injective).toMonoidHom
    (MonoidHom.ofInjective h.left_injective).injective

/-- A p-group overlap and trivial p-core of the generated group imply faithfulness.
Normality is relative to each endpoint and then to their join. -/
theorem faithful_ofSubgroups_of_pCore_eq_bot {G : Type*} [Group G] {p : ℕ}
    (P₁ D P₂ : Subgroup G) (h₁ : D ≤ P₁) (h₂ : D ≤ P₂)
    (hD : IsPGroup p D) (hcore : pCore p (P₁ ⊔ P₂ : Subgroup G) = ⊥) :
    Faithful (ofSubgroups P₁ D P₂ h₁ h₂) := by
  intro N hL hR
  let K := N.map D.subtype
  have hKD : K ≤ D := Subgroup.map_subtype_le N
  have hKP₁ : K ≤ P₁ := hKD.trans h₁
  have hKP₂ : K ≤ P₂ := hKD.trans h₂
  have he₁ : K.subgroupOf P₁ = N.map (Subgroup.inclusion h₁) := by
    apply Subgroup.map_injective P₁.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKP₁, Subgroup.map_map]
    rfl
  have he₂ : K.subgroupOf P₂ = N.map (Subgroup.inclusion h₂) := by
    apply Subgroup.map_injective P₂.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hKP₂, Subgroup.map_map]
    rfl
  have hn₁ : P₁ ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP₁).mp (he₁ ▸ hL)
  have hn₂ : P₂ ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKP₂).mp (he₂ ▸ hR)
  have hn : (K.subgroupOf (P₁ ⊔ P₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hKP₁.trans le_sup_left)).mpr
      (sup_le hn₁ hn₂)
  have hp : IsPGroup p (K.subgroupOf (P₁ ⊔ P₂)) :=
    ((hD.to_subgroup N).map D.subtype).comap_subtype
  have hle : K.subgroupOf (P₁ ⊔ P₂) ≤ pCore p (P₁ ⊔ P₂ : Subgroup G) :=
    le_sSup ⟨hn, hp⟩
  have hk : K = ⊥ := by
    have he := congrArg (Subgroup.map (P₁ ⊔ P₂).subtype)
      (bot_unique (hcore ▸ hle))
    simpa only [Subgroup.map_subgroupOf_eq_of_le (hKP₁.trans le_sup_left),
      Subgroup.map_bot] using he
  exact (Subgroup.map_eq_bot_iff_of_injective N D.subtype_injective).mp hk
end Theory.GroupTheory.RankTwoAmalgam
