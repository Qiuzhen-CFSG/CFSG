module

public import Theory.GroupTheory.Amalgam.RankTwo
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow normalization and the overlap obstruction for amalgams

For finite endpoint groups, independent endpoint isomorphisms can be adjusted
by Sylow conjugacy. Their restrictions then differ by one automorphism of the
middle group. This gives an isomorphism to an amalgam with one twisted overlap
embedding, preserving both commuting squares and faithfulness.

A twist can be removed when it factors as a left-extendible automorphism
followed by the inverse of a right-extendible automorphism. The final theorem
reduces recognition of an arbitrary faithful Sylow amalgam to this calculation
on the fixed model. It does not assert the calculation for any model.

`faithful_ofSubgroups_of_completion` obtains intrinsic amalgam faithfulness
from a generating completion with no nontrivial normal subgroup in the overlap.
Normality of the two images is relative to the two endpoint groups.

Application: the exceptional upgrades in Aschbacher--Smith, F.1.11--12,
printed pp.262--264. The proofs here use Sylow conjugacy and composition of
homomorphisms, independently of the unproved Fan--Goldschmidt classification.
-/

@[expose] public section
noncomputable section

namespace Theory.GroupTheory.RankTwoAmalgam

variable {L B R L' B' R' : Type*}
  [Group L] [Group B] [Group R] [Group L'] [Group B'] [Group R']

/-- No nontrivial subgroup of the overlap has normal images in both endpoints. -/
def Faithful (α : RankTwoAmalgam L B R) : Prop :=
  ∀ N : Subgroup B, (N.map α.left).Normal → (N.map α.right).Normal → N = ⊥

/-- Both structure maps are embeddings onto Sylow subgroups. -/
structure SylowEmbedded (p : ℕ) (α : RankTwoAmalgam L B R) : Prop where
  left_injective : Function.Injective α.left
  right_injective : Function.Injective α.right
  left_sylow : ∃ P : Sylow p L, (P : Subgroup L) = α.left.range
  right_sylow : ∃ P : Sylow p R, (P : Subgroup R) = α.right.range

/-- Keep the left map and precompose the right map with a middle automorphism. -/
def twistRight (β : RankTwoAmalgam L B R) (d : MulAut B) : RankTwoAmalgam L B R :=
  ⟨β.left, β.right.comp d.toMonoidHom⟩

/-- Extension along the specified map, with pointwise compatibility. -/
def ExtendsAcross (i : B →* L) (d : MulAut B) : Prop :=
  ∃ a : MulAut L, ∀ b, a (i b) = i (d b)

/-- The twist lies in the product of the two endpoint restriction groups. -/
def FactorsThrough (β : RankTwoAmalgam L B R) (d : MulAut B) : Prop :=
  ∃ l r : MulAut B, ExtendsAcross β.left l ∧ ExtendsAcross β.right r ∧
    d = l.trans r.symm

/-- Correct the two endpoints and the overlap simultaneously. -/
def FactorsThrough.iso {β : RankTwoAmalgam L B R} {d : MulAut B}
    (h : FactorsThrough β d) : Iso (twistRight β d) β := by
  apply Classical.choice
  obtain ⟨l, r, ⟨a, ha⟩, ⟨c, hc⟩, hd⟩ := h
  exact ⟨{
    left := a
    middle := l
    right := c
    left_commutes := ha
    right_commutes := fun b => by
      change c (β.right (d b)) = β.right (l b)
      rw [hc, hd]
      simp }⟩

/-- Faithfulness is invariant under a compatible isomorphism. -/
theorem Iso.faithful {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (e : Iso α β) (h : Faithful α) : Faithful β := by
  intro N hL hR
  let M := N.map e.middle.symm.toMonoidHom
  have hleft : M.map α.left = (N.map β.left).map e.left.symm.toMonoidHom := by
    simp only [M, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext (fun b => (e.symm.left_commutes b).symm)
  have hright : M.map α.right = (N.map β.right).map e.right.symm.toMonoidHom := by
    simp only [M, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext (fun b => (e.symm.right_commutes b).symm)
  have hm : M = ⊥ := h M
    (hleft ▸ hL.map e.left.symm.toMonoidHom e.left.symm.surjective)
    (hright ▸ hR.map e.right.symm.toMonoidHom e.right.symm.surjective)
  have hh := congrArg (Subgroup.map e.middle.toMonoidHom) hm
  simpa [M, Subgroup.map_map] using hh

/-- Sylow conjugacy aligns a single endpoint isomorphism on its overlap. -/
theorem exists_normalized_endpoint {p : ℕ} [Fact p.Prime] [Finite L']
    (i : B →* L) (j : B' →* L')
    (hi : Function.Injective i) (hj : Function.Injective j)
    (Pi : Sylow p L) (hPi : (Pi : Subgroup L) = i.range)
    (Pj : Sylow p L') (hPj : (Pj : Subgroup L') = j.range)
    (e : L ≃* L') :
    ∃ f : L ≃* L', ∃ u : B ≃* B', ∀ b, f (i b) = j (u b) := by
  let : Finite L := Finite.of_injective e e.injective
  let Q := Pi.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L' Q Pj
  let f := e.trans (MulAut.conj g)
  have hf : i.range.map f.toMonoidHom = j.range := by
    have hg' := congrArg (fun P : Sylow p L' => (P : Subgroup L')) hg
    change ((Pi : Subgroup L).map e.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (Pj : Subgroup L') at hg'
    simpa [hPi, hPj, Subgroup.map_map, f] using hg'
  let u : B ≃* B' := (MonoidHom.ofInjective hi).trans
    ((f.subgroupMap i.range).trans
      ((MulEquiv.subgroupCongr hf).trans (MonoidHom.ofInjective hj).symm))
  refine ⟨f, u, fun b => ?_⟩
  exact (MonoidHom.apply_ofInjective_symm hj
    ((MulEquiv.subgroupCongr hf) ((f.subgroupMap i.range)
      (MonoidHom.ofInjective hi b)))).symm

/-- Every parabolically equivalent Sylow amalgam is a twist of the fixed model. -/
theorem exists_twist_iso {p : ℕ} [Fact p.Prime] [Finite L'] [Finite R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (hα : SylowEmbedded p α) (hβ : SylowEmbedded p β)
    (e : ParabolicEquiv α β) :
    ∃ d : MulAut B', Nonempty (Iso α (twistRight β d)) := by
  obtain ⟨Pi, hPi⟩ := hα.left_sylow
  obtain ⟨Pj, hPj⟩ := hβ.left_sylow
  obtain ⟨f, u, hu⟩ := exists_normalized_endpoint α.left β.left
    hα.left_injective hβ.left_injective Pi hPi Pj hPj e.left
  obtain ⟨Qi, hQi⟩ := hα.right_sylow
  obtain ⟨Qj, hQj⟩ := hβ.right_sylow
  obtain ⟨g, v, hv⟩ := exists_normalized_endpoint α.right β.right
    hα.right_injective hβ.right_injective Qi hQi Qj hQj e.right
  refine ⟨u.symm.trans v, ⟨{
    left := f, middle := u, right := g, left_commutes := hu,
    right_commutes := fun b => ?_ }⟩⟩
  simpa [twistRight] using hv b

/-- A calculation on faithful model twists suffices for arbitrary-input rigidity.
The model calculation remains an explicit premise. -/
theorem iso_of_faithful_twist_factorization {p : ℕ} [Fact p.Prime]
    [Finite L'] [Finite R']
    {α : RankTwoAmalgam L B R} {β : RankTwoAmalgam L' B' R'}
    (hα : SylowEmbedded p α) (hβ : SylowEmbedded p β) (hfaith : Faithful α)
    (e : ParabolicEquiv α β)
    (hfactor : ∀ d : MulAut B', Faithful (twistRight β d) → FactorsThrough β d) :
    Nonempty (Iso α β) := by
  obtain ⟨d, ⟨f⟩⟩ := exists_twist_iso hα hβ e
  exact ⟨f.trans ((hfactor d (f.faithful hfaith)).iso)⟩

/-- A common ambient Sylow subgroup is Sylow in both containing parabolics. -/
theorem sylowEmbedded_ofSubgroups {G : Type*} [Group G] {p : ℕ}
    (S : Sylow p G) (P₁ D P₂ : Subgroup G)
    (h₁ : D ≤ P₁) (h₂ : D ≤ P₂) (hD : D = (S : Subgroup G)) :
    SylowEmbedded p (ofSubgroups P₁ D P₂ h₁ h₂) where
  left_injective := Subgroup.inclusion_injective h₁
  right_injective := Subgroup.inclusion_injective h₂
  left_sylow := ⟨S.subtype (hD ▸ h₁), by
    rw [Sylow.coe_subtype, ← hD]
    exact (Subgroup.inclusion_range h₁).symm⟩
  right_sylow := ⟨S.subtype (hD ▸ h₂), by
    rw [Sylow.coe_subtype, ← hD]
    exact (Subgroup.inclusion_range h₂).symm⟩

/-- Generation turns relative normality in both endpoints into normality in
the completion, where the source kernel condition applies. -/
theorem faithful_ofSubgroups_of_completion {G : Type*} [Group G]
    (P₁ D P₂ : Subgroup G) (h₁ : D ≤ P₁) (h₂ : D ≤ P₂)
    (hgen : P₁ ⊔ P₂ = ⊤)
    (hfaith : ∀ N : Subgroup G, N.Normal → N ≤ D → N = ⊥) :
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
  have hn : K.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_le_iff.mp (hgen ▸ sup_le hn₁ hn₂))
  exact (Subgroup.map_eq_bot_iff_of_injective N D.subtype_injective).mp
    (hfaith K hn hKD)

end Theory.GroupTheory.RankTwoAmalgam
