module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.TwoFactorDecomposition
public import Theory.Representation.BinaryTwoPlaneRecognition.OrderThirtySix
public import Theory.GroupTheory.NormalizedSupCard
/-!
# A transitive pair of natural symmetric-three factors

A full two-factor decomposition with factor orders six and support dimensions
two has the actual natural orthogonal four-dimensional action. The embedded
commuting actors have product order 36. Transitivity makes that product proper:
if it were the whole group, each factor would be normal. Permutation of the
complementary planes embeds the faithful group into O₄⁺(2), of order 72, so the
embedding is onto. Both actor and vector coordinates retain the original action.

Source: Aschbacher--Smith 15.1.2(3) and the small-module branch preceding
15.1.8, printed pp.1086--1088.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.RatioDecomposition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K : Subgroup G} {U : Submodule (ZMod 2) V}
  (c : FactorData ρ K U) (d : Decomposition c.representation)
namespace FactorData

theorem two_plane_isometry_coordinates (hf : Function.Injective ρ)
    (hU : U = ⊤) (hcount : Nat.card d.Index = 2)
    (hcard : ∀ i, Nat.card (d.factor i).Carrier = 6)
    (hdim : ∀ i, Module.finrank (ZMod 2) (d.factor i).Space = 2)
    (π : G →* Equiv.Perm d.Index)
    (hp : ∀ g i, (c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g i)).actor)
    (hs : ∀ g i, (c.ambientFactor d i).space.map (ρ g) =
      (c.ambientFactor d (π g i)).space)
    (ht : ∀ i j, ∃ g : G, π g i = j) :
    ∃ (a : V ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : G ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      ∀ g v, a (ρ g v) = (e g).val (a v) := by
  obtain ⟨i,j,hij,hall,hgen,hdis,hcom,hcompl⟩ :=
    c.two_factor_literal_decomposition d hU hcount
  have hdim' (k : d.Index) : Module.finrank (ZMod 2) (c.ambientFactor d k).space = 2 := by
    let a := (c.ambientFactor d k).embedding.spaceMap
    let e := LinearEquiv.ofInjective a (c.ambientFactor d k).embedding.space_injective
    exact e.finrank_eq.symm.trans (hdim k)
  have hcard' (k : d.Index) : Nat.card (c.ambientFactor d k).actor = 6 := by
    exact (Nat.card_range_of_injective
      (c.ambientFactor d k).embedding.group_injective).trans (hcard k)
  have hn : (c.ambientFactor d j).actor ≤ normalizer ((c.ambientFactor d i).actor : Set G) := by
    apply le_normalizer_iff.mpr
    intro y hy x hx
    rw [(hcom x hx y hy).symm.eq, mul_inv_cancel_right]
    exact hx
  have hK : Nat.card K = 36 := by
    rw [← hgen, card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hdis,
      hcard', hcard']
  have hproper : K ≠ ⊤ := by
    intro he
    apply c.transitive_actor_not_normal d π hp ht (by omega) i
    have hsurj : Function.Surjective K.subtype := by
      intro g
      exact ⟨⟨g,he ▸ mem_top g⟩,rfl⟩
    simpa only [ambientFactor,Factor.map_actor,embedding] using
      Normal.map (d.actor_normal c.representation c.faithful i) K.subtype hsurj
  have hmove (g : G) (v : V) :
      v ∈ (c.ambientFactor d i).space ∨ v ∈ (c.ambientFactor d j).space →
      ρ g v ∈ (c.ambientFactor d i).space ∨ ρ g v ∈ (c.ambientFactor d j).space := by
    intro hv
    have hm (k : d.Index) (hk : v ∈ (c.ambientFactor d k).space) :
        ρ g v ∈ (c.ambientFactor d (π g k)).space := by
      rw [← hs]
      exact ⟨v,hk,rfl⟩
    rcases hv with hv | hv
    · rcases hall (π g i) with he | he
      · exact Or.inl (he ▸ hm i hv)
      · exact Or.inr (he ▸ hm i hv)
    · rcases hall (π g j) with he | he
      · exact Or.inl (he ▸ hm j hv)
      · exact Or.inr (he ▸ hm j hv)
  have hunion (g : G) (v : V) :
      (ρ g v ∈ (c.ambientFactor d i).space ∨ ρ g v ∈ (c.ambientFactor d j).space) ↔
      (v ∈ (c.ambientFactor d i).space ∨ v ∈ (c.ambientFactor d j).space) := by
    refine ⟨fun h => ?_,hmove g v⟩
    have hh := hmove g⁻¹ (ρ g v) h
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hh
  obtain ⟨a,f,hfi,ha⟩ := BinaryTwoPlaneRecognition.exists_isometry_embedding ρ hf
    _ _ hcompl (hdim' i) (hdim' j) hunion
  have hbound : Nat.card G ≤ 72 :=
    (Nat.card_le_card_of_injective f hfi).trans_eq OrthogonalFourBinary.isometryGroup_card
  have hdiv : 36 ∣ Nat.card G := hK ▸ K.card_subgroup_dvd_card
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcards : Nat.card G = 36 ∨ Nat.card G = 72 := by
    obtain ⟨n,hn⟩ := hdiv
    omega
  have h72 : Nat.card G = 72 := hcards.resolve_left fun h =>
    hproper (K.eq_top_of_card_eq (hK.trans h.symm))
  exact ⟨a,MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr
    ⟨hfi,h72.trans OrthogonalFourBinary.isometryGroup_card.symm⟩),ha⟩
end FactorData
end CFSG.Quasithin.ChapterD.RatioDecomposition
