module
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
/-!
# Commuting factors of one or two alternating four-groups

A commuting factor of A₄ is either trivial or the whole group: the only
proper nontrivial normal subgroup is the Klein four-group, and A₄ is
centerless. Applying this to both coordinate projections shows that a
commuting factor of A₄ × A₄ is trivial, one coordinate axis, or the whole
product. The resulting isomorphisms retain the original embedded factor.

This is the factor restriction used for the A₃-block orbit in
Aschbacher--Smith 15.1.22(*), printed pp.1098--1099.
-/

public section
open Subgroup
namespace AlternatingFourPair

private theorem normal_of_commuting_sup_top {G : Type*} [Group G]
    (E C : Subgroup G) (hc : E ≤ centralizer (C : Set G)) (hg : E ⊔ C = ⊤) :
    E.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [←hg]
  exact sup_le E.le_normalizer
    ((le_centralizer_iff.mp hc).trans (centralizer_le_normalizer _))

theorem commuting_single_factors (E C : Subgroup A)
    (hc : E ≤ centralizer (C : Set A)) (hg : E ⊔ C = ⊤) :
    (E = ⊤ ∧ C = ⊥) ∨ (E = ⊥ ∧ C = ⊤) := by
  let := normal_of_commuting_sup_top E C hc hg
  let := normal_of_commuting_sup_top C E (le_centralizer_iff.mp hc) (sup_comm E C ▸ hg)
  have htop : E = ⊤ ∨ C = ⊤ := by
    by_contra hn
    have hnE := fun h => hn (Or.inl h)
    have hnC := fun h => hn (Or.inr h)
    have hEK : E ≤ K := by
      rcases normalA4 E with h | h | h
      · rw [h]; exact bot_le
      · exact h.le
      · exact (hnE h).elim
    have hCK : C ≤ K := by
      rcases normalA4 C with h | h | h
      · rw [h]; exact bot_le
      · exact h.le
      · exact (hnC h).elim
    have hKtop : K = ⊤ := top_unique (hg ▸ sup_le hEK hCK)
    have hcard := alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num : Nat.card (Fin 4) = 4)
    change Nat.card K = 4 at hcard
    rw [hKtop] at hcard
    rw [Nat.card_congr (Subgroup.topEquiv (G := A)).toEquiv] at hcard
    have ha : Nat.card A = 12 := alternatingGroup.card_of_card_eq_four (by norm_num)
    omega
  have hz : center A = ⊥ := alternatingGroup.center_eq_bot (by norm_num)
  rcases htop with he | he
  · left
    refine ⟨he,le_bot_iff.mp ?_⟩
    have hh := le_centralizer_iff.mp hc
    rw [he, coe_top, centralizer_univ] at hh
    exact hh.trans_eq hz
  · right
    refine ⟨le_bot_iff.mp ?_,he⟩
    rw [he, coe_top, centralizer_univ] at hc
    exact hc.trans_eq hz

theorem commuting_factor_cases (E C : Subgroup Model)
    (hc : E ≤ centralizer (C : Set Model)) (hg : E ⊔ C = ⊤) :
    E = ⊥ ∨ E = axis0 ∨ E = axis1 ∨ E = ⊤ := by
  let f : Model →* A := MonoidHom.fst A A
  let g : Model →* A := MonoidHom.snd A A
  have hcf : E.map f ≤ centralizer (C.map f : Set A) := by
    rintro _ ⟨e,he,rfl⟩ _ ⟨c,hc',rfl⟩
    exact congrArg f (hc he c hc')
  have hcg : E.map g ≤ centralizer (C.map g : Set A) := by
    rintro _ ⟨e,he,rfl⟩ _ ⟨c,hc',rfl⟩
    exact congrArg g (hc he c hc')
  have hgf : E.map f ⊔ C.map f = ⊤ := by
    rw [←Subgroup.map_sup,hg,map_top_of_surjective _ (fun a => ⟨(a,1),rfl⟩)]
  have hgg : E.map g ⊔ C.map g = ⊤ := by
    rw [←Subgroup.map_sup,hg,map_top_of_surjective _ (fun a => ⟨(1,a),rfl⟩)]
  have hzero (D : Subgroup Model) (hf : D.map f = ⊥) (hg : D.map g = ⊥) : D = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have h1 := hf ▸ mem_map_of_mem f hx
    have h2 := hg ▸ mem_map_of_mem g hx
    exact mem_bot.mpr (Prod.ext (mem_bot.mp h1) (mem_bot.mp h2))
  rcases commuting_single_factors (E.map f) (C.map f) hcf hgf with ⟨hef,hcf⟩ | ⟨hef,hcf⟩ <;>
    rcases commuting_single_factors (E.map g) (C.map g) hcg hgg with ⟨heg,hcg⟩ | ⟨heg,hcg⟩
  · exact Or.inr (Or.inr (Or.inr (by simpa [hzero C hcf hcg] using hg)))
  · right; left
    apply le_antisymm
    · intro x hx
      exact ⟨mem_top _, mem_bot.mp (heg ▸ mem_map_of_mem g hx)⟩
    · intro x hx
      have hm : x.1 ∈ E.map f := hef ▸ mem_top _
      obtain ⟨y,hy,hyx⟩ := hm
      have hy2 : y.2 = 1 := mem_bot.mp (heg ▸ mem_map_of_mem g hy)
      have hx2 : x.2 = 1 := hx.2
      have he : y = x := Prod.ext hyx (hy2.trans hx2.symm)
      exact he ▸ hy
  · right; right; left
    apply le_antisymm
    · intro x hx
      exact ⟨mem_bot.mp (hef ▸ mem_map_of_mem f hx), mem_top _⟩
    · intro x hx
      have hm : x.2 ∈ E.map g := heg ▸ mem_top _
      obtain ⟨y,hy,hyx⟩ := hm
      have hy1 : y.1 = 1 := mem_bot.mp (hef ▸ mem_map_of_mem f hy)
      have hx1 : x.1 = 1 := hx.1
      have he : y = x := Prod.ext (hy1.trans hx1.symm) hyx
      exact he ▸ hy
  · exact Or.inl (hzero E hef heg)

noncomputable def axis0Equiv : axis0 ≃* A where
  toFun x := x.1.1
  invFun a := ⟨(a,1),mem_top a,rfl⟩
  left_inv x := Subtype.ext (Prod.ext rfl (show 1 = x.1.2 from x.2.2.symm))
  right_inv _ := rfl
  map_mul' _ _ := rfl

noncomputable def axis1Equiv : axis1 ≃* A where
  toFun x := x.1.2
  invFun a := ⟨(1,a),rfl,mem_top a⟩
  left_inv x := Subtype.ext (Prod.ext (show 1 = x.1.1 from x.2.1.symm) rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem commuting_factor_model {H : Type*} [Group H]
    (E C : Subgroup H) (hc : E ≤ centralizer (C : Set H)) (hg : E ⊔ C = ⊤)
    (hm : Nonempty (H ≃* A) ∨ Nonempty (H ≃* Model)) :
    E = ⊥ ∨ Nonempty (E ≃* A) ∨ Nonempty (E ≃* Model) := by
  have hcomm {J : Type} [Group J] (e : H ≃* J) :
      E.map e.toMonoidHom ≤ centralizer (C.map e.toMonoidHom : Set J) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hc hx y hy)
  have hgen {J : Type} [Group J] (e : H ≃* J) :
      E.map e.toMonoidHom ⊔ C.map e.toMonoidHom = ⊤ := by
    rw [←Subgroup.map_sup,hg,map_top_of_surjective _ e.surjective]
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    rcases commuting_single_factors _ _ (hcomm e) (hgen e) with ⟨he,_⟩ | ⟨he,_⟩
    · exact Or.inr (Or.inl ⟨(e.subgroupMap E).trans
        ((MulEquiv.subgroupCongr he).trans topEquiv)⟩)
    · exact Or.inl ((map_eq_bot_iff_of_injective _ e.injective).mp he)
  · obtain ⟨e⟩ := hm
    rcases commuting_factor_cases _ _ (hcomm e) (hgen e) with he | he | he | he
    · exact Or.inl ((map_eq_bot_iff_of_injective _ e.injective).mp he)
    · exact Or.inr (Or.inl ⟨(e.subgroupMap E).trans
        ((MulEquiv.subgroupCongr he).trans axis0Equiv)⟩)
    · exact Or.inr (Or.inl ⟨(e.subgroupMap E).trans
        ((MulEquiv.subgroupCongr he).trans axis1Equiv)⟩)
    · exact Or.inr (Or.inr ⟨(e.subgroupMap E).trans
        ((MulEquiv.subgroupCongr he).trans topEquiv)⟩)
end AlternatingFourPair
