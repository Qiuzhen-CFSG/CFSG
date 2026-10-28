module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.Coordinates

/-!
# Fixed spaces in the mixed factor configuration

The exact Thompson omega center is normalized by the Sylow subgroup and lies in
its Baumann subgroup. The realized fixed-space direct products, the two distinct
unique maximal two-local overgroups, and the central fixed line from 15.4.14 give
order eight and a nontrivial common fixed subgroup. Once the three order-two
summands are preserved, they are fixed pointwise. The common fixed subgroup
centralizes exactly one of the two factors of `X`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, the second paragraph of 15.4.18, printed p.1162.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The exact Thompson omega center belongs to its Baumann centralizer. -/
theorem alpha_le_baumann (T : Subgroup G) :
    ChapterB.thompsonAlpha T ≤ ChapterB.baumann T := by
  let E := ChapterB.thompsonAlpha T
  let : IsElementaryAbelian 2 E := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hET : E ≤ T := by
    intro e he
    have hej := ((Stellmacher.mem_omegaOneCenterAmbient_iff _ e).mp he).1
    exact (sSup_le (fun _ hA => hA.1) : Stellmacher.elementaryAbelianMaxJ T ≤ T) hej
  refine le_inf hET ?_
  intro e he x hx
  exact setLike_mul_comm hx he

/-- Relative normalization of the Thompson omega center, obtained by
transporting the elementary Thompson subgroup and its omega center. -/
theorem normalizes_alpha (T : Subgroup G) :
    T ≤ normalizer (ChapterB.thompsonAlpha T : Set G) := by
  intro t ht
  have hT := mem_normalizer_iff_map_conj_eq.mp (T.le_normalizer ht)
  rw [mem_normalizer_iff_map_conj_eq]
  change (Stellmacher.omegaOneCenterAmbient (Stellmacher.elementaryAbelianMaxJ T)).map
    (MulAut.conj t).toMonoidHom = _
  rw [← Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective,
    ← Stellmacher.elementaryAbelianMaxJ_map_equiv]
  have htmap : T.map (MulAut.conj t).toMonoidHom = T := hT
  rw [htmap]
  rfl

private theorem normalizer_le_centralizer_of_card_two
    (A : Subgroup G) (hA : Nat.card A = 2) :
    normalizer (A : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro g hg x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    apply hxone
    exact (MulAut.conj g).map_eq_one_iff.mp (congrArg Subtype.val hy)
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val heq)).symm

variable [Finite G]

private theorem index_of_fixed_complement {E C F : Subgroup G} [IsMulCommutative E]
    (hsplit : C ⊔ F = E) (hdis : Disjoint C F) :
    C.relIndex E = Nat.card F := by
  have hc : C ≤ centralizer (F : Set G) := by
    intro c hC f hF
    exact setLike_mul_comm (hsplit ▸ mem_sup_right hF) (hsplit ▸ mem_sup_left hC)
  obtain ⟨e, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C F hdis hc
  have he : Nat.card E = Nat.card C * Nat.card F := by
    rw [← hsplit, ← Nat.card_congr e.toEquiv, Nat.card_prod]
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) C E bot_le (hsplit ▸ le_sup_left)
  rw [relIndex_bot_left, relIndex_bot_left, he] at hi
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hi

/-- The mixed fixed-space calculation from the realized direct products and
15.4.14. The two distinct unique overgroups force disjoint fixed subgroups;
this constructs order eight and the nontrivial common fixed subgroup. -/
theorem fixed_geometry (T : Sylow 2 G)
    {E Y₁ Y₂ X M₁ M₂ F₁ F₂ Fₓ : Subgroup G} [IsElementaryAbelian 2 E]
    (hE : E = ChapterB.thompsonAlpha (T : Subgroup G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y₁ : Set G))
    (hTX : (T : Subgroup G) ≤ normalizer (X : Set G))
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y₁ ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hsplit₁ : (E ⊓ centralizer (Y₁ : Set G)) ⊔ F₁ = E)
    (hdis₁ : Disjoint (E ⊓ centralizer (Y₁ : Set G)) F₁) (hc₁ : Nat.card F₁ = 2)
    (hsplit₂ : (E ⊓ centralizer (Y₂ : Set G)) ⊔ F₂ = E)
    (hdis₂ : Disjoint (E ⊓ centralizer (Y₂ : Set G)) F₂) (hc₂ : Nat.card F₂ = 2)
    (hsplitₓ : (E ⊓ centralizer (X : Set G)) ⊔ Fₓ = E)
    (hdisₓ : Disjoint (E ⊓ centralizer (X : Set G)) Fₓ) (hcₓ : Nat.card Fₓ = 4)
    (hZ : Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (X : Set G) : Subgroup G) = 2) :
    (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (X : Set G)) = ⊥ ∧
    Nat.card (E ⊓ centralizer (X : Set G) : Subgroup G) = 2 ∧
    Nat.card E = 8 ∧
    (E ⊓ centralizer (Y₁ : Set G)).relIndex E = 2 ∧
    (E ⊓ centralizer (Y₂ : Set G)).relIndex E = 2 ∧
    (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G)) ≠ ⊥ := by
  have hET : E ≤ (T : Subgroup G) :=
    (hE ▸ alpha_le_baumann (T : Subgroup G)).trans inf_le_left
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) := hE ▸ normalizes_alpha _
  have hd := fixed_subgroups_disjoint T.isPGroup' hET hTE hTY hTX huniqueY huniqueX hne
  have hi₁ : (E ⊓ centralizer (Y₁ : Set G)).relIndex E = 2 :=
    (index_of_fixed_complement hsplit₁ hdis₁).trans hc₁
  have hi₂ : (E ⊓ centralizer (Y₂ : Set G)).relIndex E = 2 :=
    (index_of_fixed_complement hsplit₂ hdis₂).trans hc₂
  have hiₓ : (E ⊓ centralizer (X : Set G)).relIndex E = 4 :=
    (index_of_fixed_complement hsplitₓ hdisₓ).trans hcₓ
  have hZE : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ E :=
    hE ▸ centralOmega_le_thompsonAlpha _
  obtain ⟨hx, he⟩ := mixed_omega_card hd inf_le_left hi₁ hiₓ
    (inf_le_inf_right _ hZE) hZ
  exact ⟨hd, hx, he, hi₁, hi₂, common_fixed_ne_bot he hi₁ hi₂⟩

omit [Finite G] in
/-- After the mixed calculation, the factor stabilizer fixes the three
order-two summands. In particular it centralizes the whole omega center. -/
theorem centralizes_of_three_fixed_lines {E Eₓ F F' U : Subgroup G}
    (hsplit : Eₓ ⊔ (F ⊔ F') = E)
    (hcₓ : Nat.card Eₓ = 2) (hc : Nat.card F = 2) (hc' : Nat.card F' = 2)
    (hnₓ : U ≤ normalizer (Eₓ : Set G))
    (hn : U ≤ normalizer (F : Set G)) (hn' : U ≤ normalizer (F' : Set G)) :
    U ≤ centralizer (E : Set G) := by
  apply le_centralizer_iff.mpr
  rw [← hsplit]
  exact sup_le (le_centralizer_iff.mp (hnₓ.trans (normalizer_le_centralizer_of_card_two _ hcₓ)))
    (sup_le (le_centralizer_iff.mp (hn.trans (normalizer_le_centralizer_of_card_two _ hc)))
      (le_centralizer_iff.mp (hn'.trans (normalizer_le_centralizer_of_card_two _ hc'))))

omit [Finite G] in
/-- The common fixed subgroup centralizes exactly the chosen factor of `X`.
Centralizing its partner as well would put it in the disjoint `X` fixed space. -/
theorem common_fixed_not_centralizes_partner {E Y₁ Y₂ Y₂' X : Subgroup G}
    (hX : Y₂ ⊔ Y₂' = X)
    (hdis : (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (X : Set G)) = ⊥)
    (hne : (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G)) ≠ ⊥) :
    ¬ (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G)) ≤
      centralizer (Y₂' : Set G) := by
  intro hc
  apply hne
  apply le_bot_iff.mp
  intro e he
  apply hdis.le
  refine ⟨he.1, he.1.1, ?_⟩
  have hBX : (E ⊓ centralizer (Y₁ : Set G)) ⊓ (E ⊓ centralizer (Y₂ : Set G)) ≤
      centralizer (X : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hX]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans inf_le_right))
      (le_centralizer_iff.mp hc)
  exact hBX he

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.MixedLocal
