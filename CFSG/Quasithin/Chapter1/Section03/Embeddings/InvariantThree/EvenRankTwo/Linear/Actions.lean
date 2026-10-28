module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Actions.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.NormalizerForm
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Actions.Inputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Linear.Actions.Alignment
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# The ternary PSL₃ pair action after simultaneous alignment

For a subgroup of the diagonal torus, the standard normalizer calculation
eliminates the GL₃ factor. Finite-field automorphisms act by powers, and an
actor with a graph factor proves stability under the Weyl-adjusted graph
before that involution is restricted and descended to the Frattini quotient.
The actual central model map then transports this calculation to Q.

The final theorem instantiates the proved matrix compatibility and simultaneous
Borel alignment. The recognized field has order 2^f, so intrinsic binary
coverage supplies the standard normal form, including when f = 2. Thus the
action calculation has only the stated placement, commutativity and central
disjointness hypotheses, with no additional model or coverage premise.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528 of
`refs/quasithin.pdf`), and the preceding A.3.15(5) Cartan argument.
-/

public section

open scoped MatrixGroups
open Subgroup Theory.GroupTheory
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
universe u

/-- The compatibility input follows from the actual linear, field and
inverse-transpose actions over every field. -/
theorem standardCompatibility (E : Type*) [Field E] : StandardCompatibility E :=
  ⟨Matrix.PSL3.OuterSolvable.field_linearConj,
    Matrix.PSL3.OuterSolvable.graph_linearConj_exists,
    Matrix.PSL3.OuterSolvable.field_commute_graph⟩

private theorem map_eq_of_preserves {G : Type*} [Group G]
    (B : Subgroup G) (a : MulAut G) (ha : ∀ x, a x ∈ B ↔ x ∈ B) :
    B.map a.toMonoidHom = B := by
  apply le_antisymm
  · rintro _ ⟨b,hb,rfl⟩
    exact (ha b).mpr hb
  · intro b hb
    refine ⟨a.symm b, (ha _).mp ?_, a.apply_symm_apply b⟩
    simpa only [a.apply_symm_apply] using hb

variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- For an aligned pair, the actual standard normal form and Borel kernel
construct the graph involution on the Frattini quotient. -/
theorem power_involution_of_aligned_pair
    (hlaws : StandardCompatibility F) (hcover : standard F = ⊤)
    (B : Subgroup PSL(3,F)) (hB : B ≤ torus F)
    (D : Subgroup (MulAut B)) (hD : D ≤ pairAutomizer (unipotent F) B) :
    ∃ g : MulAut (B ⧸ frattini B), g ^ 2 = 1 ∧
      ∀ a ∈ D, ∀ v, quotientAut (frattini B) a v ∈ zpowers v ∨
        quotientAut (frattini B) a v ∈ zpowers (g v) := by
  obtain ⟨g,hg,ha⟩ := InvariantLarge.EvenActions.Linear.frattini_of_torus_action
    F B hB D.subtype (by
      intro a
      obtain ⟨β,hβ⟩ := pairRestriction_surjective (unipotent F) B ⟨a.val,hD a.property⟩
      obtain ⟨σ,hσ⟩ := InvariantLarge.EvenActions.Linear.standard_normalizer_action
        F hlaws.1 hlaws.2.1 hlaws.2.2 B hB β.val (by rw [hcover]; trivial)
        (map_eq_of_preserves _ _ β.property.1)
        (map_eq_of_preserves _ _ β.property.2)
      have he (b : B) : (a.val b : PSL(3,F)) = β.val b :=
        (congrArg (fun c : pairAutomizer (unipotent F) B => (c.val b : PSL(3,F))) hβ).symm
      refine ⟨σ, ?_⟩
      rcases hσ with hσ | hσ
      · exact Or.inl (fun b => (he b).trans (hσ b b.property))
      · exact Or.inr (fun b => (he b).trans (hσ b b.property)))
  exact ⟨g,hg,fun a had v => ha ⟨a,had⟩ v⟩

/-- Pull the aligned calculation back to a central cover using the same
projection for the pair, its automorphisms and its Frattini quotient. -/
theorem power_involution_of_aligned_central_model
    (hlaws : StandardCompatibility F) (hcover : standard F = ⊤)
    {Q : Type u} [Group Q] [Finite Q]
    (e : (Q ⧸ center Q) ≃* PSL(3,F)) (S : Sylow 2 Q) (R : Subgroup Q)
    (hd : Disjoint R (center Q))
    (hS : (S : Subgroup Q).map (centralModelMap e) = unipotent F)
    (hR : R.map (centralModelMap e) ≤ torus F)
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer (S : Subgroup Q) R) :
    ∃ g : MulAut (R ⧸ frattini R), g ^ 2 = 1 ∧
      ∀ a ∈ D, ∀ v, quotientAut (frattini R) a v ∈ zpowers v ∨
        quotientAut (frattini R) a v ∈ zpowers (g v) := by
  apply power_involution_of_equiv (centralImageEquiv e R hd) D
  apply power_involution_of_aligned_pair F hlaws hcover _ hR
  rintro _ ⟨a,ha,rfl⟩
  rw [← hS]
  exact centralImage_pairAutomizer e (S : Subgroup Q) R hd (hD ha)

/-- Reusable conditional assembly of the ternary central-cover action.
This interface retains its original model inputs and universal coverage
hypothesis. The theorem `pair_power_involution` below discharges the model
inputs and uses intrinsic coverage at the recognized binary field. -/
theorem pair_power_involution_of_model_inputs
    (halign : ∀ (E : Type) [Field E] [Finite E] [CharP E 2], BorelThreeAlignment E)
    (hlaws : ∀ (E : Type) [Field E] [Finite E] [CharP E 2], StandardCompatibility E)
    (hcover : ∀ (E : Type) [Field E] [Finite E] [CharP E 2],
      IsSimpleGroup PSL(3,E) → (¬ Group.IsSolvable PSL(3,E)) → standard E = ⊤)
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ f))
    (hn : R ≤ normalizer (S : Subgroup Q)) (hcomm : IsMulCommutative R)
    (hd : Disjoint R (center Q))
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer (S : Subgroup Q) R) :
    ∃ g : MulAut (R ⧸ frattini R), g ^ 2 = 1 ∧
      ∀ a ∈ D, ∀ v, quotientAut (frattini R) a v ∈ zpowers v ∨
        quotientAut (frattini R) a v ∈ zpowers (g v) := by
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := hmodel
  let _ := Fintype.ofFinite E
  have hc : ringChar E = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hE]
    simp [Nat.pow_mod, show f ≠ 0 by omega])
  let _ : CharP E 2 := ringChar.of_eq hc
  let _ := h.quasisimple
  let _ : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  have hs : IsSimpleGroup PSL(3,E) := (MulEquiv.isSimpleGroup_congr e).mp inferInstance
  let _ := hs
  let _ : Group.IsPerfect PSL(3,E) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hstd : standard E = ⊤ := hcover E hs (Group.IsPerfect.not_isSolvable _)
  have hcomm' : IsMulCommutative (R.map (centralModelMap e)) := by
    apply isMulCommutative_iff.mpr
    rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩
    apply Subtype.ext
    change centralModelMap e x * centralModelMap e y =
      centralModelMap e y * centralModelMap e x
    rw [← map_mul, ← map_mul]
    exact congrArg (centralModelMap e) (congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x,hx⟩ : R) (⟨y,hy⟩ : R)))
  obtain ⟨a,haS,haR⟩ := halign E f hf hE (centralImageSylow e S)
    (R.map (centralModelMap e)) (h.oddComplement.isPGroup.map _) hcomm'
    (centralImage_normalizes e S R hn)
  apply power_involution_of_aligned_central_model E (hlaws E) hstd (e.trans a) S R hd
    ?_ ?_ D hD
  · change (S : Subgroup Q).map (a.toMonoidHom.comp (centralModelMap e)) = _
    rw [← Subgroup.map_map]
    exact haS
  · change R.map (a.toMonoidHom.comp (centralModelMap e)) ≤ _
    rw [← Subgroup.map_map]
    exact haR

/-- The ternary PSL₃ action calculation after Borel placement. The actual
central quotient, simultaneous alignment, matrix compatibility and intrinsic
binary coverage construct one involution controlling every actor in D.
No coverage or further model hypothesis remains. -/
theorem pair_power_involution
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ f))
    (hn : R ≤ normalizer (S : Subgroup Q)) (hcomm : IsMulCommutative R)
    (hd : Disjoint R (center Q))
    (D : Subgroup (MulAut R)) (hD : D ≤ pairAutomizer (S : Subgroup Q) R)
    (_h2 : IsPGroup 2 D) :
    ∃ g : MulAut (R ⧸ frattini R), g ^ 2 = 1 ∧
      ∀ a ∈ D, ∀ v, quotientAut (frattini R) a v ∈ zpowers v ∨
        quotientAut (frattini R) a v ∈ zpowers (g v) := by
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := hmodel
  let _ := Fintype.ofFinite E
  have hc : ringChar E = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hE]
    simp [Nat.pow_mod, show f ≠ 0 by omega])
  let _ : CharP E 2 := ringChar.of_eq hc
  have hstd : standard E = ⊤ := standard_eq_top_of_two_power_card E (by omega) hE
  have hcomm' : IsMulCommutative (R.map (centralModelMap e)) := by
    apply isMulCommutative_iff.mpr
    rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩
    apply Subtype.ext
    change centralModelMap e x * centralModelMap e y =
      centralModelMap e y * centralModelMap e x
    rw [← map_mul, ← map_mul]
    exact congrArg (centralModelMap e) (congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x,hx⟩ : R) (⟨y,hy⟩ : R)))
  obtain ⟨a,haS,haR⟩ := borelThreeAlignment E f hf hE (centralImageSylow e S)
    (R.map (centralModelMap e)) (h.oddComplement.isPGroup.map _) hcomm'
    (centralImage_normalizes e S R hn)
  apply power_involution_of_aligned_central_model E (standardCompatibility E) hstd
    (e.trans a) S R hd ?_ ?_ D hD
  · change (S : Subgroup Q).map (a.toMonoidHom.comp (centralModelMap e)) = _
    rw [← Subgroup.map_map]
    exact haS
  · change R.map (a.toMonoidHom.comp (centralModelMap e)) ≤ _
    rw [← Subgroup.map_map]
    exact haR

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear.Actions
