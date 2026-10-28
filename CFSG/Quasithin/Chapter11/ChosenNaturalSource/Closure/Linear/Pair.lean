module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Core
public import Theory.Frattini.Intersection
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Lemmas

/-!
# The opposite pair and the Cartan commutator

The Frattini subgroup of Uˣ∩Uʸ lies in the disjoint points V₁ˣ and V₁ʸ.
Coprime commutator idempotence therefore makes [Uˣ∩Uʸ,X] eligible for
11.5.6(4). The remaining triple intersection is already in O₂(G₁), so
the entire opposite pair centralizes Y/O₂(Y). Applying the core argument
then removes its opposite-pair action premise.

Only the three layer-generation identities and frame normalization remain
to be obtained from the natural and dual layer calculations. The Cartan
action and core inputs are the explicit outputs of the independent
11.5.4--6 producer.
Source: Aschbacher--Smith, 11.5.7, printed pp.781--782.
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) {x y : G}
  (d : ChapterG.Section02.LinearThree.Hypothesis (setup E)
    E.input.field.Carrier E.input.field.degree x y)

include d in
theorem oppositePair_frattini (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁) :
    frattini (oppositePair E x y) = ⊥ := by
  have hp := d.U_isPGroup hUT
  have hmap (a : G) :
      (frattini (ChapterG.Section02.Setup.conjugate E.W a)).map
        (ChapterG.Section02.Setup.conjugate E.W a).subtype ≤
          ChapterG.Section02.Setup.conjugate E.V₁ a := by
    rw [ChapterG.Section02.Setup.conjugate,
      frattini_image_map E.W _ (MulAut.conj a⁻¹).injective]
    exact map_mono hf
  apply frattini_eq_bot_of_disjoint_images
    (hp.map (MulAut.conj x⁻¹).toMonoidHom)
    (hp.map (MulAut.conj y⁻¹).toMonoidHom) inf_le_left inf_le_right
  exact (d.third_disjoint.mono_left le_sup_right).mono (hmap x) (hmap y)

private theorem coprime_commutator_idempotent (A B : Subgroup G)
    (hBA : B ≤ normalizer (A : Set G)) (hsolv : Group.IsSolvable A)
    (hcop : Nat.Coprime (Nat.card B) (Nat.card A)) : ⁅A,B⁆ = ⁅⁅A,B⁆,B⁆ := by
  let _ : Normalizes B A := ⟨hBA⟩
  have hm := commutatorAction_subgroup_conj_map_eq_commutator A B hBA
  apply le_antisymm
  · calc
      ⁅A,B⁆ = (commutatorAction₂ (A := B) (G := A)).map A.subtype := by
        rw [commutatorAction₂_eq_commutatorAction_of_solvable_coprime hsolv hcop, hm]
      _ ≤ ⁅⁅A,B⁆,B⁆ := ?_
    rw [commutatorAction₂, commutatorSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨v, ⟨b, a, ha, rfl⟩, rfl⟩
    have ham : (a : G) ∈ ⁅A,B⁆ := by
      rw [← hm]
      exact mem_map_of_mem _ ha
    change (a : G)⁻¹ * ((b : G) * (a : G) * (b : G)⁻¹) ∈ ⁅⁅A,B⁆,B⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      commutator_mem_commutator ((⁅A,B⁆).inv_mem ham) b.property
  · exact le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right A B)

/-- Restricting a core commutator to Y lands in its own core, not just O₂(G₁). -/
theorem commutator_point_core_Y_le : ⁅E.G₁.pCoreIn 2,E.Y⁆ ≤ E.Y.pCoreIn 2 := by
  have hGQ : E.G₁ ≤ normalizer (E.G₁.pCoreIn 2 : Set G) :=
    E.G₁.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image E.G₁ (pCore 2 E.G₁))
  exact (le_inf
    (le_normalizer_iff_commutator_le_right.mp
      ((pCoreIn_le 2 E.G₁).trans (G₁_normalizes_Y E)))
    (le_normalizer_iff_commutator_le_left.mp (E.Y_le_G₁.trans hGQ))).trans
      (inf_pCoreIn_le_of_le 2 E.Y_le_G₁)

include d in
/-- Apply 11.5.6(4) to the fully moved subgroup of the original opposite pair. -/
theorem oppositePair_centralizes_Y
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hpairT : oppositePair E x y ≤ (T : Subgroup G))
    (hTG : (T : Subgroup G) ≤ E.G₁)
    (hXP : E.X ≤ normalizer (oppositePair E x y : Set G))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card (oppositePair E x y)))
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hEX : oppositePair E x y ≤ ⁅oppositePair E x y,E.X⁆ ⊔ triple E x y)
    (hcartan : ∀ P : Subgroup G, P ≤ (T : Subgroup G) → P = ⁅P,E.X⁆ →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2) :
    ⁅oppositePair E x y,E.Y⁆ ≤ E.Y.pCoreIn 2 := by
  let A := oppositePair E x y
  have hp : IsPGroup 2 A := T.isPGroup'.to_le hpairT
  have hPA : ⁅A,E.X⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hXP
  have hpf : (frattini (⁅A,E.X⁆ : Subgroup G)).map (⁅A,E.X⁆).subtype ≤ E.G₁.pCoreIn 2 := by
    apply (frattini_image_le_of_le hPA hp).trans
    rw [oppositePair_frattini E d hUT hf, Subgroup.map_bot]
    exact bot_le
  have hPY := hcartan ⁅A,E.X⁆ (hPA.trans hpairT)
    (coprime_commutator_idempotent A E.X hXP
      (@IsNilpotent.to_isSolvable _ _ hp.isNilpotent) hcop) hpf
  have htriple : triple E x y ≤ E.G₁.pCoreIn 2 :=
    (triple_le_closure E x y).trans hUQ
  have hnorm : E.G₁ ≤ normalizer (E.Y.pCoreIn 2 : Set G) :=
    (G₁_normalizes_Y E).trans
      (normalizer_le_normalizer_characteristic_image E.Y (pCore 2 E.Y))
  exact (commutator_mono hEX le_rfl).trans
    (commutator_sup_le_of_relative_normal E.G₁ ⁅A,E.X⁆ (triple E x y) E.Y
      (E.Y.pCoreIn 2) hnorm (hPA.trans (hpairT.trans hTG))
      (htriple.trans (pCoreIn_le 2 E.G₁)) hPY
      ((commutator_mono htriple le_rfl).trans (commutator_point_core_Y_le E)))

include d in
/-- The original source core argument with the opposite-pair action proved.
The layer-generation inputs are separate from all preceding Chapter 11 inputs. -/
theorem threeCore_le_point_core_of_cartan
    (hUT : E.W ≤ (T : Subgroup G))
    (hf : (frattini E.W).map E.W.subtype ≤ E.V₁)
    (hTG : (T : Subgroup G) ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (hUQ : E.W ≤ E.G₁.pCoreIn 2)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hSL : threeCore E x y = ⁅threeCore E x y,E.L₁⁆ ⊔ oppositePair E x y)
    (hSX : threeCore E x y ≤ ⁅threeCore E x y,E.X⁆ ⊔
      (threeCore E x y ⊓ E.W))
    (hEX : oppositePair E x y ≤ ⁅oppositePair E x y,E.X⁆ ⊔ triple E x y)
    (hXP : E.X ≤ normalizer (oppositePair E x y : Set G))
    (hcop : Nat.Coprime (Nat.card E.X) (Nat.card (oppositePair E x y)))
    (hcartan : ∀ P : Subgroup G, P ≤ (T : Subgroup G) → P = ⁅P,E.X⁆ →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hcoreX : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    threeCore E x y ≤ E.G₁.pCoreIn 2 := by
  have hpair : oppositePair E x y ≤ threeCore E x y :=
    (le_sup_right : oppositePair E x y ≤
      ⁅threeCore E x y,E.L₁⁆ ⊔ oppositePair E x y).trans hSL.ge
  have hpairT : oppositePair E x y ≤ (T : Subgroup G) :=
    hpair.trans ((threeCore_le_LT_core d hUT hf).trans (d.LT_core_le_T))
  exact threeCore_le_point_core E d hUT hf hTG hXG hUQ hgen hSL hSX
    (oppositePair_centralizes_Y E d hUT hf hpairT hTG hXP hcop hUQ hEX hcartan) hcoreX

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear
