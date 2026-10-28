module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.SourceApplication
public import Theory.GroupTheory.CenterlessDirectFactors
/-!
# Source factor permutation without a general Krull--Schmidt input

The actual quotient in 1.3.8 is centerless and has exactly two directly
indecomposable factors. The coordinate theorem therefore proves its factor
permutation directly, and the original quotient maps lift the conclusion.
Source: Aschbacher--Smith A.1.15 and proof of 1.3.8, printed pp.23,514.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
universe u
variable {C : Type*} [Group C]
private theorem center_bot_of_equiv {D : Type*} [Group D]
    (e : C ≃* D) (hz : center D = ⊥) : center C = ⊥ := by
  apply bot_unique
  intro x hx
  have he : e x ∈ center D := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx z]
  have he1 : e x = e 1 := (mem_bot.mp (hz ▸ he)).trans (map_one e).symm
  exact e.injective he1

/-- The exact two-factor specialization needed by the original block consumer. -/
theorem sourceA115_pair_of_centerless {D : Type*} [Group D]
    (A B : Subgroup D) (hA : DirectlyIndecomposable A) (hB : DirectlyIndecomposable B)
    (hprod : ∃ e : A × B ≃* D, ∀ a b, e (a,b) = (a : D) * (b : D))
    (hz : center D = ⊥) (α : MulAut D) :
    (A.map α.toMonoidHom = A ∨ A.map α.toMonoidHom = B) ∧
      (B.map α.toMonoidHom = A ∨ B.map α.toMonoidHom = B) := by
  obtain ⟨e,he⟩ := hprod
  let : Nontrivial A := hA.1
  let : Nontrivial B := hB.1
  have hzP := center_bot_of_equiv e hz
  have hzA : center A = ⊥ := by
    apply bot_unique
    intro a ha
    have hh : (a, (1 : B)) ∈ center (A × B) := by
      rw [Subgroup.center_prod]
      exact ⟨ha,one_mem _⟩
    exact congrArg Prod.fst (mem_bot.mp (hzP ▸ hh))
  have hzB : center B = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : ((1 : A), b) ∈ center (A × B) := by
      rw [Subgroup.center_prod]
      exact ⟨one_mem _,hb⟩
    exact congrArg Prod.snd (mem_bot.mp (hzP ▸ hh))
  let γ : MulAut (A × B) := e.trans (α.trans e.symm)
  have hp := Theory.GroupTheory.CenterlessDirectFactors.coordinate_factors hA.2 hB.2 hzA hzB γ
  have hEA : (e.toMonoidHom.comp (MonoidHom.inl A B)).range = A := by
    have hh : e.toMonoidHom.comp (MonoidHom.inl A B) = A.subtype := by
      ext a
      change e (a,1) = (a : D)
      simpa using he a 1
    rw [hh]
    exact A.range_subtype
  have hEB : (e.toMonoidHom.comp (MonoidHom.inr A B)).range = B := by
    have hh : e.toMonoidHom.comp (MonoidHom.inr A B) = B.subtype := by
      ext b
      change e (1,b) = (b : D)
      simpa using he 1 b
    rw [hh]
    exact B.range_subtype
  have hmA : ((MonoidHom.inl A B).range).map e.toMonoidHom = A := by
    rw [← MonoidHom.range_comp]
    exact hEA
  have hmB : ((MonoidHom.inr A B).range).map e.toMonoidHom = B := by
    rw [← MonoidHom.range_comp]
    exact hEB
  have hGA : ((γ.toMonoidHom.comp (MonoidHom.inl A B)).range).map e.toMonoidHom =
      A.map α.toMonoidHom := by
    rw [← MonoidHom.range_comp]
    have hh : e.toMonoidHom.comp (γ.toMonoidHom.comp (MonoidHom.inl A B)) =
        α.toMonoidHom.comp (e.toMonoidHom.comp (MonoidHom.inl A B)) := by
      ext a
      change e (γ (a,1)) = α (e (a,1))
      exact e.apply_symm_apply _
    rw [hh,MonoidHom.range_comp,hEA]
  have hGB : ((γ.toMonoidHom.comp (MonoidHom.inr A B)).range).map e.toMonoidHom =
      B.map α.toMonoidHom := by
    rw [← MonoidHom.range_comp]
    have hh : e.toMonoidHom.comp (γ.toMonoidHom.comp (MonoidHom.inr A B)) =
        α.toMonoidHom.comp (e.toMonoidHom.comp (MonoidHom.inr A B)) := by
      ext b
      change e (γ (1,b)) = α (e (1,b))
      exact e.apply_symm_apply _
    rw [hh,MonoidHom.range_comp,hEB]
  rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨Or.inl (hGA.symm.trans ((congrArg (fun U => U.map e.toMonoidHom) ha).trans hmA)),
      Or.inr (hGB.symm.trans ((congrArg (fun U => U.map e.toMonoidHom) hb).trans hmB))⟩
  · exact ⟨Or.inr (hGA.symm.trans ((congrArg (fun U => U.map e.toMonoidHom) ha).trans hmB)),
      Or.inl (hGB.symm.trans ((congrArg (fun U => U.map e.toMonoidHom) hb).trans hmA))⟩



variable {G : Type u} [Group G]
private theorem lift_centerFactor_eq {X W V : Subgroup G}
    (hWX : W ≤ X) (hVX : V ≤ X) (d : normalizer (X : Set G))
    (he : (centerFactor X W).map
      (quotientAut (center X) (X.normalizerMonoidHom d)).toMonoidHom = centerFactor X V) :
    (W ⊔ (center X).map X.subtype).conjBy (d : G) = V ⊔ (center X).map X.subtype := by
  have hh := congrArg (fun F : Subgroup (X ⧸ center X) =>
    (F.comap (QuotientGroup.mk' (center X))).map X.subtype) he
  rw [preimage_map_quotient_conj, centerFactor_preimage hWX, centerFactor_preimage hVX] at hh
  exact hh

/-- Applying the centerless two-factor theorem to the actual multiplication isomorphism and pulling
back both quotient factors. Indecomposability is still an explicit premise. -/
theorem centerFactor_pair_of_centerless [Finite G]
    {X W V : Subgroup G} (hgen : W ⊔ V = X) (hcomm : ⁅W, V⁆ = ⊥)
    (hW : DirectlyIndecomposable (centerFactor X W))
    (hV : DirectlyIndecomposable (centerFactor X V))
    (hz : center (X ⧸ center X) = ⊥) :
    ∀ d ∈ normalizer (X : Set G),
      ((W ⊔ (center X).map X.subtype).conjBy d = W ⊔ (center X).map X.subtype ∨
        (W ⊔ (center X).map X.subtype).conjBy d = V ⊔ (center X).map X.subtype) ∧
      ((V ⊔ (center X).map X.subtype).conjBy d = W ⊔ (center X).map X.subtype ∨
        (V ⊔ (center X).map X.subtype).conjBy d = V ⊔ (center X).map X.subtype) := by
  have hWX : W ≤ X := le_sup_left.trans_eq hgen
  have hVX : V ≤ X := le_sup_right.trans_eq hgen
  intro d hd
  have hp := sourceA115_pair_of_centerless (centerFactor X W) (centerFactor X V) hW hV
    (centerFactor_product hgen hcomm) hz
    (quotientAut (center X) (X.normalizerMonoidHom ⟨d, hd⟩))
  constructor
  · exact hp.1.imp (lift_centerFactor_eq hWX hWX ⟨d, hd⟩)
      (lift_centerFactor_eq hWX hVX ⟨d, hd⟩)
  · exact hp.2.imp (lift_centerFactor_eq hVX hWX ⟨d, hd⟩)
      (lift_centerFactor_eq hVX hVX ⟨d, hd⟩)

end CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
