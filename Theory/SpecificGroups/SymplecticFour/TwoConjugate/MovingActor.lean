module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Geometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CenterAction

@[expose] public section
noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.ExceptionalGraph
open EvenBorelTorus EvenBorelTorus.ActorReduction CentralRootGeometry
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

private theorem upper_injective {s t u v : F} (he : upper s t = upper u v) :
    s=u ∧ t=v := by
  have hh : parameter (Multiplicative.ofAdd s,Multiplicative.ofAdd t) =
      parameter (Multiplicative.ofAdd u,Multiplicative.ofAdd v) := by
    simpa only [parameter_apply,toAdd_ofAdd,upper] using he
  have h := parameter_injective hh
  exact ⟨congrArg (fun x : Multiplicative F × Multiplicative F => x.1.toAdd) h,
    congrArg (fun x : Multiplicative F × Multiplicative F => x.2.toAdd) h⟩

private theorem field_upper (σ : F ≃+* F) (s t : F) :
    fieldAutomorphism σ (upper s t) = upper (σ s) (σ t) := by
  simp only [upper,map_mul,fieldAutomorphism_root]

private theorem graph_upper (s t : F) : graphAut (upper s t) = upper (t^2) s := by
  have hc := (Commute.all
    (Multiplicative.ofAdd (0:F),Multiplicative.ofAdd s)
    (Multiplicative.ofAdd (t^2),Multiplicative.ofAdd (0:F))).map (parameter (F := F))
  simp only [parameter_apply,toAdd_ofAdd,RootSubgroup.element_zero,
    one_mul,mul_one] at hc
  simpa [upper,graphAut_apply,graphEnd_root,rootPermutation,rootParameter] using hc.eq

/-- A genuine diagram-moving Sylow stabilizer has the exceptional semilinear
coordinate action, with both scalar coefficients nonzero. -/
theorem moving_actor_coordinates (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬ PreservesDiagram a.val) :
    ∃ (σ : F ≃+* F) (c d : F), c≠0 ∧ d≠0 ∧ ∀s t:F,
      a.val (upper s t) = upper (c*(σ t)^2) (d*σ s) := by
  obtain ⟨g,k,hk⟩ := exists_inner_graph_power hq
    SemilinearClassification.inner_field_of_preservesDiagram a
  have he : a.val = MulAut.conj g.val * graphAut ^ k := congrArg Subtype.val hk
  have ho : Odd k := by
    rcases Nat.even_or_odd k with h | h
    · obtain ⟨m,rfl⟩ := even_iff_two_dvd.mp h
      apply False.elim
      apply ha
      rw [he,pow_mul,graphAut_square]
      have hi : MulAut.conj g.val ∈ (parabolicClassAction hq).ker :=
        (mem_parabolicClassAction_ker_iff hq _).mpr (inner_preservesDiagram _)
      have hf : fieldAutomorphism (frobeniusEquiv F 2) ∈ (parabolicClassAction hq).ker :=
        (mem_parabolicClassAction_ker_iff hq _).mpr (field_preservesDiagram _)
      exact (mem_parabolicClassAction_ker_iff hq _).mp
        ((parabolicClassAction hq).ker.mul_mem hi ((parabolicClassAction hq).ker.pow_mem hf m))
    · exact h
  obtain ⟨m,rfl⟩ := ho
  refine ⟨frobeniusEquiv F 2 ^ m,((borelCharacters g).1:F)^2,
    ((borelCharacters g).2:F),pow_ne_zero _ (Units.ne_zero _),Units.ne_zero _,?_⟩
  intro s t
  have hp : graphAut (F := F) ^ (2*m+1) =
      fieldAutomorphism (frobeniusEquiv F 2 ^ m) * graphAut := by
    rw [pow_add,pow_mul,graphAut_square,pow_one]
    exact congrArg (· * graphAut) (fieldAutomorphismHom.map_pow _ _).symm
  rw [he,hp,MulAut.mul_apply,MulAut.mul_apply,graph_upper,field_upper,map_pow]
  simpa only [parameter_apply,toAdd_ofAdd,upper,MulAut.conj_apply] using
    CenterAction.borel_conj_parameter g
      (((frobeniusEquiv F 2)^m) t ^ 2) (((frobeniusEquiv F 2)^m) s)

/-- A subgroup of a diagonal root line stabilized by a diagram-moving actor
has at most two elements. This uses setwise stability, not pointwise fixation. -/
theorem diagonal_card_le_two (a : MulAut (Sp F))
    (σ : F ≃+* F) (c d : F) (hc : c≠0) (_hd : d≠0)
    (hcoord : ∀s t:F,a (upper s t) = upper (c*(σ t)^2) (d*σ s))
    (V : Subgroup (Sp F)) (hV : V.map a.toMonoidHom = V)
    (μ : F) (hμ : μ≠0) (hline : V ≤ diagonal μ) : Nat.card V ≤ 2 := by
  classical
  have rel (x:F) (hx:upper x (x*μ) ∈ V) :
      d*σ x = (c*(σ x * σ μ)^2)*μ := by
    have hm : a (upper x (x*μ)) ∈ V := hV.le (mem_map_of_mem a.toMonoidHom hx)
    obtain ⟨y,hy⟩ := (mem_diagonal_iff μ _).mp (hline hm)
    rw [hcoord,map_mul] at hy
    obtain ⟨he,hf⟩ := upper_injective hy
    rw [he] at hf
    exact hf.symm
  have unique (x y:F) (hx:upper x (x*μ)∈V) (hy:upper y (y*μ)∈V)
      (hx0:x≠0) (hy0:y≠0) : x=y := by
    let C : F := c*(σ μ)^2*μ
    have hC : C≠0 := mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ ((map_ne_zero σ).mpr hμ))) hμ
    have hdx : d=C*σ x := by
      apply (mul_left_inj' ((map_ne_zero σ).mpr hx0)).mp
      have h := rel x hx
      dsimp [C]
      linear_combination h
    have hdy : d=C*σ y := by
      apply (mul_left_inj' ((map_ne_zero σ).mpr hy0)).mp
      have h := rel y hy
      dsimp [C]
      linear_combination h
    exact σ.injective (mul_left_cancel₀ hC (hdx.symm.trans hdy))
  let f : V → Bool := fun x => decide (x=1)
  have hf : Function.Injective f := by
    intro x y he
    by_cases hx:x=1
    · have hy:y=1 := by simpa [f,hx] using he.symm
      exact hx.trans hy.symm
    · have hy:y≠1 := by simpa [f,hx] using he
      obtain ⟨s,hs⟩ := (mem_diagonal_iff μ _).mp (hline x.property)
      obtain ⟨t,ht⟩ := (mem_diagonal_iff μ _).mp (hline y.property)
      have hs0:s≠0 := by
        intro hh
        apply hx
        apply Subtype.ext
        rw [←hs,hh]
        simp [upper,RootSubgroup.element_zero]
      have ht0:t≠0 := by
        intro hh
        apply hy
        apply Subtype.ext
        rw [←ht,hh]
        simp [upper,RootSubgroup.element_zero]
      have heq := unique s t (hs.symm ▸ x.property) (ht.symm ▸ y.property) hs0 ht0
      apply Subtype.ext
      exact hs.symm.trans ((congrArg (fun z:F => upper z (z*μ)) heq).trans ht)
  simpa using Nat.card_le_card_of_injective f hf

/-- Noncyclic source V cannot lie on a diagonal root line. -/
theorem not_diagonal_of_moving_actor (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬ PreservesDiagram a.val)
    (V : Subgroup (Sp F)) (hV : V.map a.val.toMonoidHom = V)
    (hr : 2 < Nat.card V) (μ : F) (hμ : μ≠0) : ¬V ≤ diagonal μ := by
  obtain ⟨σ,c,d,hc,hd,hcoord⟩ := moving_actor_coordinates hq a ha
  exact fun hline => (not_le_of_gt hr) (diagonal_card_le_two a.val σ c d hc hd hcoord V hV μ hμ hline)

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
