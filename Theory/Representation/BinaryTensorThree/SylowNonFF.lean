module
public import Theory.Representation.BinaryTensorThree.SylowCertificates
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Obstruction

/-!
# Non-FF for the binary three-by-three tensor Sylow action

Quadratic elementary subgroups form cliques in the checked compatibility
graph and therefore have order at most four. Each nonidentity involution
moves at least three dimensions. Thompson replacement then contradicts
any FF-offender inequality. The companion source adapter transports this
result through coordinates on the actual Sylow automizer of the full module.

Source: Aschbacher--Smith H.4.10--11 and B.1.4, printed pp.384,68--69.
-/

public section
namespace BinaryTensorThree.Small
open Representation.BinaryOffender
open scoped IsMulCommutative

private theorem quadratic_adjacent {A : Subgroup P} (hq : IsQuadratic actionSmall A)
    {v w : Fin 44} (hv : vertex v ∈ A) (hw : vertex w ∈ A) : adjacent v w=true := by
  rcases rejection_check v w with h|h
  · exact h
  · exfalso
    dsimp only at h
    let a := if (witness v w).2.2 then w else v
    let b := if (witness v w).2.2 then v else w
    have ha : vertex a ∈ A := by dsimp [a]; split <;> assumption
    have hb : vertex b ∈ A := by dsimp [b]; split <;> assumption
    have hz : displacement a (displacement b (unit (witness v w).1)) = 0 := by
      simp only [displacement,act_eq]
      exact sub_eq_zero.mpr (hq _ ha _ hb _)
    exact h (congrFun (congrFun hz _) _)

/-- Every quadratic elementary subgroup of the actual binary tensor Sylow action has order at most four. -/
theorem quadratic_card_le_four (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hq : IsQuadratic actionSmall A) : Nat.card A ≤ 4 := by
  classical
  let s : Finset (Fin 44) := Finset.univ.filter (fun v => vertex v ∈ A)
  have hs : s.card ≤ 4 :=
    MathieuCode.QuadraticActors.clique_card_le_four 0 adjacent neighbors_check s (by
      intro v hv w hw
      exact quadratic_adjacent hq (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2)
  let f : s → A := fun v => ⟨vertex v.val,(Finset.mem_filter.mp v.property).2⟩
  have hf : Function.Surjective f := by
    intro a
    have ha : a.val*a.val=1 := by
      simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a.val a.property
    obtain ⟨v,hv⟩ := vertex_cover a.val ha
    exact ⟨⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv.symm ▸ a.property⟩⟩,Subtype.ext hv⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (by simpa using hs)

/-- Every nonidentity involution in the literal Sylow action has displacement rank at least three. -/
theorem involution_fixedCodim (g : P) (hg : orderOf g=2) :
    2 < fixedCodim actionSmall (Subgroup.zpowers g) := by
  have hsq : g*g=1 := by simpa only [pow_two, hg] using pow_orderOf_eq_one g
  obtain ⟨v,rfl⟩ := vertex_cover g hsq
  have hv : v≠0 := by
    intro h
    subst v
    rw [vertex_zero,orderOf_one] at hg
    omega
  let δ := actionSmall (vertex v) - LinearMap.id
  let f := δ.comp (probe v)
  have hf : Function.Injective f := by
    rw [←LinearMap.ker_eq_bot]
    apply bot_unique
    intro c hc
    change action (toTensor (vertex v)) (probe v c) - probe v c=0 at hc
    rw [←act_eq] at hc
    exact rank_check v hv c hc
  have hle : f.range ≤ δ.range := by
    rintro _ ⟨c,rfl⟩
    exact ⟨probe v c,rfl⟩
  have hm := Submodule.finrank_mono hle
  change Module.finrank (ZMod 2) f.range ≤ _ at hm
  rw [LinearMap.finrank_range_of_inj hf] at hm
  have hn : Module.finrank (ZMod 2) Natural = 3 := by simp
  rw [hn] at hm
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact hm

/-- Thompson replacement and the checked quadratic bounds rule out every FF-offender. -/
theorem notFF : ¬ IsFFModule actionSmall :=
  not_isFFModule_of_quadratic_card_le_four actionSmall
    (fun A hA hq => @quadratic_card_le_four A hA hq) involution_fixedCodim

end BinaryTensorThree.Small
