module

public import Stellmacher.PushingUp.CriticalCommutatorNoncentral

/-!
# Vanishing of a bicentral closure commutator

Let `(a,a′)` and `(u,c)` be positive-distance critical pairs. Suppose the
2-core of `G_a` lies in `G_u` and `Z_u` lies in `G_a`. Let `V` be the normal
closure of `Z_u` in `G_a`, joined with `Z_a`, and let `U ≤ Q_a` be a 2-group.
If `[V,U]` is central in both vertex stabilizers, then it is trivial.
This is the first case of step (2) in the proof of Stellmacher, *Pushing up*
(1986), (2.4), where the source has `Z_y ≤ Q_a`.

Write `R = [V,U]`. For each `g ∈ G_a`, conjugating a commutator with `Z_u`
shows `[Z_u,U^g] ≤ R`, because the normal closure contains the conjugates of
`Z_u` and `g` centralizes `R`. Since `U^g ≤ Q_a ≤ G_u`, the natural-module
noncentrality theorem at `u` forces `U^g ≤ Q_u`. The core-center containment
then makes `U^g` centralize `Z_u`. Reversing conjugation shows that every
normal-closure generator centralizes `U`; `Z_a` also centralizes `U ≤ Q_a`.
No normality hypothesis on `U` is used.
-/

open scoped commutatorElement

namespace Stellmacher.PushingUp

open AmalgamGraph

universe u

variable {M : Type u} [Group M] [Finite M]

private theorem mem_center_map_commute {G : Type*} [Group G]
    (A : Subgroup G) {r g : G}
    (hr : r ∈ (Subgroup.center A).map A.subtype) (hg : g ∈ A) :
    g * r = r * g := by
  obtain ⟨rA, hrA, rfl⟩ := hr
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hrA) ⟨g, hg⟩)

/-- The closure commutator vanishes when it is central at both critical vertices. -/
public theorem criticalClosure_commutator_eq_bot_of_bicentral
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' u c : Vertex S)
    (hcritA : IsCriticalPair S a a') (hcritU : IsCriticalPair S u c)
    (hb : 0 < criticalDistance S)
    (hQaGu : vertexTwoCore S a ≤ stabilizer S u)
    (hZuGa : vertexZ S u ≤ stabilizer S a)
    (U : Subgroup (FreeAmalgam S)) (hU : U ≤ vertexTwoCore S a)
    (hUtwo : IsPGroup 2 U)
    (hcentA :
      ⁅(Subgroup.normalClosure ((vertexZ S u).subgroupOf (stabilizer S a) :
        Set (stabilizer S a))).map (stabilizer S a).subtype ⊔ vertexZ S a, U⁆ ≤
        (Subgroup.center (stabilizer S a)).map (stabilizer S a).subtype)
    (hcentU :
      ⁅(Subgroup.normalClosure ((vertexZ S u).subgroupOf (stabilizer S a) :
        Set (stabilizer S a))).map (stabilizer S a).subtype ⊔ vertexZ S a, U⁆ ≤
        (Subgroup.center (stabilizer S u)).map (stabilizer S u).subtype) :
    ⁅(Subgroup.normalClosure ((vertexZ S u).subgroupOf (stabilizer S a) :
      Set (stabilizer S a))).map (stabilizer S a).subtype ⊔ vertexZ S a, U⁆ = ⊥ := by
  let N : Subgroup (stabilizer S a) := Subgroup.normalClosure
    ((vertexZ S u).subgroupOf (stabilizer S a) : Set (stabilizer S a))
  let V := N.map (stabilizer S a).subtype ⊔ vertexZ S a
  let R := ⁅V, U⁆
  have hZuN : (vertexZ S u).subgroupOf (stabilizer S a) ≤ N :=
    Subgroup.subset_normalClosure
  have hQconj (g : stabilizer S a) :
      (vertexTwoCore S a).map (MulAut.conj (g : FreeAmalgam S)).toMonoidHom ≤
        vertexTwoCore S a := by
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨qA, hqA, rfl⟩ := hq
    exact Subgroup.mem_map_of_mem (stabilizer S a).subtype
      ((inferInstance : (pCore 2 (stabilizer S a)).Normal).conj_mem qA hqA g)
  have hconjcore (g : stabilizer S a) :
      U.map (MulAut.conj (g : FreeAmalgam S)).toMonoidHom ≤ vertexTwoCore S u := by
    let Ug := U.map (MulAut.conj (g : FreeAmalgam S)).toMonoidHom
    have hUgGu : Ug ≤ stabilizer S u :=
      ((Subgroup.map_mono hU).trans (hQconj g)).trans hQaGu
    have hUgTwo : IsPGroup 2 Ug := hUtwo.map _
    by_contra hUgcore
    apply criticalPair_commutator_not_le_center S T hTS hP hSne hA u c hcritU hb
      Ug hUgGu hUgTwo hUgcore
    apply Subgroup.commutator_le.mpr
    intro z hz x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    let zA : stabilizer S a := ⟨z, hZuGa hz⟩
    have hzAN : zA ∈ N := hZuN hz
    have hzinvN : g⁻¹ * zA * g ∈ N := by
      simpa using (inferInstance : N.Normal).conj_mem zA hzAN g⁻¹
    have hzinvV : (g : FreeAmalgam S)⁻¹ * z * g ∈ V :=
      (show N.map (stabilizer S a).subtype ≤ V from le_sup_left)
        (Subgroup.mem_map_of_mem (stabilizer S a).subtype hzinvN)
    have hr : ⁅(g : FreeAmalgam S)⁻¹ * z * g, x₀⁆ ∈ R :=
      Subgroup.commutator_mem_commutator hzinvV hx₀
    have hcomm := mem_center_map_commute (stabilizer S a) (hcentA hr) g.property
    have heq : ⁅z, (MulAut.conj (g : FreeAmalgam S)).toMonoidHom x₀⁆ =
        ⁅(g : FreeAmalgam S)⁻¹ * z * g, x₀⁆ := by
      calc
        _ = (g : FreeAmalgam S) * ⁅(g : FreeAmalgam S)⁻¹ * z * g, x₀⁆ *
            (g : FreeAmalgam S)⁻¹ := by
          simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
            commutatorElement_def]
          group
        _ = _ := by rw [hcomm]; simp
    rw [heq]
    exact hcentU hr
  obtain ⟨hVa, ha', hinputsA⟩ := criticalPair_actionInputs S T hTS hP hSne hA a a' hcritA hb
  obtain ⟨hVu, hc, hinputsU⟩ := criticalPair_actionInputs S T hTS hP hSne hA u c hcritU hb
  have hZuComm (z x : FreeAmalgam S) (hz : z ∈ vertexZ S u)
      (hx : x ∈ vertexTwoCore S u) : z * x = x * z := by
    exact (((mem_omegaOneCenterAmbient_iff (vertexTwoCore S u) z).mp
      (hinputsU.left_Z_le_coreOmega hz)).2.2 x hx).symm
  have hNcentral : N.map (stabilizer S a).subtype ≤ Subgroup.centralizer (U : Set (FreeAmalgam S)) := by
    apply Subgroup.map_le_iff_le_comap.mpr
    change Subgroup.closure (Group.conjugatesOfSet
      ((vertexZ S u).subgroupOf (stabilizer S a) : Set (stabilizer S a))) ≤ _
    apply (Subgroup.closure_le (K := _)).mpr
    intro z hz
    obtain ⟨z₀, hz₀, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    rw [← hg]
    change ((g * z₀ * g⁻¹ : stabilizer S a) : FreeAmalgam S) ∈
      Subgroup.centralizer (U : Set (FreeAmalgam S))
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxcore : (g : FreeAmalgam S)⁻¹ * x * g ∈ vertexTwoCore S u := by
      apply hconjcore g⁻¹
      simpa using Subgroup.mem_map_of_mem
        (MulAut.conj ((g⁻¹ : stabilizer S a) : FreeAmalgam S)).toMonoidHom hx
    have hcomm := hZuComm (z₀ : FreeAmalgam S)
      ((g : FreeAmalgam S)⁻¹ * x * g) hz₀ hxcore
    have h := congrArg (fun k : FreeAmalgam S => (g : FreeAmalgam S) * k * (g : FreeAmalgam S)⁻¹) hcomm
    simpa [mul_assoc] using h.symm
  have hZaCentral : vertexZ S a ≤ Subgroup.centralizer (U : Set (FreeAmalgam S)) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) z).mp
      (hinputsA.left_Z_le_coreOmega hz)).2.2 x (hU hx)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (sup_le hNcentral hZaCentral)

end Stellmacher.PushingUp
