module

public import Theory.SpecificGroups.ReeTwo.CoreActionPacking

/-!
# Reconstructing an inverting squaring action from one root image

Root 2 together with four successive images of root 0 under `c` generates
the core: the ten original roots have the explicit words below. A squaring
action takes those four orbit elements to every second element of the orbit
of its image of root 0. Thus its ten root images are determined by one
integer coordinate and its prescribed value on root 2.

Source: direct certificates in the verified coordinates of Shinoda (1975),
(2.3), using `CoreActionPacking` and the core presentation.
-/

@[expose] public section
open ReeTwo
namespace ReeTwo.Core.InvertingActionCensus
open CensusPacked

def orbitWord (g : Fin 5 → Core) : CoreRoot → Core :=
  ![g 0,
    g 0 * g 2 * g 0 * g 4 * g 3,
    g 4,
    g 0 * g 1 * g 4 * g 2,
    g 1,
    g 0 * g 4 * g 0 * g 4 * g 4 * g 4,
    g 0 * g 2 * g 1 * g 0 * g 1 * g 2,
    g 0 * g 2 * g 0 * g 2 * g 4 * g 4,
    g 0 * g 1 * g 0 * g 2 * g 1 * g 2,
    g 4 * g 4]

theorem orbitWord_map (f : Core →* Core) (g : Fin 5 → Core) (i : CoreRoot) :
    f (orbitWord g i) = orbitWord (fun k => f (g k)) i := by
  fin_cases i <;> simp [orbitWord, map_mul]

def packedOrbitWord (g : Fin 5 → Nat) : CoreRoot → Nat :=
  ![(g 0),
    (pmul (pmul (pmul (pmul (g 0) (g 2)) (g 0)) (g 4)) (g 3)),
    (g 4),
    (pmul (pmul (pmul (g 0) (g 1)) (g 4)) (g 2)),
    (g 1),
    (pmul (pmul (pmul (pmul (pmul (g 0) (g 4)) (g 0)) (g 4)) (g 4)) (g 4)),
    (pmul (pmul (pmul (pmul (pmul (g 0) (g 2)) (g 1)) (g 0)) (g 1)) (g 2)),
    (pmul (pmul (pmul (pmul (pmul (g 0) (g 2)) (g 0)) (g 2)) (g 4)) (g 4)),
    (pmul (pmul (pmul (pmul (pmul (g 0) (g 1)) (g 0)) (g 2)) (g 1)) (g 2)),
    (pmul (g 4) (g 4))]

theorem packedOrbitWord_code (g : Fin 5 → Core) (i : CoreRoot) :
    packedOrbitWord (fun k => code (g k)) i = code (orbitWord g i) := by
  fin_cases i <;> simp [packedOrbitWord, orbitWord, pmul_code]

def orbitGenerators : Fin 5 → Core :=
  ![root 0, decode 16, decode 765, decode 475, root 2]

private theorem c_zero : c (root 0) = decode 16 := by
  apply code_injective
  exact (cRoots_eq 0).symm

private theorem c_sixteen : c (decode 16) = decode 765 := by
  apply code_injective
  exact (cAct_code _).symm.trans (by decide +kernel)

private theorem c_seven_sixtyfive : c (decode 765) = decode 475 := by
  apply code_injective
  exact (cAct_code _).symm.trans (by decide +kernel)

theorem orbitGenerators_code : (fun k => code (orbitGenerators k)) = ![1,16,765,475,4] := by
  funext k
  exact (by decide +kernel : ∀ k, code (orbitGenerators k) = ![1,16,765,475,4] k) k

theorem orbitWord_generators (i : CoreRoot) : orbitWord orbitGenerators i = root i := by
  apply code_injective
  rw [← packedOrbitWord_code, orbitGenerators_code]
  exact (by decide +kernel : ∀ i, packedOrbitWord ![1,16,765,475,4] i = code (root i)) i

def imageCodes (n : Nat) : CoreRoot → Nat :=
  packedOrbitWord ![n, (cAct^[2]) n, (cAct^[2]) ((cAct^[2]) n),
    (cAct^[2]) ((cAct^[2]) ((cAct^[2]) n)), 516]

theorem squaring_apply (β δ : MulAut Core)
    (hc : β * δ * β⁻¹ = δ ^ 2) (x : Core) : β (δ x) = (δ ^ 2) (β x) := by
  have h := congrArg (fun f : MulAut Core => f x) (mul_inv_eq_iff_eq_mul.mp hc)
  simpa only [MulAut.mul_apply] using h

private theorem intertwining_code (β : MulAut Core)
    (hc : β * c * β⁻¹ = c ^ 2) (x : Core) :
    code (β (c x)) = (cAct^[2]) (code (β x)) :=
  (congrArg code (squaring_apply β c hc x)).trans (cAct_iterate_code 2 (β x)).symm

private theorem beta_sixteen (β : MulAut Core) (hc : β * c * β⁻¹ = c ^ 2) :
    code (β (decode 16)) = (cAct^[2]) (code (β (root 0))) :=
  (congrArg (fun x => code (β x)) c_zero).symm.trans (intertwining_code β hc _)

private theorem beta_seven_sixtyfive (β : MulAut Core) (hc : β * c * β⁻¹ = c ^ 2) :
    code (β (decode 765)) = (cAct^[2]) ((cAct^[2]) (code (β (root 0)))) :=
  (congrArg (fun x => code (β x)) c_sixteen).symm.trans
    ((intertwining_code β hc _).trans (congrArg (cAct^[2]) (beta_sixteen β hc)))

private theorem beta_four_seventyfive (β : MulAut Core) (hc : β * c * β⁻¹ = c ^ 2) :
    code (β (decode 475)) = (cAct^[2]) ((cAct^[2]) ((cAct^[2]) (code (β (root 0))))) :=
  (congrArg (fun x => code (β x)) c_seven_sixtyfive).symm.trans
    ((intertwining_code β hc _).trans (congrArg (cAct^[2]) (beta_seven_sixtyfive β hc)))

theorem aut_images_code (β : MulAut Core)
    (hc : β * c * β⁻¹ = c ^ 2) (ht : β (root 2) = (root 2)⁻¹) :
    ∀ i, code (β (root i)) = imageCodes (code (β (root 0))) i := by
  have hg : (fun k => code (β (orbitGenerators k))) =
      ![code (β (root 0)), (cAct^[2]) (code (β (root 0))),
        (cAct^[2]) ((cAct^[2]) (code (β (root 0)))),
        (cAct^[2]) ((cAct^[2]) ((cAct^[2]) (code (β (root 0))))), 516] := by
    funext k
    fin_cases k
    · rfl
    · exact beta_sixteen β hc
    · exact beta_seven_sixtyfive β hc
    · exact beta_four_seventyfive β hc
    · change code (β (root 2)) = 516
      rw [ht]
      rfl
  intro i
  rw [← orbitWord_generators i]
  change code (β.toMonoidHom _) = _
  rw [orbitWord_map, ← packedOrbitWord_code]
  change packedOrbitWord (fun k => code (β (orbitGenerators k))) i = _
  rw [hg]
  rfl

/-- A generator-wise converse to the squaring identity, with the action abstract. -/
theorem squaring_conj_of_apply (β δ : MulAut Core)
    (h : ∀ i, β (δ (root i)) = (δ ^ 2) (β (root i))) :
    β * δ * β⁻¹ = δ ^ 2 := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply aut_ext
  intro i
  simpa only [MulAut.mul_apply] using h i

/-- Check the fourth power without unfolding a concrete automorphism's definition. -/
theorem aut_four_of_apply (β : MulAut Core)
    (h : ∀ i, β (β (β (β (root i)))) = root i) : β ^ 4 = 1 := by
  apply aut_ext
  intro i
  simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using h i

end ReeTwo.Core.InvertingActionCensus
