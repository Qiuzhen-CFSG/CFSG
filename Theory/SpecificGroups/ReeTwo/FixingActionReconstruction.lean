module

public import Theory.SpecificGroups.ReeTwo.InvertingActionReconstruction

/-!
# Reconstructing a root-fixing squaring action from one root image

Root 2 together with four successive images of root 0 under `c` generates
the core: the ten original roots have explicit words in these generators. A squaring
action takes those four orbit elements to every second element of the orbit
of its image of root 0. Thus its ten root images are determined by one
integer coordinate and its prescribed value on root 2.

Source: direct certificates in the verified coordinates of Shinoda (1975),
(2.3), using `InvertingActionReconstruction` and the core presentation.
-/

@[expose] public section
open ReeTwo
namespace ReeTwo.Core.FixingActionCensus
open CensusPacked

open InvertingActionCensus

private theorem c_zero : c (root 0) = decode 16 := by
  apply code_injective
  exact (cRoots_eq 0).symm

private theorem c_sixteen : c (decode 16) = decode 765 := by
  apply code_injective
  exact (cAct_code _).symm.trans (by decide +kernel)

private theorem c_seven_sixtyfive : c (decode 765) = decode 475 := by
  apply code_injective
  exact (cAct_code _).symm.trans (by decide +kernel)

def imageCodes (n : Nat) : CoreRoot → Nat :=
  packedOrbitWord ![n, (cAct^[2]) n, (cAct^[2]) ((cAct^[2]) n),
    (cAct^[2]) ((cAct^[2]) ((cAct^[2]) n)), 4]

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
    (hc : β * c * β⁻¹ = c ^ 2) (ht : β (root 2) = root 2) :
    ∀ i, code (β (root i)) = imageCodes (code (β (root 0))) i := by
  have hg : (fun k => code (β (orbitGenerators k))) =
      ![code (β (root 0)), (cAct^[2]) (code (β (root 0))),
        (cAct^[2]) ((cAct^[2]) (code (β (root 0)))),
        (cAct^[2]) ((cAct^[2]) ((cAct^[2]) (code (β (root 0))))), 4] := by
    funext k
    fin_cases k
    · rfl
    · exact beta_sixteen β hc
    · exact beta_seven_sixtyfive β hc
    · exact beta_four_seventyfive β hc
    · change code (β (root 2)) = 4
      rw [ht]
      rfl
  intro i
  rw [← orbitWord_generators i]
  change code (β.toMonoidHom _) = _
  rw [orbitWord_map, ← packedOrbitWord_code]
  change packedOrbitWord (fun k => code (β (orbitGenerators k))) i = _
  rw [hg]
  rfl

end ReeTwo.Core.FixingActionCensus
