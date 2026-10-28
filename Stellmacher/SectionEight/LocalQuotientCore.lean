module
public import Stellmacher.LaterDefs

/-!
# The local center quotient has trivial 2-core

For any coset-graph vertex d, the quotient of G_d by the centralizer
of Z_d has trivial 2-core. The statement accepts the quotient-module
witness used by Section 8; it needs only the defining Sylow-center generation
of Z_d, not Hypothesis 2 or any structural result from Section 1.

Pull back an element of the quotient 2-core. For every Sylow subgroup T
of G_d, its image is in the image of T, so it can be written as a
kernel element times an element of T. Both factors centralize
Ω₁(Z(T)). As these subgroups generate Z_d, the original element is
in the centralizer kernel, and its image is trivial.

This is the argument of Stellmacher (2.1), applied directly to the graph's
Sylow-center definition, supplying the Section 1 hypothesis required in
(8.1), journal p.37 of refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

/-- The faithful local quotient on the center module has trivial 2-core. -/
public theorem local_quotient_twoCore_eq_bot
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (d : Γ.Vertex)
    (w : QuotientModuleWitness (stabilizer Γ d)
      (stabilizer Γ d ⊓ Subgroup.centralizer (z Γ d : Set G)) (z Γ d)) :
    let _ := w.groupX
    let _ := w.finiteX
    pCore 2 w.X = ⊥ := by
  let := w.groupX
  let := w.finiteX
  apply bot_unique
  intro x hx
  obtain ⟨a, rfl⟩ := w.surjective x
  have hza : z Γ d ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
    rw [z, Γ.zAt_def]
    refine sSup_le fun Z hZ ↦ ?_
    change ∃ T : Sylow 2 (stabilizer Γ d),
      Z = omegaOneCenter ((T : Subgroup (stabilizer Γ d)).map
        (stabilizer Γ d).subtype) at hZ
    obtain ⟨T, rfl⟩ := hZ
    let U : Subgroup G := (T : Subgroup (stabilizer Γ d)).map
      (stabilizer Γ d).subtype
    have hOmegaZ : omegaOneCenter U ≤ z Γ d := by
      rw [z, Γ.zAt_def]
      exact le_sSup ⟨T, rfl⟩
    let Tb : Sylow 2 w.X := T.mapSurjective w.surjective
    have haTb : w.projection a ∈ (Tb : Subgroup w.X) :=
      fitting_pCore_le_sylow Tb hx
    change w.projection a ∈ (T : Subgroup (stabilizer Γ d)).map
      w.projection at haTb
    obtain ⟨t, ht, hta⟩ := haTb
    have hker : a * t⁻¹ ∈ w.projection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hta]
      simp
    rw [w.kernel_eq] at hker
    have hkC : ((a * t⁻¹ : stabilizer Γ d) : G) ∈
        Subgroup.centralizer (omegaOneCenter U : Set G) :=
      Subgroup.centralizer_le hOmegaZ hker.2
    have htC : (t : G) ∈ Subgroup.centralizer (omegaOneCenter U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨yU, hyU, rfl⟩ := hy
      obtain ⟨yC, _, rfl⟩ := hyU
      have htU : (t : G) ∈ U := Subgroup.mem_map_of_mem _ ht
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp yC.property (⟨t, htU⟩ : U)).symm
    have haC : (a : G) ∈ Subgroup.centralizer (omegaOneCenter U : Set G) := by
      have hh := (Subgroup.centralizer (omegaOneCenter U : Set G)).mul_mem hkC htC
      simpa using hh
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact (Subgroup.mem_centralizer_iff.mp haC y hy).symm
  have ha : a ∈ w.projection.ker := by
    rw [w.kernel_eq]
    refine ⟨a.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hza hy) a (Set.mem_singleton _)).symm
  exact ha

end Stellmacher.SectionEight

