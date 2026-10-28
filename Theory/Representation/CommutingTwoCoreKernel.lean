module
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryOffender.CentralSectionAction

/-!
# A two-core kernel under commuting generators

A two-group has a nonzero fixed vector in characteristic two. If one
ambient generating subgroup normalizes it and the other commutes with its
action, its fixed space is invariant under the whole group. Irreducibility
then kills the two-group. Relative normalization is sufficient; ambient
normality of the original two-group is not assumed.

The original Hermitian chief-section consumer applies this to the two-core
of O²(H)V, which is normal in H and commutes with the local residual in the
action. Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
set_option backward.isDefEq.respectTransparency false

/-- A two-group normalized by one generating subgroup and centralized in the
action by the other acts trivially on an irreducible binary module. -/
theorem twoGroup_kernel_of_commuting_supplement
    (ρ : Representation (ZMod 2) G W) [ρ.IsIrreducible]
    (R H Q : Subgroup G) (hgen : R ⊔ H = ⊤) (hQ : IsPGroup 2 Q)
    (hHQ : H ≤ normalizer (Q : Set G))
    (hc : ∀ (r : R) (q : Q), Commute (ρ r) (ρ q)) : Q ≤ ρ.ker := by
  let X := fixedSpace ρ Q
  have hR : R ≤ subspaceStabilizer ρ X := by
    apply le_subspaceStabilizer
    intro r hr w hw q
    change ρ q (ρ r w) = ρ r w
    have hh : ρ q (ρ r w) = ρ r (ρ q w) :=
      LinearMap.congr_fun (hc ⟨r,hr⟩ q).eq.symm w
    rw [hh]
    exact congrArg (ρ r) (show ρ q w = w from hw q)
  have hH : H ≤ subspaceStabilizer ρ X := fixedSpace_stable_of_normalizes ρ hHQ
  have htop : subspaceStabilizer ρ X = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact sup_le hR hH
  let S : Subrepresentation ρ := {
    toSubmodule := X
    apply_mem_toSubmodule g w hw := (htop ▸ mem_top g : g ∈ subspaceStabilizer ρ X) w |>.2 hw }
  let := Subrepresentation.irreducible_module_nontrivial ρ
  have hchar : ringChar (ZMod 2) = 2 := ringChar.eq _ 2
  have hchar0 : ringChar (ZMod 2) ≠ 0 := by rw [hchar]; decide
  have hQchar : IsPGroup (ringChar (ZMod 2)) Q := by rwa [hchar]
  obtain ⟨w,hw,hfix⟩ := pGroup_fix_nonzero_vector hchar0 hQchar (ρ.comp Q.subtype)
  have hSne : S ≠ ⊥ := by
    intro hz
    have hm : w ∈ S.toSubmodule := hfix
    rw [hz] at hm
    exact hw hm
  have hS : S = ⊤ := (inferInstance : ρ.IsIrreducible).eq_bot_or_eq_top S |>.resolve_left hSne
  intro q hq
  apply LinearMap.ext
  intro w
  have hw : w ∈ S.toSubmodule := hS ▸ Submodule.mem_top
  exact hw ⟨q,hq⟩
end Representation.BinaryOffender
