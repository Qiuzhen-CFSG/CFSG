module
public import Theory.GroupTheory.CComponent.SimplePairKernel
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleKernel
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# Kernels of irreducible binary actions above simple-core components

A nontrivial irreducible binary action detects the two-residual. If a normal
simple-core C-component has a two-group supplement, its surviving image
forces the kernel into the two-core. The same holds for a normal pair of
conjugate simple-core C-components: normality of the kernel makes both
components survive, and the component-pair kernel theorem applies.

In both cases normal two-subgroups act trivially, giving equality of the
kernel with the original two-core. The intended consumer is the literal
partner chief action in Aschbacher--Smith 15.2.27(2), printed p.1119.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace Representation.BinaryOffender
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem avoids_kernel (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    (K S : Subgroup G) [K.Normal] (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤)
    (hn : ∃ g, ρ g ≠ 1) : ¬ K ≤ ρ.ker := by
  have hres : pResidual 2 G ≤ K := (pResidual_le_iff_isPGroup_quotient 2 K).mpr
    (isPGroup_quotient_of_sup_eq_top K S hS hgen)
  apply mt (fun hk => hres.trans hk)
  apply irreducible_residual_not_le_ker ρ
  obtain ⟨g,hg⟩ := hn
  have hv : ∃ w, ρ g w ≠ w := by
    by_contra hh
    apply hg
    ext w
    exact not_exists_not.mp hh w
  obtain ⟨w,hw⟩ := hv
  exact ⟨g,w,hw⟩

/-- A simple-core component with a two-group supplement is detected faithfully modulo O₂. -/
theorem kernel_eq_twoCore_of_simpleCore_supplement
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    (K S : Subgroup G) [K.Normal] (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤) (hn : ∃ g, ρ g ≠ 1) :
    ρ.ker = pCore 2 G := by
  let := hK.perfect
  let : Group.IsPerfect (K ⧸ pCore 2 K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hz : center (K ⧸ pCore 2 K) = ⊥ :=
    (inferInstance : (center (K ⧸ pCore 2 K)).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  let : IsQuasisimple (K ⧸ pCore 2 K) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  have hQ : pCore 2 G ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  have hk := (QuasisimpleKernel.normal_kernel_structure K S ρ.ker hK hS hgen hQ
    (avoids_kernel ρ K S hS hgen hn)).1
  rw [hz,MonoidHom.comap_bot,QuotientGroup.ker_mk'] at hk
  exact le_antisymm (hk.trans (sup_le le_rfl (pCoreIn_le_of_subnormal 2 hK.subnormal))) hQ

/-- The same kernel equality for a conjugate pair of simple-core components. -/
theorem kernel_eq_twoCore_of_conjugate_simpleCore_pair
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    (B S : Subgroup G) (t : G) (hB : B.IsCComponent)
    [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hne : B ≠ B.conjBy t) [(B ⊔ B.conjBy t).Normal]
    (hS : IsPGroup 2 S) (hgen : (B ⊔ B.conjBy t) ⊔ S = ⊤)
    (hn : ∃ g, ρ g ≠ 1) : ρ.ker = pCore 2 G := by
  have hav := avoids_kernel ρ (B ⊔ B.conjBy t) S hS hgen hn
  have hBN : ¬ B ≤ ρ.ker := by
    intro hh
    apply hav
    exact sup_le hh ((map_mono hh).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top t))))
  have hDN : ¬ B.conjBy t ≤ ρ.ker := by
    intro hh
    apply hBN
    intro b hb
    have hc := hh (mem_map_of_mem (MulAut.conj t).toMonoidHom hb)
    have hv := (inferInstance : ρ.ker.Normal).conj_mem _ hc t⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using hv
  let e := (MulAut.conj t).subgroupMap B
  let : IsSimpleGroup (B.conjBy t ⧸ pCore 2 (B.conjBy t)) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.isSimpleGroup
  have hp := isTwoGroup_of_normal_avoiding_simpleCore_pair B (B.conjBy t) S ρ.ker
    hB (hB.map_equiv (MulAut.conj t)) hne hS hgen hBN hDN
  exact le_antisymm (le_sSup ⟨inferInstance,hp⟩)
    (normal_p_subgroup_le_ker ρ _ pCore_isPGroup)

end Representation.BinaryOffender
