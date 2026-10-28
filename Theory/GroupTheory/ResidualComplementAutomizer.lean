module
public import Theory.GroupTheory.PResidual.CoreCentralizer

/-!
# Automizers of residual complements through two-group kernels

Suppose a homomorphism maps an odd complement onto the two-residual of a
finite group with trivial two-core. If the complement meets the kernel
trivially and its two-group actor factors through the kernel and the
complement normalizer, the complement automizer is the actual actor image.
The two maps on the normalizer have equal kernels: a two-subgroup
centralizing the residual lies in the two-core. Restriction to a containing
subgroup preserves this automizer, with the literal conjugation maps.

The application is the cubic automizer in Aschbacher--Smith 8.3.7,
printed p.724: the actor image is a Sylow subgroup of S₃ wr C₂.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H] [Finite H]

/-- Removing a two-group kernel identifies the complement automizer with the
actual image of its two-group actor. -/
theorem complement_automizer_equiv_image
    (f : G →* H) (T P : Subgroup G)
    (hT : IsPGroup 2 T) (hK : pCore 2 H = ⊥)
    (hP : P.map f = pResidual 2 H)
    (hd : Disjoint P f.ker)
    (hfactor : T ≤ f.ker ⊔ (T ⊓ normalizer (P : Set G))) :
    Nonempty ((P.normalizerMonoidHom.comp
      (inclusion (show T ⊓ normalizer (P : Set G) ≤ normalizer (P : Set G)
        from inf_le_right))).range ≃* T.map f) := by
  let N := T ⊓ normalizer (P : Set G)
  let a : N →* MulAut P := P.normalizerMonoidHom.comp (inclusion inf_le_right)
  let b : N →* H := f.comp N.subtype
  have hk : a.ker = b.ker := by
    apply le_antisymm
    · let R := a.ker.map N.subtype
      have hRC : R ≤ centralizer (P : Set G) := by
        rintro x ⟨s,hs,rfl⟩
        have hs' : inclusion (show N ≤ normalizer (P : Set G) from inf_le_right) s ∈
            P.normalizerMonoidHom.ker := hs
        rwa [normalizerMonoidHom_ker] at hs'
      have hcomm : ⁅R.map f,pResidual 2 H⁆ = ⊥ := by
        rw [←hP,←map_commutator,
          commutator_eq_bot_iff_le_centralizer.mpr hRC,Subgroup.map_bot]
      have hle := pSubgroup_le_pCore_of_centralizes_pResidual (R.map f)
        (((hT.to_le inf_le_left).to_subgroup a.ker).map N.subtype |>.map f)
        (commutator_eq_bot_iff_le_centralizer.mp hcomm)
      rw [hK] at hle
      intro s hs
      exact hle (mem_map_of_mem f (mem_map_of_mem N.subtype hs))
    · intro s hs
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      have hconj : (s : G) * (x : G) * (s : G)⁻¹ ∈ P :=
        (s.property.2 (x : G)).mp x.property
      have hmem : (s : G) * (x : G) * (s : G)⁻¹ * (x : G)⁻¹ ∈ P :=
        P.mul_mem hconj (P.inv_mem x.property)
      have hfs : f (s : G) = 1 := hs
      have hf : (s : G) * (x : G) * (s : G)⁻¹ * (x : G)⁻¹ ∈ f.ker := by
        simp only [MonoidHom.mem_ker,map_mul,map_inv,hfs,one_mul,inv_one,mul_one,mul_inv_cancel]
      exact mul_inv_eq_one.mp (hd.le_bot ⟨hmem,hf⟩)
  have hr : b.range = T.map f := by
    apply le_antisymm
    · rw [MonoidHom.range_comp,range_subtype]
      exact map_mono inf_le_left
    · have hh := map_mono (f := f) hfactor
      simp only [Subgroup.map_sup,Subgroup.map_ker_self,bot_sup_eq] at hh
      simpa only [b,MonoidHom.range_comp,range_subtype] using hh
  exact ⟨(QuotientGroup.quotientKerEquivRange a).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      ((QuotientGroup.quotientKerEquivRange b).trans (MulEquiv.subgroupCongr hr)))⟩
/-- The automizer is unchanged on restricting its ambient group to an
 overgroup of the actor and the acted-on subgroup. -/
theorem normalizer_action_range_equiv_subgroupOf
    (T P M : Subgroup G) (hTM : T ≤ M) (hPM : P ≤ M) :
    Nonempty ((P.normalizerMonoidHom.comp (inclusion
      (show T ⊓ normalizer (P : Set G) ≤ normalizer (P : Set G) from inf_le_right))).range ≃*
      ((P.subgroupOf M).normalizerMonoidHom.comp (inclusion
        (show T.subgroupOf M ⊓ normalizer (P.subgroupOf M : Set M) ≤
          normalizer (P.subgroupOf M : Set M) from inf_le_right))).range) := by
  let N := T ⊓ normalizer (P : Set G)
  let N' := T.subgroupOf M ⊓ normalizer (P.subgroupOf M : Set M)
  have hn : N.subgroupOf M = N' := by
    rw [show N.subgroupOf M = T.subgroupOf M ⊓ (normalizer (P : Set G)).subgroupOf M
      from rfl, subgroupOf_normalizer_eq hPM]
  let c : N' ≃* N := (MulEquiv.subgroupCongr hn).symm.trans
    (subgroupOfEquivOfLe (inf_le_left.trans hTM))
  let a : N →* MulAut P := P.normalizerMonoidHom.comp (inclusion inf_le_right)
  let b : N' →* MulAut (P.subgroupOf M) :=
    (P.subgroupOf M).normalizerMonoidHom.comp (inclusion inf_le_right)
  let e : P ≃* P.subgroupOf M := (subgroupOfEquivOfLe hPM).symm
  have he : b = (MulAut.congr e).toMonoidHom.comp (a.comp c.toMonoidHom) := by
    ext s x
    rfl
  have hr : b.range = a.range.map (MulAut.congr e).toMonoidHom := by
    rw [he,MonoidHom.range_comp,MonoidHom.range_comp,(MonoidHom.range_eq_top.mpr c.surjective),
      ←MonoidHom.range_eq_map]
  exact ⟨(a.range.equivMapOfInjective (MulAut.congr e).toMonoidHom
    (MulAut.congr e).injective).trans (MulEquiv.subgroupCongr hr.symm)⟩

end Theory.GroupTheory
