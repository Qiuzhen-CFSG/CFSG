module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeFiveAction

/-!
# The scalar commutant of the native M22 quintet five-space

The literal A5 subgroup of the five-part S5 acts without fixed vectors on
the quintet kernel. In characteristic two, an A5-fixed vector would give an
S5-fixed vector by applying an odd involution minus the identity. The native
fixed-vector calculation excludes this. The inner four-space is transitive
on nonzero vectors through the existing SL2(4) marking, hence irreducible.
Every nonzero submodule consequently contains that four-space.

A commuting endomorphism is scalar on the one-dimensional coinvariant
quotient. Subtracting this scalar gives a map with nonzero kernel; its
kernel contains the inner four-space, so its image has dimension at most
one and must vanish. This gives the faithful binary multiplicity action
on the original two-copy section in Chapter8's M22-code pair.

Source: Aschbacher--Smith H.14.3(2), H.16.3(3), and 8.2.8(4--5), printed
pp.397,403,718--719, refs/quasithin.pdf. Native ATLAS attribution is retained
by the imported quintet calculations; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
open M22ChapterH.Quintet

private theorem fivePart_lift (a : alternatingGroup (Fin 5)) :
    ∃ g : naturalActor, NaturalQuotient.q g.val = a.val := by
  have hm : a.val ∈ naturalFivePartGroup := naturalFivePart_eq.symm ▸ a.property
  exact hm

private theorem kernel_fixed_zero (v : Additive M22Quintet.K)
    (hv : ∀ g, kernelS5Conjugation g v = v) : v = 0 := by
  apply coreTranslationEquiv.injective
  rw [map_zero]
  apply outerTranslationConjugation_fixed_eq_zero
  intro g
  have he := LinearMap.congr_fun (coreTranslationRepresentationEquiv.isIntertwining' g) v
  change coreTranslationEquiv (kernelConjugation g v) = outerTranslationConjugation g (coreTranslationEquiv v) at he
  rw [←kernelS5Conjugation_q,hv] at he
  exact he.symm

/-- The even five-part group also fixes no nonzero vector of the actual quintet kernel. -/
theorem fiveAction_fixed_zero (v : Additive M22Quintet.K)
    (hv : ∀ a, fiveAction a v = v) : v = 0 := by
  let t : Equiv.Perm (Fin 5) := Equiv.swap 0 1
  have ht : t * t = 1 := Equiv.swap_mul_self _ _
  have hsign : Equiv.Perm.sign t = -1 := Equiv.Perm.sign_swap (by decide)
  have even_fix (g : Equiv.Perm (Fin 5)) (hg : g ∈ alternatingGroup (Fin 5)) :
      kernelS5Conjugation g v = v := hv ⟨g,hg⟩
  have odd_fix (g : Equiv.Perm (Fin 5)) (hg : g ∉ alternatingGroup (Fin 5)) :
      kernelS5Conjugation g v = kernelS5Conjugation t v := by
    have hs : Equiv.Perm.sign g = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h | h
      · exact (hg (Equiv.Perm.mem_alternatingGroup.mpr h)).elim
      · exact h
    have hm : t * g ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup,map_mul,hsign,hs]
      norm_num
    have hh := congrArg (kernelS5Conjugation t) (even_fix (t*g) hm)
    simpa only [←Module.End.mul_apply,←map_mul,←mul_assoc,ht,one_mul] using hh
  have htfix : kernelS5Conjugation t v = v := by
    have hz : kernelS5Conjugation t v - v = 0 := by
      apply kernel_fixed_zero
      intro g
      rw [map_sub]
      by_cases hg : g ∈ alternatingGroup (Fin 5)
      · have hc : g*t = t*(t*g*t) := by rw [←mul_assoc,←mul_assoc,ht,one_mul]
        have hm : t*g*t ∈ alternatingGroup (Fin 5) := by
          rw [Equiv.Perm.mem_alternatingGroup,map_mul,map_mul,hsign,
            Equiv.Perm.mem_alternatingGroup.mp hg]
          norm_num
        rw [even_fix g hg,←Module.End.mul_apply,←map_mul,hc,map_mul,
          Module.End.mul_apply,even_fix _ hm]
      · have hm : g*t ∈ alternatingGroup (Fin 5) := by
          rw [Equiv.Perm.mem_alternatingGroup,map_mul,hsign]
          rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hs | hs
          · exact (hg (Equiv.Perm.mem_alternatingGroup.mpr hs)).elim
          · rw [hs]; norm_num
        rw [←Module.End.mul_apply,←map_mul,even_fix _ hm,odd_fix g hg]
        apply sub_eq_sub_iff_add_eq_add.mpr
        have htwo (w : Additive M22Quintet.K) : w + w = 0 := by
          have he : (1 : ZMod 2) + 1 = 0 := by decide
          simpa only [add_smul,one_smul,zero_smul] using
            congrArg (fun c : ZMod 2 => c • w) he
        rw [htwo,htwo]
    exact sub_eq_zero.mp hz
  apply kernel_fixed_zero v
  intro g
  by_cases hg : g ∈ alternatingGroup (Fin 5)
  · exact even_fix g hg
  · exact (odd_fix g hg).trans htfix

private def fiveInner : Subrepresentation fiveAction where
  toSubmodule := innerInclusion.range
  apply_mem_toSubmodule a v hv := by
    obtain ⟨g,hg⟩ := fivePart_lift a
    obtain ⟨w,rfl⟩ := hv
    change kernelS5Conjugation a.val (innerInclusion w) ∈ innerInclusion.range
    rw [←hg,kernelS5Conjugation_q,←innerInclusion_equivariant innerInputs]
    exact ⟨_,rfl⟩

private theorem fiveInner_dim : Module.finrank (ZMod 2) fiveInner.toSubmodule = 4 := by
  change Module.finrank (ZMod 2) innerInclusion.range = 4
  rw [LinearMap.finrank_range_of_inj innerInclusion_injective,innerIntersection_finrank]

private theorem inner_natural_transitive (u z : Additive A0)
    (hu : innerCoreNaturalEquiv u ≠ 0) (hz : innerCoreNaturalEquiv z ≠ 0) :
    ∃ g : naturalActor, innerConjugation innerInputs g.val u = z := by
  obtain ⟨a,ha⟩ := SL2FourNatural.transitive_nonzero _ _ hu hz
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective naturalActorTranslations (naturalActorModelEquiv.symm a)
  refine ⟨g,innerCoreNaturalEquiv.injective ?_⟩
  rw [innerCore_natural,show QuotientGroup.mk g = naturalActorModelEquiv.symm a from hg,
    naturalActorModelEquiv.apply_symm_apply,ha]

set_option backward.isDefEq.respectTransparency false in
private theorem fiveInner_transitive (v w : fiveInner.toSubmodule) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ a, fiveInner.toRepresentation a v = w := by
  obtain ⟨u,hu⟩ := v.property
  obtain ⟨z,hz⟩ := w.property
  have hu0 : innerCoreNaturalEquiv u ≠ 0 := by
    intro he
    have : u = 0 := innerCoreNaturalEquiv.injective (he.trans (map_zero _).symm)
    exact hv (Subtype.ext (by rw [←hu,this,map_zero]; rfl))
  have hz0 : innerCoreNaturalEquiv z ≠ 0 := by
    intro he
    have : z = 0 := innerCoreNaturalEquiv.injective (he.trans (map_zero _).symm)
    exact hw (Subtype.ext (by rw [←hz,this,map_zero]; rfl))
  obtain ⟨g,hg⟩ := inner_natural_transitive u z hu0 hz0
  have hmem : NaturalQuotient.q g.val ∈ alternatingGroup (Fin 5) :=
    naturalFivePart_eq ▸ (show NaturalQuotient.q g.val ∈ naturalFivePartGroup from ⟨g,rfl⟩)
  refine ⟨⟨NaturalQuotient.q g.val,hmem⟩,?_⟩
  apply Subtype.ext
  change kernelS5Conjugation (NaturalQuotient.q g.val) v.val = w.val
  rw [←hu,←hz,kernelS5Conjugation_q,←innerInclusion_equivariant innerInputs]
  exact congrArg innerInclusion hg

private theorem fiveInner_irreducible : IsIrreducible fiveInner.toRepresentation := by
  let : Nontrivial fiveInner.toSubmodule := Module.nontrivial_of_finrank_pos (by rw [fiveInner_dim]; decide)
  refine ⟨fun A => ?_⟩
  by_cases hb : A.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hb)
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · exact hw ▸ A.toSubmodule.zero_mem
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨a,rfl⟩ := fiveInner_transitive v w hv0 hw
    exact A.apply_mem_toSubmodule a hv

private theorem five_small_bot (A : Subrepresentation fiveAction)
    (hd : Module.finrank (ZMod 2) A.toSubmodule ≤ 1) : A = ⊥ := by
  apply bot_unique
  intro v hv
  apply fiveAction_fixed_zero v
  intro g
  have he := LinearGroup.eq_one_of_binary_finrank_le_one hd
    (LinearMap.GeneralLinearGroup.toLinearEquiv (A.toRepresentation.asGroupHom g))
  exact congrArg Subtype.val (LinearEquiv.congr_fun he ⟨v,hv⟩)

private theorem five_subrepresentation (A : Subrepresentation fiveAction) :
    A = ⊥ ∨ fiveInner ≤ A := by
  let J : Subrepresentation fiveInner.toRepresentation := {
    toSubmodule := A.toSubmodule.comap fiveInner.toSubmodule.subtype
    apply_mem_toSubmodule a v hv := A.apply_mem_toSubmodule a hv }
  rcases fiveInner_irreducible.eq_bot_or_eq_top J with hj | hj
  · left
    have hi : fiveInner.toSubmodule ⊓ A.toSubmodule = ⊥ := by
      apply bot_unique
      intro v hv
      have hh : (⟨v,hv.1⟩ : fiveInner.toSubmodule) ∈ J := hv.2
      rw [hj] at hh
      exact congrArg Subtype.val (show (⟨v,hv.1⟩ : fiveInner.toSubmodule) = 0 from hh)
    have hd := Submodule.finrank_sup_add_finrank_inf_eq fiveInner.toSubmodule A.toSubmodule
    rw [hi,finrank_bot,fiveInner_dim] at hd
    have hb := (fiveInner.toSubmodule ⊔ A.toSubmodule).finrank_le
    rw [kernel_finrank] at hb
    exact five_small_bot A (by omega)
  · right
    intro v hv
    have hh : (⟨v,hv⟩ : fiveInner.toSubmodule) ∈ J := hj.symm ▸ Submodule.mem_top
    exact hh

/-- The entire binary endomorphism commutant of the native A5 five-space is scalar. -/
theorem fiveAction_commuting_scalar (f : Module.End (ZMod 2) (Additive M22Quintet.K))
    (hf : ∀ a v, f (fiveAction a v) = fiveAction a (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let F : IntertwiningMap fiveAction fiveAction := ⟨f,by
    intro a
    apply LinearMap.ext
    exact hf a⟩
  have hdim : Module.finrank (ZMod 2) (Coinvariants fiveAction) = 1 := by
    have hd := (Coinvariants.ker fiveAction).finrank_quotient_add_finrank
    rw [fiveAction_moved_dim,kernel_finrank] at hd
    change Module.finrank (ZMod 2) (Coinvariants fiveAction) + 4 = 5 at hd
    omega
  obtain ⟨c,hc,_⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim
    (Coinvariants.map fiveAction fiveAction F)
  let D : IntertwiningMap fiveAction fiveAction := F - c • IntertwiningMap.id fiveAction
  have hm (v : Additive M22Quintet.K) : D v ∈ Coinvariants.ker fiveAction := by
    apply (Coinvariants.mk_eq_zero fiveAction).mp
    change Coinvariants.mk fiveAction (f v - c • v) = 0
    rw [map_sub,map_smul]
    have hh := LinearMap.congr_fun hc (Coinvariants.mk fiveAction v)
    change Coinvariants.mk fiveAction (f v) = c • Coinvariants.mk fiveAction v at hh
    rw [hh,sub_self]
  have hk : D.ker ≠ ⊥ := by
    intro hk
    have hinj : Function.Injective D := LinearMap.ker_eq_bot.mp
      (congrArg Subrepresentation.toSubmodule hk)
    have hsur := (LinearMap.injective_iff_surjective).mp hinj
    have ht : Coinvariants.ker fiveAction = ⊤ := by
      apply top_unique
      intro v _
      obtain ⟨u,rfl⟩ := hsur v
      exact hm u
    have hd := fiveAction_moved_dim
    rw [ht,finrank_top,kernel_finrank] at hd
    omega
  have hN : fiveInner ≤ D.ker := (five_subrepresentation D.ker).resolve_left hk
  have hdimK : 4 ≤ Module.finrank (ZMod 2) D.toLinearMap.ker := by
    rw [←fiveInner_dim]
    exact Submodule.finrank_mono hN
  have hrank := D.toLinearMap.finrank_range_add_finrank_ker
  rw [kernel_finrank] at hrank
  have hzero : D.range = ⊥ := five_small_bot D.range (by
    change Module.finrank (ZMod 2) D.toLinearMap.range ≤ 1
    omega)
  refine ⟨c,fun v => sub_eq_zero.mp ?_⟩
  have hv : D v ∈ D.range := ⟨v,rfl⟩
  rw [hzero] at hv
  exact hv

end MathieuCode.NormalizedShadowRows.M22CodeSection
