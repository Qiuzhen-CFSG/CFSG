module
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.SpecificGroups.SymmetricEight.CentralPair
public import Theory.Representation.BinaryOffender.CommutatorRank
/-!
# Dimension of the natural A8 central cover with a rank-two actor

The Sylow-central pair flip has displacement rank at least three on the
seven-dimensional augmentation core. An explicit three-dimensional coordinate
map witnesses this bound. Conjugacy preserves it. A quotient of this core
which still surjects onto the six-dimensional natural module therefore has
dimension six if that actor has displacement rank at most two.

Source: Aschbacher--Smith 13.5.23, printed p.925. This retains the whole
central cover and its literal projection; no splitting is assumed.
-/

@[expose] public noncomputable section
open Subgroup Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.CentralPair
namespace BinaryPermutation.EightCover
private def fullTest : (Fin 3 → ZMod 2) →ₗ[ZMod 2] Full (Fin 8) :=
  let p : Fin 3 → ((Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2) := fun j=>LinearMap.proj j
  LinearMap.pi (![p 0+p 1+p 2,0,p 0,0,p 1,0,p 2,0] :
    Fin 8 → ((Fin 3 → ZMod 2) →ₗ[ZMod 2] ZMod 2))
private def testMap : (Fin 3 → ZMod 2) →ₗ[ZMod 2] core (Fin 8) :=
  fullTest.codRestrict _ (by
    intro a
    rw [mem_core]
    change (∑j:Fin 8, ![a 0+a 1+a 2,0,a 0,0,a 1,0,a 2,0] j)=0
    simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,zero_add,add_zero]
    exact (show ∀x y z:ZMod 2,x+y+z+(x+(y+z))=0 from by decide) _ _ _)

theorem core_pairFlip_rank_ge_three : 3≤Module.finrank (ZMod 2)
    (LinearMap.range (alternatingCoreRepresentation (Fin 8) z-LinearMap.id)) := by
  let t:=(alternatingCoreRepresentation (Fin 8) z-LinearMap.id).comp testMap
  have ht : Function.Injective t := by
    intro a b hab
    have h0:=congrArg (fun v:core (Fin 8)=>v.val 2) hab
    have h1:=congrArg (fun v:core (Fin 8)=>v.val 4) hab
    have h2:=congrArg (fun v:core (Fin 8)=>v.val 6) hab
    change 0-a 0 = 0-b 0 at h0
    change 0-a 1 = 0-b 1 at h1
    change 0-a 2 = 0-b 2 at h2
    ext j
    fin_cases j
    · exact sub_right_injective h0
    · exact sub_right_injective h1
    · exact sub_right_injective h2
  have hle:=Submodule.finrank_mono (LinearMap.range_comp_le_range testMap
    (alternatingCoreRepresentation (Fin 8) z-LinearMap.id))
  have he:=t.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr ht] at he
  simp only [finrank_bot,add_zero] at he
  change Module.finrank (ZMod 2) t.range ≤ _ at hle
  rw [he] at hle
  simpa using hle

theorem core_pairFlip_conjugate_rank_ge_three (v:alternatingGroup (Fin 8))
    (hc:∃g:alternatingGroup (Fin 8), MulAut.conj g z=v) :
    3≤Module.finrank (ZMod 2)
      (LinearMap.range (alternatingCoreRepresentation (Fin 8) v-LinearMap.id)) := by
  obtain ⟨g,rfl⟩:=hc
  rw [←fixedCodim_zpowers_eq_displacement_rank]
  change 3≤fixedCodim (alternatingCoreRepresentation (Fin 8)) (zpowers (g*z*g⁻¹))
  rw [fixedCodim_zpowers_conj,fixedCodim_zpowers_eq_displacement_rank]
  exact core_pairFlip_rank_ge_three

variable {U:Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
theorem finrank_six_of_core_surjection
    (f:core (Fin 8)→ₗ[ZMod 2]U) (hf:Function.Surjective f)
    (p:U→ₗ[ZMod 2]natural (Fin 8)) (hp:Function.Surjective p)
    (v:alternatingGroup (Fin 8)) (hc:∃g:alternatingGroup (Fin 8),MulAut.conj g z=v)
    (a:U→ₗ[ZMod 2]U)
    (he:∀w,f (alternatingCoreRepresentation (Fin 8) v w)=a (f w))
    (hr:Module.finrank (ZMod 2) (LinearMap.range (a-LinearMap.id))≤2) :
    Module.finrank (ZMod 2) U=6 := by
  have hlo:=LinearMap.finrank_le_finrank_of_surjective hp
  have hhi:=LinearMap.finrank_le_finrank_of_surjective hf
  rw [finrank_natural_even (Fin 8) (by decide)] at hlo
  rw [finrank_core] at hhi
  norm_num only [Fintype.card_fin] at hlo hhi
  have hnot : Module.finrank (ZMod 2) U≠7 := by
    intro h7
    have hdim : Module.finrank (ZMod 2) (core (Fin 8))=Module.finrank (ZMod 2) U := by
      rw [finrank_core,h7]
      rfl
    have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf
    let E:=LinearEquiv.ofBijective f ⟨hi,hf⟩
    have hmap : (LinearMap.range (alternatingCoreRepresentation (Fin 8) v-LinearMap.id)).map
        E.toLinearMap ≤ LinearMap.range (a-LinearMap.id) := by
      rintro _ ⟨_,⟨w,rfl⟩,rfl⟩
      refine ⟨f w,?_⟩
      change a (f w)-f w=f (alternatingCoreRepresentation (Fin 8) v w-w)
      rw [map_sub,he]
    have hm:=Submodule.finrank_mono hmap
    rw [E.finrank_map_eq] at hm
    have h3:=core_pairFlip_conjugate_rank_ge_three v hc
    omega
  omega
end BinaryPermutation.EightCover
